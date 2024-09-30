use std::{fmt::Display, num::ParseIntError, str::FromStr, sync::LazyLock};

use fuzzy_matcher::clangd::fuzzy_match;
use memory::LoadOpcode;
use miette::SourceSpan;
use regex::Regex;
use strum::IntoEnumIterator;
use thiserror::Error;

use crate::{Machine, Outcome, Resource};

mod arithmetic;
mod memory;

const COMMENT_START: char = '#';

/// Trait for providing information about an operation
trait Info: Display {
    /// The opcodes these arguments support
    type Opcode;
    /// Decode the instruction into the output. The implementation is expected
    /// to return an error if an input **or** an output would cause issues (e.g.,
    /// misalignment or register out of bounds)
    fn decode(&self, opcode: Self::Opcode, machine: &Machine) -> Result<Vec<Outcome>, DecodeError>;
    /// The inputs to this. All memory inputs should use an address of 0
    fn inputs(&self) -> Vec<Location>;
    /// The outputs. All memory outputs should use an address of 0
    fn outputs(&self) -> Vec<Location>;
}

/// Memory Alignment. It is an error to read a value from an unaligned address
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum Alignment {
    /// Byte-aligned; any address is valid
    Byte,
    /// Half-word aligned; any even address is valid
    Half,
    /// Full-on word aligned; all addresses must be divisible by 4
    #[default]
    Word,
}

impl Alignment {
    /// The offset this alignment implies
    pub fn offset(self) -> usize {
        match self {
            Alignment::Byte => 1,
            Alignment::Half => 2,
            Alignment::Word => 4,
        }
    }
}

impl Display for Alignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Byte => "byte",
            Self::Half => "half",
            Self::Word => "word",
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Error)]
pub enum DecodeError {
    #[error("Register {0} does not exist")]
    InvalidRegister(Register),
    #[error("Address 0x{0:04x} is out of bounds for accessing a {1}")]
    AddressOutOfBounds(usize, Alignment),
    #[error("Address 0x{0:04x} is not aligned to the {1} boundary")]
    MisalignedAccess(usize, Alignment),
}

#[derive(Debug, Clone, Error, PartialEq, Eq, Hash)]
#[error("{source}")]
pub struct WithContext<S> {
    pub source: S,
    pub ctx: SourceSpan,
    pub help: Option<String>,
}

impl<S> WithContext<S> {
    pub fn span_context(&self, start: usize) -> SourceSpan {
        (self.ctx.offset() + start, self.ctx.len()).into()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Kind {
    Arithmetic,
    Multiplication,
    Load,
    Store,
    // Intercluster,
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Arithmetic => "Arithmetic",
            Self::Multiplication => "Multiplication",
            Self::Load => "Load",
            Self::Store => "Store",
            // Self::Intercluster => "Intercluster Communication",
        })
    }
}

impl From<Kind> for Resource {
    fn from(value: Kind) -> Self {
        match value {
            Kind::Arithmetic /*| Kind::Intercluster */ => Self::Alu,
            Kind::Load => Self::Load,
            Kind::Store => Self::Store,
            Kind::Multiplication => Self::Mul,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operand {
    Register(Register),
    Immediate(u32),
}

impl Operand {
    pub fn resolve(self, machine: &Machine) -> Result<u32, DecodeError> {
        match self {
            Self::Register(r) => machine.get_reg(r),
            Self::Immediate(i) => Ok(i),
        }
    }
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Register(r) => f.write_fmt(format_args!("{r}")),
            Self::Immediate(i) => f.write_fmt(format_args!("0x{i:x}")),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("{0}")]
pub struct OperandParseError(RegisterParseError, #[source] ParseIntError);

impl FromStr for Operand {
    type Err = OperandParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let reg_res = s.parse::<Register>();
        let int_res = parse_num(s);
        match (reg_res, int_res) {
            (Err(r), Err(i)) => Err(OperandParseError(r.source, i)),
            (Ok(r), _) => Ok(Operand::Register(r)),
            (_, Ok(i)) => Ok(Operand::Immediate(i)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RegisterType {
    General,
    Branch,
    Link,
}

impl FromStr for RegisterType {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "r" => Ok(Self::General),
            "b" => Ok(Self::Branch),
            "l" => Ok(Self::Link),
            _ => Err(()),
        }
    }
}

impl Display for RegisterType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::General => "r",
            Self::Branch => "b",
            Self::Link => "l",
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Register {
    pub(crate) num: usize,
    pub(crate) class: RegisterType,
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { num, class: bank } = self;
        f.write_fmt(format_args!("${bank}0.{num}"))
    }
}

#[derive(Debug, Clone, Copy, Error, PartialEq, Eq, Hash)]
pub enum RegisterParseError {
    #[error("Expected `{expected}`{got}")]
    UnexpectedChar {
        expected: char,
        got: UnexpectedValue,
    },
    #[error("Invalid register class: Must be one of `r`, `b`, or `l`")]
    Class,
    #[error("Invalid cluster")]
    Cluster,
    #[error("Invalid register number")]
    Number,
}

impl FromStr for Register {
    type Err = WithContext<RegisterParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Better be a $
        if !s.starts_with('$') {
            return Err(WithContext {
                source: RegisterParseError::UnexpectedChar {
                    got: UnexpectedValue(s.chars().next()),
                    expected: '$',
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        let s = &s[1..];
        idx += 1;
        // Chomp the register type
        let Some(Ok(bank)) = s.chars().next().map(|c| c.to_string().parse()) else {
            return Err(WithContext {
                source: RegisterParseError::Class,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let s = &s[1..];
        idx += 1;
        if !s.starts_with('0') {
            return Err(WithContext {
                source: RegisterParseError::Cluster,
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        let s = &s[1..];
        idx += 1;
        if !s.starts_with('.') {
            return Err(WithContext {
                source: RegisterParseError::UnexpectedChar {
                    got: UnexpectedValue(s.chars().next()),
                    expected: '.',
                },
                help: None,
                ctx: (idx, 0).into(),
            });
        }
        let s = &s[1..];
        idx += 1;
        let s = trim_start(s, &mut idx).trim();
        let Ok(num) = s.parse() else {
            return Err(WithContext {
                source: RegisterParseError::Number,
                ctx: (idx, s.len()).into(),
                help: None,
            });
        };
        Ok(Self { num, class: bank })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Location {
    Register(Register),
    Memory(usize, Alignment),
}

impl Location {
    pub const fn sanitize(self) -> Self {
        match self {
            Self::Register(r) => Self::Register(r),
            Self::Memory(_, _) => Self::Memory(0, Alignment::Word),
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Memory(m, _) => f.write_fmt(format_args!("MEM[0x{m:04x}]")),
            Self::Register(r) => f.write_fmt(format_args!("{r}")),
        }
    }
}

pub fn parse_num(num: &str) -> Result<u32, ParseIntError> {
    let num = num.trim();
    if num.starts_with("0x") {
        u32::from_str_radix(num.trim_start_matches("0x"), 16)
    } else {
        num.parse()
    }
}

fn remove_comment(s: &str) -> &str {
    // Remove comment
    s.find(COMMENT_START).map_or(s, |com| &s[..com])
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Action {
    BasicArithmetic(arithmetic::BasicOpcode, arithmetic::BasicArgs),
    CarryArithmetic(arithmetic::CarryOpcode, arithmetic::CarryArgs),
    Sub(arithmetic::SubArgs),
    Load(memory::LoadOpcode, memory::LoadArgs),
    Store(memory::StoreOpcode, memory::StoreArgs),
    Extend(arithmetic::ExtendOpcode, arithmetic::ExtendArgs),
}

/// Trim the start, and update the idx to point at the new start
fn trim_start<'a>(s: &'a str, idx: &mut usize) -> &'a str {
    let prev_len = s.len();
    let s = s.trim_start();
    *idx += prev_len - s.len();
    s
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnexpectedValue(Option<char>);

impl Display for UnexpectedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(c) = self.0 {
            f.write_fmt(format_args!(", but got `{c}` instead"))
        } else {
            f.write_fmt(format_args!(", but hit end of input instead"))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ParseError {
    #[error("Expected a cluster, but could not find one")]
    NoCluster,
    #[error("Expected an opcode, but none was found")]
    NoOpcode,
    #[error("Unrecognized opcode `{0}`")]
    UnknownOpcode(String),
    #[error("Expected a register, but none was found")]
    NoRegister,
    #[error("Failed to parse register: {0}")]
    BadRegister(RegisterParseError),
    #[error("Wrong register type: Wanted {wanted}, but got {got} instead")]
    WrongRegisterType {
        wanted: RegisterType,
        got: RegisterType,
    },
    #[error("Expected an offset, but none was found")]
    NoOffset,
    #[error("Failed to parse offset: {0}")]
    BadOffset(ParseIntError),
    #[error("Expected a value, but got none")]
    NoValue,
    #[error("Failed to parse operand `{0}`")]
    BadOperand(String, #[source] OperandParseError),
    #[error("Expected end of input or comment, but got `{0}`")]
    ExpectedEnd(String),
    #[error("Wanted {wanted}, but got {got} instead")]
    UnexpectedCharacter { wanted: char, got: UnexpectedValue },
}

impl ParseError {
    pub const fn element(&self) -> &'static str {
        match self {
            Self::NoCluster => "cluster",
            Self::NoOpcode | Self::UnknownOpcode(_) => "opcode",
            Self::NoRegister
            | Self::BadRegister(_)
            | Self::WrongRegisterType { got: _, wanted: _ } => "register",
            Self::NoOffset | Self::BadOffset(_) => "offset",
            Self::NoValue | Self::BadOperand(_, _) => "value",
            Self::ExpectedEnd(_) | Self::UnexpectedCharacter { wanted: _, got: _ } => "problem",
        }
    }
}

impl From<RegisterParseError> for ParseError {
    fn from(value: RegisterParseError) -> Self {
        Self::BadRegister(value)
    }
}

impl FromStr for Action {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = remove_comment(s);
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        static OPCODE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"\w+").unwrap());

        let Some(cap) = OPCODE.captures(s).and_then(|c| c.get(0)) else {
            return Err(WithContext {
                source: ParseError::NoOpcode,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let opcode = cap.as_str();
        let rest = &s[cap.len()..];
        let err = move |p: WithContext<_>| {
            let span = p.span_context(idx + cap.len());
            WithContext {
                source: p.source,
                ctx: span,
                help: None,
            }
        };
        if let Ok(ar_opcode) = opcode.parse::<arithmetic::BasicOpcode>() {
            Ok(Self::BasicArithmetic(ar_opcode, rest.parse().map_err(err)?))
        } else if let Ok(cg_opcode) = opcode.parse::<arithmetic::CarryOpcode>() {
            Ok(Self::CarryArithmetic(cg_opcode, rest.parse().map_err(err)?))
        } else if let Ok(ld_opcode) = opcode.parse::<memory::LoadOpcode>() {
            Ok(Self::Load(ld_opcode, rest.parse().map_err(err)?))
        } else if let Ok(st_opcode) = opcode.parse::<memory::StoreOpcode>() {
            Ok(Self::Store(st_opcode, rest.parse().map_err(err)?))
        } else if let Ok(ex_opcode) = opcode.parse::<arithmetic::ExtendOpcode>() {
            Ok(Self::Extend(ex_opcode, rest.parse().map_err(err)?))
        } else if opcode == "sub" {
            Ok(Self::Sub(rest.parse().map_err(err)?))
        } else {
            // No matched op code
            let help = arithmetic::BasicOpcode::iter()
                .map(arithmetic::BasicOpcode::code)
                .chain(memory::LoadOpcode::iter().map(LoadOpcode::code))
                .filter_map(|op| fuzzy_match(opcode, op).map(|s| (op, s)))
                .max_by_key(|&(_, s)| s)
                .map(|(op, _)| format!("Perhaps you meant {op} instead?"));

            Err(WithContext {
                source: ParseError::UnknownOpcode(cap.as_str().to_owned()),
                ctx: (idx, cap.len()).into(),
                help,
            })
        }
    }
}

impl Action {
    pub fn inputs(&self) -> Vec<Location> {
        match self {
            Self::BasicArithmetic(_, args) => args.inputs(),
            Self::Sub(args) => args.inputs(),
            Self::CarryArithmetic(_, args) => args.inputs(),
            Self::Extend(_, args) => args.inputs(),
            Self::Load(_, load) => load.inputs(),
            Self::Store(_, store) => store.inputs(),
        }
    }
    pub fn outputs(&self) -> Vec<Location> {
        match self {
            Self::BasicArithmetic(_, args) => args.outputs(),
            Self::Sub(args) => args.outputs(),
            Self::Extend(_, args) => args.outputs(),
            Self::CarryArithmetic(_, args) => args.outputs(),
            Self::Load(_, load) => load.outputs(),
            Self::Store(_, store) => store.outputs(),
        }
    }
    pub fn decode(&self, machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        match self {
            Self::BasicArithmetic(op, args) => args.decode(*op, machine),
            Self::Sub(args) => args.decode((), machine),
            Self::Extend(op, args) => args.decode(*op, machine),
            Self::CarryArithmetic(op, args) => args.decode(*op, machine),
            Self::Load(op, args) => args.decode(*op, machine),
            Self::Store(op, args) => args.decode(*op, machine),
        }
    }
    pub const fn code(&self) -> &'static str {
        match self {
            Self::BasicArithmetic(op, _) => op.code(),
            Self::Sub(_) => "sub",
            Self::Extend(op, _) => op.code(),
            Self::CarryArithmetic(op, _) => op.code(),
            Self::Load(op, _) => op.code(),
            Self::Store(op, _) => op.code(),
        }
    }
    pub const fn kind(&self) -> Kind {
        match self {
            Self::BasicArithmetic(op, _) => op.kind(),
            Self::CarryArithmetic(op, _) => op.kind(),
            Self::Sub(_)|Self::Extend(_, _) => Kind::Arithmetic,
            Self::Load(_, _) => Kind::Load,
            Self::Store(_, _) => Kind::Store,
        }
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BasicArithmetic(op, args) => f.write_fmt(format_args!("{op} {args}")),
            Self::CarryArithmetic(op, args) => f.write_fmt(format_args!("{op} {args}")),
            Self::Sub(args) => f.write_fmt(format_args!("sub {args}")),
            Self::Extend(op, args) => f.write_fmt(format_args!("{op} {args}")),
            Self::Load(op, args) => f.write_fmt(format_args!("{op} {args}")),
            Self::Store(op, args) => f.write_fmt(format_args!("{op} {args}")),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Operation {
    pub ctx: Option<(usize, SourceSpan)>,
    pub cluster: usize,
    pub action: Action,
}

impl Operation {
    pub fn summary(&self) -> String {
        let out = format!("{} instruction", self.action.code());
        if let Some((line, _)) = self.ctx {
            out + &format!(" on line {line}")
        } else {
            out
        }
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            cluster,
            action: op,
            ..
        } = self;
        f.write_fmt(format_args!("c{cluster} {op}"))
    }
}

impl FromStr for Operation {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        static CLUSTER: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"\d+").unwrap());
        // Chomp whitespace
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Should start with c
        if !s.starts_with('c') {
            return Err(WithContext {
                source: ParseError::UnexpectedCharacter {
                    wanted: 'c',
                    got: UnexpectedValue(s.chars().next()),
                },
                ctx: (idx, 0).into(),
                help: Some(String::from("Clusters must begin with the letter `c`")),
            });
        }
        let s = &s[1..];
        idx += 1;
        // First thing better be cluster
        let Some(c) = CLUSTER.captures(s).and_then(|s| s.get(0)) else {
            // Couldn't find the cluster
            return Err(WithContext {
                source: ParseError::NoCluster,
                ctx: (idx, 0).into(),
                help: Some(String::from("All instructions must have a cluster")),
            });
        };
        let cluster = c.as_str().parse().map_err(|_e| WithContext {
            source: ParseError::NoOffset,
            ctx: (idx, c.len()).into(),
            help: None,
        })?;
        idx += c.len();
        let op = s[c.end()..].parse().map_err(|e: WithContext<_>| {
            let span = e.span_context(idx);
            WithContext { ctx: span, ..e }
        })?;
        Ok(Self {
            cluster,
            action: op,
            ctx: None,
        })
    }
}

impl Operation {
    pub const fn with_context(self, ctx: (usize, SourceSpan)) -> Self {
        Self {
            ctx: Some(ctx),
            ..self
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct Instruction(pub Vec<Operation>);

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in &self.0 {
            f.write_fmt(format_args!("{i}\n"))?;
        }
        f.write_str(";;")
    }
}

#[cfg(test)]
mod test {
    use std::{
        fmt::{Debug, Display},
        str::FromStr,
    };

    use crate::operation::Alignment;

    use super::{
        arithmetic::{BasicArgs, BasicOpcode, CarryArgs, CarryOpcode, SubArgs},
        memory::{LoadArgs, LoadOpcode, StoreArgs, StoreOpcode},
        Action, Location, Operand, Operation, Register, RegisterType,
    };
    pub fn positive<T, E>(tests: &[(&'static str, T)])
    where
        T: Eq + FromStr<Err = E> + Debug,
        E: Debug,
    {
        for (i, exp) in tests {
            dbg!(i);
            let res = i.parse::<T>();
            if let Err(ref e) = res {
                dbg!(e);
            }
            assert_eq!(&res.unwrap(), exp);
        }
    }

    pub fn negative<T, E>(tests: &[&'static str])
    where
        T: FromStr<Err = E> + Debug,
        E: Debug,
    {
        for i in tests {
            dbg!(i);
            let res = i.parse::<T>();
            assert!(res.is_err());
        }
    }

    pub fn display<T>(tests: &[(&'static str, T)])
    where
        T: Display + Debug,
    {
        for (exp, i) in tests {
            dbg!(i);
            assert_eq!(&format!("{i}"), exp);
        }
    }
    #[test]
    fn reg_parser() {
        positive(&[
            (
                "$r0.1",
                Register {
                    num: 1,
                    class: RegisterType::General,
                },
            ),
            (
                "$r0.56",
                Register {
                    num: 56,
                    class: RegisterType::General,
                },
            ),
            (
                "$b0.1",
                Register {
                    num: 1,
                    class: RegisterType::Branch,
                },
            ),
        ]);

        negative::<Register, _>(&[
            "r0.1", "$r1.1", "$d0.1", "b", "$0.1", "$.1", "$", "0", "$r0",
        ]);
    }

    #[test]
    fn reg_display() {
        display(&[
            (
                "$r0.1",
                Register {
                    class: RegisterType::General,
                    num: 1,
                },
            ),
            (
                "$b0.8",
                Register {
                    class: RegisterType::Branch,
                    num: 8,
                },
            ),
            (
                "$l0.0",
                Register {
                    class: RegisterType::Link,
                    num: 0,
                },
            ),
        ]);
    }

    #[test]
    fn loc_display() {
        display(&[
            (
                "$r0.1",
                Location::Register(Register {
                    class: RegisterType::General,
                    num: 1,
                }),
            ),
            ("MEM[0x0020]", Location::Memory(0x20, Alignment::Word)),
        ]);
    }
    #[test]
    fn operand_display() {
        display(&[
            (
                "$r0.1",
                Operand::Register(Register {
                    class: RegisterType::General,
                    num: 1,
                }),
            ),
            ("0x20", Operand::Immediate(0x20)),
        ]);
    }

    #[test]
    fn operation_parser() {
        positive(&[
            (
                "c0 maxu $r0.3 = $r0.1, $r0.2",
                Operation {
                    action: Action::BasicArithmetic(
                        BasicOpcode::MaxUnsigned,
                        BasicArgs {
                            src1: Register {
                                num: 1,
                                class: RegisterType::General,
                            },
                            src2: Operand::Register(Register {
                                num: 2,
                                class: RegisterType::General,
                            }),
                            dst: Register {
                                num: 3,
                                class: RegisterType::General,
                            },
                        },
                    ),
                    cluster: 0,
                    ctx: None,
                },
            ),
            (
                "c0 ldw $r0.3=0x20[$r0.1]",
                Operation {
                    action: Action::Load(
                        LoadOpcode::Word,
                        LoadArgs {
                            base: Register {
                                num: 1,
                                class: RegisterType::General,
                            },
                            offset: 0x20,
                            dst: Register {
                                num: 3,
                                class: RegisterType::General,
                            },
                        },
                    ),
                    cluster: 0,
                    ctx: None,
                },
            ),
            (
                "c0 stw       5    [$r0.1] = $r0.3",
                Operation {
                    action: Action::Store(
                        StoreOpcode::Word,
                        StoreArgs {
                            base: Register {
                                num: 1,
                                class: RegisterType::General,
                            },
                            offset: 5,
                            src: Register {
                                num: 3,
                                class: RegisterType::General,
                            },
                        },
                    ),
                    cluster: 0,
                    ctx: None,
                },
            ),
            (
                "c0 sub $r0.1 = 5, $r0.3",
                Operation {
                    action: Action::Sub(SubArgs {
                        dst: Register {
                            num: 1,
                            class: RegisterType::General,
                        },
                        src1: Operand::Immediate(5),
                        src2: Register {
                            num: 3,
                            class: RegisterType::General,
                        },
                    }),
                    cluster: 0,
                    ctx: None,
                },
            ),
            (
                "c0 addcg $r0.1, $b0.1 = $b0.2, $r0.2, $r0.3",
                Operation {
                    action: Action::CarryArithmetic(
                        CarryOpcode::AddCarry,
                        CarryArgs {
                            cout: Register {
                                num: 1,
                                class: RegisterType::Branch,
                            },
                            dst: Register {
                                num: 1,
                                class: RegisterType::General,
                            },
                            cin: Register {
                                num: 2,
                                class: RegisterType::Branch,
                            },
                            src1: Register {
                                num: 2,
                                class: RegisterType::General,
                            },
                            src2: Register {
                                num: 3,
                                class: RegisterType::General,
                            },
                        },
                    ),
                    cluster: 0,
                    ctx: None,
                },
            ),
        ]);
    }

    #[test]
    fn operation_display() {
        display(&[
            (
                "c0 maxu $r0.3 = $r0.1, $r0.2",
                Operation {
                    action: Action::BasicArithmetic(
                        BasicOpcode::MaxUnsigned,
                        BasicArgs {
                            src1: Register {
                                num: 1,
                                class: RegisterType::General,
                            },
                            src2: Operand::Register(Register {
                                num: 2,
                                class: RegisterType::General,
                            }),
                            dst: Register {
                                num: 3,
                                class: RegisterType::General,
                            },
                        },
                    ),
                    cluster: 0,
                    ctx: None,
                },
            ),
            (
                "c0 addcg $r0.1, $b0.1 = $b0.2, $r0.2, $r0.3",
                Operation {
                    action: Action::CarryArithmetic(
                        CarryOpcode::AddCarry,
                        CarryArgs {
                            cout: Register {
                                num: 1,
                                class: RegisterType::Branch,
                            },
                            dst: Register {
                                num: 1,
                                class: RegisterType::General,
                            },
                            cin: Register {
                                num: 2,
                                class: RegisterType::Branch,
                            },
                            src1: Register {
                                num: 2,
                                class: RegisterType::General,
                            },
                            src2: Register {
                                num: 3,
                                class: RegisterType::General,
                            },
                        },
                    ),
                    cluster: 0,
                    ctx: None,
                },
            ),
        ]);
    }
}
