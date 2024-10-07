use std::{borrow::Cow, fmt::Display, num::ParseIntError, str::FromStr, sync::LazyLock};

use fuzzy_matcher::clangd::fuzzy_match;
use memory::LoadOpcode;
use miette::SourceSpan;
use regex::Regex;
use strum::IntoEnumIterator;
use thiserror::Error;

use crate::{Machine, Outcome, Resource};

mod arithmetic;
mod help;
mod intercluster;
mod logical;
mod memory;

const COMMENT_START: char = '#';

/// Trait for providing information about an operation
trait Info: Display {
    /// The opcodes these arguments support
    type Opcode: Copy;
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
    pub help: Option<Cow<'static, str>>,
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
pub enum RegisterClass {
    General,
    Branch,
    Link,
}

impl FromStr for RegisterClass {
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

impl Display for RegisterClass {
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
    pub(crate) cluster: usize,
    pub(crate) num: usize,
    pub(crate) class: RegisterClass,
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            cluster,
            num,
            class,
        } = self;
        f.write_fmt(format_args!("${class}{cluster}.{num}"))
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
        let Some(Ok(class)) = s.chars().next().map(|c| c.to_string().parse()) else {
            return Err(WithContext {
                source: RegisterParseError::Class,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let s = &s[1..];
        idx += 1;
        // Chomp the cluster
        let Some((cluster, s)) = s.split_once('.') else {
            return Err(WithContext {
                source: RegisterParseError::Cluster,
                ctx: (idx, 0).into(),
                help: Some("All registers must have a cluster".into()),
            });
        };
        let val_len = cluster.len();
        idx += val_len + 1;
        let Ok(cluster) = cluster.parse() else {
            return Err(WithContext {
                source: RegisterParseError::Cluster,
                ctx: (idx, val_len).into(),
                help: None,
            });
        };
        let s = trim_start(s, &mut idx).trim();
        let Ok(num) = s.parse() else {
            return Err(WithContext {
                source: RegisterParseError::Number,
                ctx: (idx, s.len()).into(),
                help: None,
            });
        };
        Ok(Self {
            cluster,
            num,
            class,
        })
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Action {
    BasicArithmetic(arithmetic::BasicOpcode, arithmetic::BasicArgs),
    CarryArithmetic(arithmetic::CarryOpcode, arithmetic::CarryArgs),
    Sub(arithmetic::SubArgs),
    Load(memory::LoadOpcode, memory::LoadArgs),
    Store(memory::StoreOpcode, memory::StoreArgs),
    Extend(arithmetic::ExtendOpcode, arithmetic::ExtendArgs),
    Move(intercluster::MoveArgs),
    Send(intercluster::SendArgs),
    Recv(intercluster::RecvArgs),
    Compare(logical::CompareOpcode, logical::CompareArgs),
    Logical(logical::LogicalOpcode, logical::LogicalArgs),
    Select(logical::SelectOpcode, logical::SelectArgs),
}

/// Trim the start, and update the idx to point at the new start
fn trim_start<'a>(s: &'a str, idx: &mut usize) -> &'a str {
    let prev_len = s.len();
    let s = s.trim_start();
    *idx += prev_len - s.len();
    s
}

/// Map a register error with context
fn reg_err(r: WithContext<RegisterParseError>, idx: usize) -> WithContext<ParseError> {
    WithContext {
        source: r.source.into(),
        ctx: r.span_context(idx),
        help: None,
    }
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
    WrongRegisterClass {
        wanted: RegisterClass,
        got: RegisterClass,
    },
    #[error(
        "Cluster {0} found, but so was cluster {1}. This instruction only supports one cluster"
    )]
    RegisterClusterMismatch(usize, usize),
    #[error("Expected an offset, but none was found")]
    NoOffset,
    #[error("Failed to parse offset: {0}")]
    BadOffset(ParseIntError),
    #[error("Failed to parse immediate: {0}")]
    BadImmediate(ParseIntError),
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
    pub fn element(&self) -> Cow<'static, str> {
        match self {
            Self::NoCluster | Self::RegisterClusterMismatch(_, _) => Cow::Borrowed("cluster"),
            Self::NoOpcode | Self::UnknownOpcode(_) => Cow::Borrowed("opcode"),
            Self::NoRegister
            | Self::BadRegister(_)
            | Self::WrongRegisterClass { got: _, wanted: _ } => Cow::Borrowed("register"),
            Self::NoOffset | Self::BadOffset(_) => Cow::Borrowed("offset"),
            Self::NoValue | Self::BadOperand(_, _) | Self::BadImmediate(_) => {
                Cow::Borrowed("value")
            }
            Self::ExpectedEnd(_) => Cow::Borrowed("problem"),
            Self::UnexpectedCharacter { wanted, got: _ } => {
                Cow::Owned(format!("Expected '{wanted}'"))
            }
        }
    }
}

impl From<RegisterParseError> for ParseError {
    fn from(value: RegisterParseError) -> Self {
        Self::BadRegister(value)
    }
}

fn check_cluster(
    r1: Register,
    r2: Register,
    idx: usize,
    len: usize,
) -> Result<(), WithContext<ParseError>> {
    if r1.cluster != r2.cluster {
        Err(WithContext {
            ctx: (idx, len).into(),
            help: Some(help::CLUSTER_MISMATCH.into()),
            source: ParseError::RegisterClusterMismatch(r1.cluster, r2.cluster),
        })
    } else {
        Ok(())
    }
}

impl FromStr for Action {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.find(COMMENT_START).map_or(s, |com| &s[..com]);
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        static OPCODE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"\w+").unwrap());

        let Some(cap) = OPCODE.captures(s).and_then(|c| c.get(0)) else {
            return Err(WithContext {
                source: ParseError::NoOpcode,
                ctx: (idx, 0).into(),
                help: Some(help::NO_OPCODE.into()),
            });
        };
        let opcode = cap.as_str();
        let rest = &s[cap.len()..];
        let err = move |p: WithContext<_>| {
            let span = p.span_context(idx + cap.len());
            WithContext {
                source: p.source,
                ctx: span,
                help: p.help,
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
        } else if let Ok(cmp_opcode) = opcode.parse::<logical::CompareOpcode>() {
            Ok(Self::Compare(cmp_opcode, rest.parse().map_err(err)?))
        } else if let Ok(lg_opcode) = opcode.parse::<logical::LogicalOpcode>() {
            Ok(Self::Logical(lg_opcode, rest.parse().map_err(err)?))
        } else if let Ok(slct_opcode) = opcode.parse::<logical::SelectOpcode>() {
            Ok(Self::Select(slct_opcode, rest.parse().map_err(err)?))
        } else if opcode == "sub" {
            Ok(Self::Sub(rest.parse().map_err(err)?))
        } else if opcode == "mov" {
            Ok(Self::Move(rest.parse().map_err(err)?))
        } else if opcode == "send" {
            Ok(Self::Send(rest.parse().map_err(err)?))
        } else if opcode == "recv" {
            Ok(Self::Recv(rest.parse().map_err(err)?))
        } else {
            // No matched op code
            let help = arithmetic::BasicOpcode::iter()
                .map(arithmetic::BasicOpcode::code)
                .chain(memory::LoadOpcode::iter().map(LoadOpcode::code))
                .filter_map(|op| fuzzy_match(opcode, op).map(|s| (op, s)))
                .max_by_key(|&(_, s)| s)
                .map(|(op, _)| format!("Perhaps you meant {op} instead?").into());

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
            Self::Move(args) => args.inputs(),
            Self::Send(args) => args.inputs(),
            Self::Recv(args) => args.inputs(),
            Self::Compare(_, args) => args.inputs(),
            Self::Logical(_, args) => args.inputs(),
            Self::Select(_, args) => args.inputs(),
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
            Self::Move(args) => args.outputs(),
            Self::Send(args) => args.outputs(),
            Self::Recv(args) => args.outputs(),
            Self::Compare(_, args) => args.outputs(),
            Self::Logical(_, args) => args.outputs(),
            Self::Select(_, args) => args.outputs(),
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
            Self::Move(args) => args.decode((), machine),
            Self::Send(args) => args.decode((), machine),
            Self::Recv(args) => args.decode((), machine),
            Self::Compare(op, args) => args.decode(*op, machine),
            Self::Logical(op, args) => args.decode(*op, machine),
            Self::Select(op, args) => args.decode(*op, machine),
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
            Self::Compare(op, _) => op.code(),
            Self::Logical(op, _) => op.code(),
            Self::Select(op, _) => op.code(),
            Self::Move(_) => "mov",
            Self::Send(_) => "send",
            Self::Recv(_) => "recv",
        }
    }
    pub const fn kind(&self) -> Kind {
        match self {
            Self::BasicArithmetic(op, _) => op.kind(),
            Self::CarryArithmetic(op, _) => op.kind(),
            Self::Sub(_) | Self::Extend(_, _) => Kind::Arithmetic,
            Self::Move(_) | Self::Send(_) | Self::Recv(_) => Kind::Arithmetic,
            Self::Compare(_, _) | Self::Logical(_, _) | Self::Select(_, _) => Kind::Arithmetic,
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
            Self::Move(args) => f.write_fmt(format_args!("mov {args}")),
            Self::Send(args) => f.write_fmt(format_args!("send {args}")),
            Self::Recv(args) => f.write_fmt(format_args!("recv {args}")),
            Self::Compare(op, args) => f.write_fmt(format_args!("{op} {args}")),
            Self::Logical(op, args) => f.write_fmt(format_args!("{op} {args}")),
            Self::Select(op, args) => f.write_fmt(format_args!("{op} {args}")),
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
                help: Some(help::BAD_CLUSTER.into()),
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
                help: Some(help::NO_CLUSTER.into()),
            });
        };
        let cluster = c.as_str().parse().map_err(|_e| WithContext {
            source: ParseError::NoOffset,
            ctx: (idx, c.len() - 1).into(),
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
    pub fn with_context(self, ctx: (usize, SourceSpan)) -> Self {
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
        Action, Location, Operand, Operation, Register, RegisterClass,
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
                    cluster: 0,
                    num: 1,
                    class: RegisterClass::General,
                },
            ),
            (
                "$r0.56",
                Register {
                    cluster: 0,
                    num: 56,
                    class: RegisterClass::General,
                },
            ),
            (
                "$b1.1",
                Register {
                    cluster: 1,
                    num: 1,
                    class: RegisterClass::Branch,
                },
            ),
        ]);

        negative::<Register, _>(&[
            "r0.1", "$d0.1", "b", "$0.1", "$.1", "$", "0", "$r0", "",
        ]);
    }

    #[test]
    fn reg_display() {
        display(&[
            (
                "$r0.1",
                Register {
                    cluster: 0,
                    class: RegisterClass::General,
                    num: 1,
                },
            ),
            (
                "$b0.8",
                Register {
                    cluster: 0,
                    class: RegisterClass::Branch,
                    num: 8,
                },
            ),
            (
                "$l0.0",
                Register {
                    cluster: 0,
                    class: RegisterClass::Link,
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
                    cluster: 0,
                    class: RegisterClass::General,
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
                    cluster: 0,
                    class: RegisterClass::General,
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
                                cluster: 0,
                                num: 1,
                                class: RegisterClass::General,
                            },
                            src2: Operand::Register(Register {
                                cluster: 0,
                                num: 2,
                                class: RegisterClass::General,
                            }),
                            dst: Register {
                                cluster: 0,
                                num: 3,
                                class: RegisterClass::General,
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
                                cluster: 0,
                                num: 1,
                                class: RegisterClass::General,
                            },
                            offset: 0x20,
                            dst: Register {
                                cluster: 0,
                                num: 3,
                                class: RegisterClass::General,
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
                                cluster: 0,
                                num: 1,
                                class: RegisterClass::General,
                            },
                            offset: 5,
                            src: Register {
                                cluster: 0,
                                num: 3,
                                class: RegisterClass::General,
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
                            cluster: 0,
                            num: 1,
                            class: RegisterClass::General,
                        },
                        src1: Operand::Immediate(5),
                        src2: Register {
                            cluster: 0,
                            num: 3,
                            class: RegisterClass::General,
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
                                cluster: 0,
                                num: 1,
                                class: RegisterClass::Branch,
                            },
                            dst: Register {
                                cluster: 0,
                                num: 1,
                                class: RegisterClass::General,
                            },
                            cin: Register {
                                cluster: 0,
                                num: 2,
                                class: RegisterClass::Branch,
                            },
                            src1: Register {
                                cluster: 0,
                                num: 2,
                                class: RegisterClass::General,
                            },
                            src2: Register {
                                cluster: 0,
                                num: 3,
                                class: RegisterClass::General,
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
                                cluster: 0,
                                num: 1,
                                class: RegisterClass::General,
                            },
                            src2: Operand::Register(Register {
                                cluster: 0,
                                num: 2,
                                class: RegisterClass::General,
                            }),
                            dst: Register {
                                cluster: 0,
                                num: 3,
                                class: RegisterClass::General,
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
                                cluster: 0,
                                num: 1,
                                class: RegisterClass::Branch,
                            },
                            dst: Register {
                                cluster: 0,
                                num: 1,
                                class: RegisterClass::General,
                            },
                            cin: Register {
                                cluster: 0,
                                num: 2,
                                class: RegisterClass::Branch,
                            },
                            src1: Register {
                                cluster: 0,
                                num: 2,
                                class: RegisterClass::General,
                            },
                            src2: Register {
                                cluster: 0,
                                num: 3,
                                class: RegisterClass::General,
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
