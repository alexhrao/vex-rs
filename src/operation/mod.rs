use std::{borrow::Cow, fmt::Display, num::ParseIntError, str::FromStr, sync::LazyLock};

use fuzzy_matcher::clangd::fuzzy_match;
use memory::LoadOpcode;
use miette::{Diagnostic, NamedSource, SourceSpan};
use regex::Regex;
use strum::IntoEnumIterator;
use thiserror::Error;

use crate::machine::{Machine, MemoryValue};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
pub enum Resource {
    Arithmetic,
    Multiplication,
    Load,
    Store,
    Copy,
}

impl Display for Resource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Arithmetic => "Arithmetic & Logic",
            Self::Load => "Memory Load",
            Self::Store => "Memory Store",
            Self::Multiplication => "Multiplier",
            Self::Copy => "Intercluster",
        })
    }
}

/// Describes how a result should be committed
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Outcome {
    /// The value to be committed
    pub(crate) value: u32,
    /// The location to store
    pub(crate) dst: Location,
}

impl Outcome {
    /// Commit this outcome to memory or the register bank
    pub fn commit(&self, machine: &mut Machine) {
        match self.dst {
            // Alignment has already been checked
            Location::Memory(m, a) => {
                machine
                    .write_memory(m, MemoryValue::new(self.value, a))
                    .unwrap();
            }
            Location::Register(r) => {
                machine[r] = self.value;
            }
        }
    }
}

impl Display for Outcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{} = {}", self.dst, self.value))
    }
}

/// Memory Alignment
///
/// It is an error to read memory from an unaligned address. This represents
/// the expected alignment an address must respect.
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
    pub const fn offset(self) -> usize {
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

/// An error that occurred during the decoding of an instruction
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Error)]
pub enum DecodeError {
    /// An invalid (non-existent) register was referenced, or is not
    /// writeable
    #[error("Register {0} either does not exist, or is not writeable")]
    InvalidRegister(Register),
    /// The address did not respect the necessary alignment
    #[error("Address 0x{0:04x} is not aligned to the {1} boundary")]
    MisalignedAccess(usize, Alignment),
    #[error("Adderss 0x{0:04x} was read without ever being initialized")]
    UninitializedRead(usize, Alignment),
}

/// An error with source context
#[derive(Debug, Clone, Error, PartialEq, Eq, Hash)]
#[error("{source}")]
pub struct WithContext<S> {
    /// The error that occurred
    pub source: S,
    /// The context (e.g., where in the source code)
    pub ctx: SourceSpan,
    /// Helpful information for the end-user, if any
    pub help: Option<Cow<'static, str>>,
}

impl<S> WithContext<S> {
    pub fn span_context(&self, start: usize) -> SourceSpan {
        (self.ctx.offset() + start, self.ctx.len()).into()
    }
}

/// An argument that is either a register or an immediate
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operand {
    /// A named register
    Register(Register),
    /// A literal 32-bit unsigned value
    Immediate(u32),
}

impl Operand {
    /// Resolve this to a value
    ///
    /// This will attempt to resolve the operand to a 32-bit unsigned
    /// value. If it is an immediate, this is guaranteed to succeed.
    /// However, if it is a register that does not exist, then this
    /// will fail with a [`DecodeError::InvalidRegister`] error.
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

/// An error that occurred when parsing an operand
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

/// Class of a register
///
/// While all registers are 32-bit containers, the class
/// of a register determines what kinds of values it is
/// allowed to use, and perhaps more importantly, what
/// contexts the register is allowed to appear in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RegisterClass {
    /// A general-purpose register. This is the most widespread
    /// register class
    General,
    /// A single-bit register. This is typically used for comparison
    /// and branching instructions
    Branch,
    /// The link register. This is used for navigating around code at
    /// runtime
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

/// A single register
///
/// A register is a 32-bit container that, depending on
/// its class, can hold different values and be used
/// in different contexts.
///
/// A register lives inside a cluster. Typically, an operation will
/// require that all referenced registers reside in the same cluster.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Register {
    /// The cluster that this register belongs to
    pub cluster: usize,
    /// The zero-based index of this register
    pub num: usize,
    /// The class of register
    pub class: RegisterClass,
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

/// An error that occurred during register parsing
#[derive(Debug, Clone, Error, PartialEq, Eq, Hash)]
pub enum RegisterParseError {
    /// An unexpected character was encountered while parsing
    #[error("Expected `{expected}`{got}")]
    UnexpectedChar {
        expected: ExpectedValue<char>,
        got: UnexpectedValue<char>,
    },
    /// The class was invalid
    #[error("Invalid register class: Must be one of `r`, `b`, or `l`")]
    Class,
    /// The cluster isn't valid. Note that just because the cluster is
    /// valid, does **not** mean the cluster is correct. If the machine
    /// this register is associated with does not have the referenced
    /// cluster, this register will fail to be used at runtime. See
    /// [`DecodeError::InvalidRegister`] for more details.
    #[error("Invalid (or non-existent) cluster")]
    Cluster,
    /// The register index is invalid. Note that, as with the cluster, just
    /// because the register index is _valid_ does not mean it is correct;
    /// if the index exceeds the bounds of the machine's registers, it will
    /// fail at runtime. See [`DecodeError::InvalidRegister`] for more details.
    #[error("Invalid register number")]
    Number,
}

impl FromStr for Register {
    type Err = WithContext<RegisterParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = ParseState::new(s);
        s.trim_start();
        let ParseState { s, mut idx } = s;
        // Better be a $. Don't use `expect` because it returns a generic
        // ParseError, not a RegisterParseError
        if !s.starts_with('$') {
            return Err(WithContext {
                source: RegisterParseError::UnexpectedChar {
                    got: s.chars().next().into(),
                    expected: '$'.into(),
                },
                ctx: idx.into(),
                help: None,
            });
        }
        let s = &s[1..];
        idx += 1;
        // Chomp the register type
        let Some(Ok(class)) = s.chars().next().map(|c| c.to_string().parse()) else {
            return Err(WithContext {
                source: RegisterParseError::Class,
                ctx: idx.into(),
                help: None,
            });
        };
        let s = &s[1..];
        idx += 1;
        // Chomp the cluster
        let Some((cluster, s)) = s.split_once('.') else {
            return Err(WithContext {
                source: RegisterParseError::Cluster,
                ctx: idx.into(),
                help: Some(help::NO_REG_CLUSTER),
            });
        };
        let val_len = cluster.len();
        let Ok(cluster) = cluster.parse() else {
            return Err(WithContext {
                source: RegisterParseError::Cluster,
                ctx: (idx, val_len).into(),
                help: None,
            });
        };
        idx += val_len + 1;
        let mut s = ParseState { s, idx };
        s.trim_start();
        let ParseState { s, idx } = s;
        let Some(num) = s.split_whitespace().next() else {
            return Err(WithContext {
                source: RegisterParseError::Number,
                ctx: idx.into(),
                help: None,
            });
        };
        let Ok(num) = num.parse() else {
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

/// Where a value lives
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum Location {
    /// The value lives in the specified register
    Register(Register),
    /// The value lives in memory, at the given address
    /// and with the given alignment.
    Memory(usize, Alignment),
}

impl Location {
    /// Sanitize a location
    ///
    /// We won't know until runtime where in memory a read
    /// will occur. This method will ensure that all memory
    /// operations appear to target the exact same address, to aid
    /// in detecting conflicts
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

fn parse_num(num: &str) -> Result<u32, ParseIntError> {
    let num = num.trim();
    if num.starts_with("0x") {
        u32::from_str_radix(num.trim_start_matches("0x"), 16)
    } else {
        num.parse()
    }
}

/// Represents what an operation "does"
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Action {
    /// Basic arithmetic operations that take in a register and
    /// either another register or an immediate, and returns the value
    /// in a register
    BasicArithmetic(arithmetic::Opcode, arithmetic::Args),
    /// Arithmetic operations that involve carry bits
    CarryArithmetic(arithmetic::CarryOpcode, arithmetic::CarryArgs),
    /// A subtraction operation
    Sub(arithmetic::SubArgs),
    /// Operations that load data from memory
    Load(memory::LoadOpcode, memory::LoadArgs),
    /// Operations taht store data in memory
    Store(memory::StoreOpcode, memory::StoreArgs),
    /// Operations that extend numbers (signed or unsigned)
    Extend(arithmetic::ExtendOpcode, arithmetic::ExtendArgs),
    /// Operations that move data between clusters
    Move(intercluster::MoveArgs),
    /// Operations that send data to another cluster
    Send(intercluster::SendArgs),
    /// Operations that receive data from another cluster
    Recv(intercluster::RecvArgs),
    /// Operations that invoke comparisons
    Compare(logical::CompareOpcode, logical::CompareArgs),
    /// Operations that perform basic logic
    Logical(logical::Opcode, logical::Args),
    /// Operations that select values based on a condition
    Select(logical::SelectOpcode, logical::SelectArgs),
}

struct ParseState<'a> {
    s: &'a str,
    idx: usize,
}

impl<'a> ParseState<'a> {
    fn new(s: &'a str) -> Self {
        Self { s, idx: 0 }
    }
    fn split(&self, pattern: char) -> Option<(&'a str, &'a str)> {
        self.s
            .split_once(pattern)
            // I know the delimiter doesn't exist, so if I'm not empty,
            // just return myself
            .or(if self.s.is_empty() {
                None
            } else {
                Some((self.s, ""))
            })
    }
    fn expect(&mut self, next: char) -> Result<(), WithContext<ParseError>> {
        if self.s.starts_with(next) {
            self.s = &self.s[1..];
            self.idx += 1;
            Ok(())
        } else {
            Err(WithContext {
                source: ParseError::Unexpected {
                    wanted: next.into(),
                    got: self.s.chars().next().into(),
                },
                ctx: self.idx.into(),
                help: None,
            })
        }
    }
    fn chomp_register(
        &mut self,
        pattern: char,
    ) -> Result<(Register, SourceSpan), WithContext<ParseError>> {
        let start = self.idx;
        self.trim_start();
        let Some((reg, s)) = self.split(pattern) else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: self.idx.into(),
                help: None,
            });
        };
        let val_len = reg.len();
        let reg = reg.parse().map_err(|r| reg_err(r, self.idx))?;
        self.s = s;
        self.idx += val_len + 1;
        Ok((reg, (start, val_len).into()))
    }
    fn chomp_operand(
        &mut self,
        pattern: char,
    ) -> Result<(Operand, SourceSpan), WithContext<ParseError>> {
        let start = self.idx;
        self.trim_start();
        let Some((operand, s)) = self.split(pattern) else {
            return Err(WithContext {
                source: ParseError::NoValue,
                ctx: self.idx.into(),
                help: None,
            });
        };
        let val_len = operand.len();
        let operand = operand
            .parse()
            .map_err(|op: OperandParseError| WithContext {
                source: ParseError::BadOperand(operand.to_owned(), op),
                ctx: (self.idx, val_len).into(),
                help: None,
            })?;
        self.s = s;
        self.idx += val_len + 1;
        Ok((operand, (start, val_len).into()))
    }
    fn chomp_offset(&mut self) -> Result<(u32, SourceSpan), WithContext<ParseError>> {
        let start = self.idx;
        self.trim_start();
        let Some((num, s)) = self.split('[') else {
            return Err(WithContext {
                source: ParseError::NoOffset,
                ctx: self.idx.into(),
                help: None,
            });
        };
        let val_len = num.len();
        let num = parse_num(num).map_err(|e| WithContext {
            source: ParseError::BadOffset(e),
            ctx: (self.idx, val_len).into(),
            help: None,
        })?;
        self.s = s;
        self.idx += val_len + 1;
        Ok((num, (start, val_len).into()))
    }
    fn chomp_imm(&mut self, pattern: char) -> Result<(u32, SourceSpan), WithContext<ParseError>> {
        let start = self.idx;
        self.trim_start();
        let Some((payload, s)) = self.split(pattern) else {
            return Err(WithContext {
                source: ParseError::NoImmediate,
                ctx: self.idx.into(),
                help: None,
            });
        };
        let val_len = payload.len();
        let num = parse_num(payload).map_err(|e| WithContext {
            source: ParseError::BadImmediate(e),
            ctx: (self.idx, val_len).into(),
            help: None,
        })?;
        self.s = s;
        self.idx += val_len + 1;
        Ok((num, (start, val_len).into()))
    }
    fn trim_start(&mut self) {
        let len = self.s.len();
        self.s = self.s.trim_start();
        self.idx += len - self.s.len();
    }
    fn finish(mut self) -> Result<(), WithContext<ParseError>> {
        self.trim_start();
        if self.s.is_empty() {
            Ok(())
        } else {
            Err(WithContext {
                source: ParseError::ExpectedEnd(self.s.to_owned()),
                ctx: (self.idx, self.s.len()).into(),
                help: None,
            })
        }
    }
}

/// Map a register error with context
fn reg_err(r: WithContext<RegisterParseError>, idx: usize) -> WithContext<ParseError> {
    let ctx = r.span_context(idx);
    let help = Some(r.to_string().into());
    WithContext {
        ctx,
        help,
        source: r.source.into(),
    }
}

/// An unexpected value (including nothing)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnexpectedValue<T>(Option<T>);

impl<T> Display for UnexpectedValue<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref c) = self.0 {
            f.write_fmt(format_args!(", but got `{c}` instead"))
        } else {
            f.write_fmt(format_args!(", but hit end of input instead"))
        }
    }
}

impl<T> From<Option<T>> for UnexpectedValue<T>
where
    T: Display,
{
    fn from(value: Option<T>) -> Self {
        Self(value)
    }
}

impl<T> From<T> for UnexpectedValue<T>
where
    T: Display,
{
    fn from(value: T) -> Self {
        Self(Some(value))
    }
}

/// An expectation of value (or values)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExpectedValue<T>(Vec<T>);

impl<T> Display for ExpectedValue<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vals = self
            .0
            .iter()
            .map(|v| format!("`{v}`"))
            .collect::<Vec<_>>()
            .join(", ");
        if self.0.len() == 1 {
            f.write_str(&vals)
        } else {
            f.write_fmt(format_args!("One of {vals}"))
        }
    }
}

impl<T> From<T> for ExpectedValue<T>
where
    T: Display,
{
    fn from(value: T) -> Self {
        Self(vec![value])
    }
}

/// An error encountered while parsing an operation
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ParseError {
    #[error("Expected a cluster, but could not find one")]
    /// A cluster wasn't found to start the instruction
    NoCluster,
    #[error("Expected an opcode, but none was found")]
    NoOpcode,
    #[error("Unrecognized opcode `{0}`")]
    UnknownOpcode(String),
    #[error("Expected a register, but none was found")]
    NoRegister,
    #[error("Expected an immediate, but none was found")]
    NoImmediate,
    #[error("Failed to parse register: {0}")]
    BadRegister(#[from] RegisterParseError),
    #[error("Wrong register type: Wanted {wanted}, but got {got} instead")]
    WrongRegisterClass {
        wanted: RegisterClass,
        got: RegisterClass,
    },
    #[error(
        "Cluster {0} found, but so was cluster {1}. This instruction only supports one cluster"
    )]
    RegisterClusterMismatch(usize, usize),
    #[error("Operation specified cluster {0}, but register {1} isn't in that cluster")]
    WrongRegisterCluster(usize, Register),
    #[error("Expected an offset, but none was found")]
    NoOffset,
    #[error("Failed to parse offset: {0}")]
    BadOffset(#[source] ParseIntError),
    #[error("Failed to parse immediate: {0}")]
    BadImmediate(#[source] ParseIntError),
    #[error("Expected a value, but got none")]
    NoValue,
    #[error("Failed to parse operand `{0}`")]
    BadOperand(String, #[source] OperandParseError),
    #[error("Expected end of input or comment, but got `{0}`")]
    ExpectedEnd(String),
    #[error("Expected `{wanted}`{got}")]
    Unexpected {
        wanted: ExpectedValue<char>,
        got: UnexpectedValue<char>,
    },
}

impl ParseError {
    pub fn element(&self) -> Cow<'static, str> {
        match self {
            Self::NoCluster
            | Self::RegisterClusterMismatch(_, _)
            | Self::WrongRegisterCluster(_, _) => Cow::Borrowed("cluster"),
            Self::NoOpcode | Self::UnknownOpcode(_) => Cow::Borrowed("opcode"),
            Self::NoRegister
            | Self::BadRegister(_)
            | Self::WrongRegisterClass { got: _, wanted: _ } => Cow::Borrowed("register"),
            Self::NoOffset | Self::BadOffset(_) => Cow::Borrowed("offset"),
            Self::NoValue | Self::BadOperand(_, _) | Self::BadImmediate(_) | Self::NoImmediate => {
                Cow::Borrowed("value")
            }
            Self::ExpectedEnd(_) => Cow::Borrowed("problem"),
            Self::Unexpected { wanted, got: _ } => Cow::Owned(format!("Expected {wanted}")),
        }
    }
}

#[derive(Error, Debug, Clone, PartialEq, Eq, Diagnostic)]
#[error("Operation Parse Failure")]
pub struct ParseDiagnostic {
    pub source: ParseError,
    #[label("{}", source.element())]
    pub problem: SourceSpan,
    #[source_code]
    pub src: NamedSource<String>,
    #[help]
    pub help: Option<Cow<'static, str>>,
}

impl ParseDiagnostic {
    pub fn from_err(p: WithContext<ParseError>, src: NamedSource<String>, offset: usize) -> Self {
        let problem = p.span_context(offset);
        let help = p.help;
        let source = p.source;
        Self {
            problem,
            source,
            src,
            help,
        }
    }
}

fn check_cluster(
    r1: Register,
    r2: Register,
    ctx: SourceSpan,
) -> Result<(), WithContext<ParseError>> {
    if r1.cluster == r2.cluster {
        Ok(())
    } else {
        Err(WithContext {
            ctx: (ctx.offset() + 1).into(),
            help: Some(help::CLUSTER_MISMATCH),
            source: ParseError::RegisterClusterMismatch(r1.cluster, r2.cluster),
        })
    }
}

impl FromStr for Action {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        static OPCODE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"\w+").unwrap());
        let s = s.find(COMMENT_START).map_or(s, |com| &s[..com]);
        let mut s = ParseState::new(s);
        s.trim_start();
        let ParseState { s, idx } = s;

        let Some(cap) = OPCODE.captures(s).and_then(|c| c.get(0)) else {
            return Err(WithContext {
                source: ParseError::NoOpcode,
                ctx: idx.into(),
                help: Some(help::NO_OPCODE),
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
        if let Ok(ar_opcode) = opcode.parse::<arithmetic::Opcode>() {
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
        } else if let Ok(lg_opcode) = opcode.parse::<logical::Opcode>() {
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
            let help = arithmetic::Opcode::iter()
                .map(arithmetic::Opcode::code)
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
    /// The inputs for this operation
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
    /// The outputs for this operation
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
    /// Decode this operation into concrete outcomes
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
    /// Obtain a textual representation of the command code (opcode)
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
    /// Obtain the used resource
    pub const fn kind(&self) -> Resource {
        match self {
            Self::BasicArithmetic(op, _) => op.kind(),
            Self::CarryArithmetic(_, _)
            | Self::Sub(_)
            | Self::Extend(_, _)
            | Self::Compare(_, _)
            | Self::Logical(_, _)
            | Self::Select(_, _)
            | Self::Move(_) => Resource::Arithmetic,
            Self::Load(_, _) => Resource::Load,
            Self::Store(_, _) => Resource::Store,
            Self::Send(_) | Self::Recv(_) => Resource::Copy,
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

/// A single operation within an [`Instruction`]
///
/// An operation in VLIW is similar to the concept of an instruction in
/// traditional assembly. In traditional assembly, there's only one slot
/// to issue commands; in VLIW, there are potentially more, so a single
/// cycle can contain multiple commands. Each of those commands in VLIW
/// is known as an `Operation`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Operation {
    /// If present, this is the context within which an operation was found.
    /// Typically, this context is absolute; for example, the absolute position
    /// within a source file. By default, it's not provided; this allows parsing
    /// an operation directly from a single line, without the context of the rest
    /// of the source code.
    ///
    /// The first entry in the tuple represents the line number (one-indexed) that
    /// this operation occured on; the second represents the absolute span that
    /// this operation resides within.
    pub ctx: Option<(usize, SourceSpan)>,
    /// The cluster this operation was invoked in
    pub cluster: usize,
    /// The action this operation will undertake
    pub action: Action,
}

impl Operation {
    /// Generate a summary of this command
    ///
    /// The full-blown display method for an `Operation` displays the
    /// entire command, including all the inputs and outputs. However,
    /// this is too much for just referring to the operation quickly; that
    /// is where this method is most useful. Typically it will be used to
    /// refer to an operation that caused undefined behavior.
    pub fn summary(&self) -> String {
        let out = format!("{} operation", self.action.code());
        if let Some((line, _)) = self.ctx {
            out + &format!(" on line {line}")
        } else {
            out
        }
    }
    /// Add context to an operation
    pub fn with_context(self, ctx: (usize, SourceSpan)) -> Self {
        Self {
            ctx: Some(ctx),
            ..self
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
        let mut s = ParseState::new(s);
        s.trim_start();
        s.expect('c').map_err(|p| WithContext {
            help: Some(help::BAD_CLUSTER),
            ..p
        })?;
        let ParseState { s, mut idx } = s;
        // First thing better be cluster
        let Some(c) = CLUSTER.captures(s).and_then(|s| s.get(0)) else {
            // Couldn't find the cluster
            return Err(WithContext {
                source: ParseError::NoCluster,
                ctx: idx.into(),
                help: Some(help::NO_CLUSTER),
            });
        };
        let cluster = c.as_str().parse().map_err(|_e| WithContext {
            source: ParseError::NoOffset,
            ctx: (idx, c.len() - 1).into(),
            help: None,
        })?;
        let clust_idx = idx;
        idx += c.len();
        let op: Action = s[c.end()..].parse().map_err(|e: WithContext<_>| {
            let span = e.span_context(idx);
            WithContext { ctx: span, ..e }
        })?;

        let regs = op
            .inputs()
            .into_iter()
            .chain(op.outputs())
            .filter_map(|l| match l {
                Location::Register(r) => Some(r),
                Location::Memory(_, _) => None,
            });

        for r in regs {
            if r.cluster != cluster {
                return Err(WithContext {
                    source: ParseError::WrongRegisterCluster(cluster, r),
                    ctx: clust_idx.into(),
                    help: None,
                });
            }
        }
        Ok(Self {
            cluster,
            action: op,
            ctx: None,
        })
    }
}

/// A group of [`Operation`]s that are issued in the same
/// cycle
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

    use miette::SourceSpan;

    use crate::operation::{Alignment, RegisterParseError, WithContext};

    use super::{
        arithmetic::{Args, CarryArgs, CarryOpcode, Opcode, SubArgs},
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

        negative::<Register, _>(&["r0.1", "$d0.1", "b", "$0.1", "$.1", "$", "0", "$r0", ""]);
    }

    #[test]
    fn reg_diagnostic() {
        // Should fail because no $
        let res = "r0.1".parse::<Register>();
        assert!(res.is_err());
        let WithContext { source, ctx, .. } = res.unwrap_err();
        assert_eq!(
            source,
            RegisterParseError::UnexpectedChar {
                expected: '$'.into(),
                got: 'r'.into(),
            }
        );
        assert_eq!(ctx, SourceSpan::new(0.into(), 0));

        // Should fail because no class
        let res = "  $0.1".parse::<Register>();
        assert!(res.is_err());
        let WithContext { source, ctx, .. } = res.unwrap_err();
        assert_eq!(source, RegisterParseError::Class);
        assert_eq!(ctx, SourceSpan::new(3.into(), 0));

        // Should fail because no cluster
        let res = "$rx.1".parse::<Register>();
        assert!(res.is_err());
        let WithContext { source, ctx, .. } = res.unwrap_err();
        assert_eq!(source, RegisterParseError::Cluster);
        assert_eq!(ctx, SourceSpan::new(2.into(), 1));

        // Should fail because no cluster
        let res = "$r.1".parse::<Register>();
        assert!(res.is_err());
        let WithContext { source, ctx, .. } = res.unwrap_err();
        assert_eq!(source, RegisterParseError::Cluster);
        assert_eq!(ctx, SourceSpan::new(2.into(), 0));

        // Should fail because bad number
        let res = "$r0.".parse::<Register>();
        assert!(res.is_err());
        let WithContext { source, ctx, .. } = res.unwrap_err();
        assert_eq!(source, RegisterParseError::Number);
        assert_eq!(ctx, SourceSpan::new(4.into(), 0));

        // Should fail because bad number
        let res = "$r0.x".parse::<Register>();
        assert!(res.is_err());
        let WithContext { source, ctx, .. } = res.unwrap_err();
        assert_eq!(source, RegisterParseError::Number);
        assert_eq!(ctx, SourceSpan::new(4.into(), 1));
    }

    #[test]
    fn reg_display() {
        display(&[
            (
                "$r1.1",
                Register {
                    cluster: 1,
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
                        Opcode::MaxUnsigned,
                        Args {
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
                        Opcode::MaxUnsigned,
                        Args {
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
