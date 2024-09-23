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

pub const COMMENT_START: char = '#';

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
    pub fn resolve(self, machine: &Machine) -> u32 {
        match self {
            Self::Register(r) => machine[r],
            Self::Immediate(i) => i,
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
    pub(crate) bank: RegisterType,
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { num, bank } = self;
        f.write_fmt(format_args!("${bank}0.{num}"))
    }
}

#[derive(Debug, Clone, Copy, Error, PartialEq, Eq, Hash)]
pub enum RegisterParseError {
    #[error("Expected `{expected}`; got `{got}`")]
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

#[derive(Debug, Clone, Error, PartialEq, Eq, Hash)]
#[error("{source}")]
pub struct WithContext<T> {
    pub source: T,
    pub span: SourceSpan,
    pub help: Option<String>,
}

impl<T> WithContext<T> {
    pub fn span_context(&self, start: usize) -> SourceSpan {
        (self.span.offset() + start, self.span.len()).into()
    }
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
                span: (idx, 0).into(),
                help: None,
            });
        }
        let s = &s[1..];
        idx += 1;
        // Chomp the register type
        let Some(Ok(bank)) = s.chars().next().map(|c| c.to_string().parse()) else {
            return Err(WithContext {
                source: RegisterParseError::Class,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let s = &s[1..];
        idx += 1;
        if !s.starts_with('0') {
            return Err(WithContext {
                source: RegisterParseError::Cluster,
                span: (idx, 0).into(),
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
                span: (idx, 0).into(),
            });
        }
        let s = &s[1..];
        idx += 1;
        let s = trim_start(s, &mut idx).trim();
        let Ok(num) = s.parse() else {
            return Err(WithContext {
                source: RegisterParseError::Number,
                span: (idx, s.len()).into(),
                help: None,
            });
        };
        Ok(Self { num, bank })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Location {
    Register(Register),
    Memory(usize),
}

impl Location {
    pub const fn sanitize(self) -> Self {
        match self {
            Self::Register(r) => Self::Register(r),
            Self::Memory(_) => Self::Memory(0),
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Memory(m) => f.write_fmt(format_args!("Memory[0x{m:4x}]")),
            Self::Register(r) => f.write_fmt(format_args!("{r}")),
        }
    }
}

pub fn parse_num(num: &str) -> Result<u32, ParseIntError> {
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
pub enum Operation {
    Arithmetic(arithmetic::BasicOpcode, arithmetic::BasicArgs),
    Load(memory::LoadOpcode, memory::LoadArgs),
    Store(memory::StoreOpcode, memory::StoreArgs),
    // SignExtend(opcode, args),
    // ...
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
            f.write_fmt(format_args!(", but got {c} instead"))
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
    #[error("Failed to parse value `{0}`")]
    BadValue(String),
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
            Self::NoValue | Self::BadValue(_) => "value",
            Self::ExpectedEnd(_) | Self::UnexpectedCharacter { wanted: _, got: _ } => "problem",
        }
    }
}

impl From<RegisterParseError> for ParseError {
    fn from(value: RegisterParseError) -> Self {
        Self::BadRegister(value)
    }
}

impl FromStr for Operation {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = remove_comment(s);
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        static OPCODE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"\w+").unwrap());

        let Some(cap) = OPCODE.captures(s).and_then(|c| c.get(0)) else {
            return Err(WithContext {
                source: ParseError::NoOpcode,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let opcode = cap.as_str();
        let rest = &s[cap.len()..];
        let err = move |p: WithContext<ParseError>| {
            let span = p.span_context(idx + cap.len());
            WithContext {
                source: p.source,
                span,
                help: None,
            }
        };
        if let Ok(ar_opcode) = opcode.parse::<arithmetic::BasicOpcode>() {
            // TODO: Arithmetic parsing failed. I might not need to do anything?
            let args = rest.parse().map_err(err)?;
            Ok(Self::Arithmetic(ar_opcode, args))
        } else if let Ok(ld_opcode) = opcode.parse::<memory::LoadOpcode>() {
            let args = rest.parse().map_err(err)?;
            Ok(Self::Load(ld_opcode, args))
        } else if let Ok(st_opcode) = opcode.parse::<memory::StoreOpcode>() {
            let args = rest.parse().map_err(err)?;
            Ok(Self::Store(st_opcode, args))
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
                span: (idx, cap.len()).into(),
                help,
            })
        }
    }
}

impl Operation {
    pub fn inputs(&self) -> Vec<Location> {
        match self {
            Self::Arithmetic(_, args) => args.inputs(),
            Self::Load(_, load) => load.inputs(),
            Self::Store(_, store) => store.inputs(),
        }
    }
    pub fn decode(&self, machine: &Machine) -> Option<Outcome> {
        match self {
            Self::Arithmetic(op, args) => Some(args.decode(*op, machine)),
            Self::Load(op, args) => Some(args.decode(*op, machine)),
            Self::Store(op, args) => Some(args.decode(*op, machine)),
        }
    }
    pub const fn code(&self) -> &'static str {
        match self {
            Self::Arithmetic(op, _) => op.code(),
            Self::Load(op, _) => op.code(),
            Self::Store(op, _) => op.code(),
        }
    }
    pub const fn kind(&self) -> Kind {
        match self {
            Self::Arithmetic(op, _) => op.kind(),
            Self::Load(_, _) => Kind::Load,
            Self::Store(_, _) => Kind::Store,
        }
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Arithmetic(op, args) => f.write_fmt(format_args!("{op} {args}")),
            Self::Load(op, args) => f.write_fmt(format_args!("{op} {args}")),
            Self::Store(op, args) => f.write_fmt(format_args!("{op} {args}")),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Instruction {
    pub ctx: Option<(usize, SourceSpan)>,
    pub cluster: usize,
    pub op: Operation,
}

impl Instruction {
    pub fn summary(&self) -> String {
        let out = format!("{} instruction", self.op.code());
        if let Some((line, _)) = self.ctx {
            out + &format!(" on line {line}")
        } else {
            out
        }
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { cluster, op, .. } = self;
        f.write_fmt(format_args!("c{cluster} {op}"))
    }
}

impl FromStr for Instruction {
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
                span: (idx, 0).into(),
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
                span: (idx, 0).into(),
                help: Some(String::from("All instructions must have a cluster")),
            });
        };
        let cluster = c.as_str().parse().map_err(|_e| WithContext {
            source: ParseError::NoOffset,
            span: (idx, c.len()).into(),
            help: None,
        })?;
        idx += c.len();
        let op = s[c.end()..].parse().map_err(|e: WithContext<ParseError>| {
            let span = e.span_context(idx);
            WithContext { span, ..e }
        })?;
        Ok(Self {
            cluster,
            op,
            ctx: None,
        })
    }
}

impl Instruction {
    pub const fn with_context(self, ctx: (usize, SourceSpan)) -> Self {
        Self {
            ctx: Some(ctx),
            ..self
        }
    }
}
