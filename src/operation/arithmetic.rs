use std::{fmt::Display, str::FromStr};

use crate::{Location, Machine, Outcome};

use super::{
    parse_num, trim_start, Kind, Operand, ParseError, Register, RegisterParseError, RegisterType,
    WithContext,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
pub enum BasicOpcode {
    Add,
    And,
    AndComplement,
    Max,
    MaxUnsigned,
    Min,
    MinUnsigned,
    Or,
    OrComplement,
    Shift1Add,
    Shift2Add,
    Shift3Add,
    Shift4Add,
    ShiftLeft,
    ShiftRight,
    ShiftRightUnsigned,
    Xor,
    MultiplyLowLow,
    MultiplyLowLowUnsigned,
    MultiplyLowHigh,
    MultiplyLowHighUnsigned,
    MultiplyHighHigh,
    MultiplyHighHighUnsigned,
    MultiplyLow,
    MultiplyLowUnsigned,
    MultiplyHigh,
    MultiplyHighUnsigned,
    MultiplyHighShift,
}

impl BasicOpcode {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::And => "and",
            Self::AndComplement => "andc",
            Self::Max => "max",
            Self::MaxUnsigned => "maxu",
            Self::Min => "min",
            Self::MinUnsigned => "minu",
            Self::Or => "or",
            Self::OrComplement => "orc",
            Self::Shift1Add => "sh1add",
            Self::Shift2Add => "sh2add",
            Self::Shift3Add => "sh3add",
            Self::Shift4Add => "sh4add",
            Self::ShiftLeft => "shl",
            Self::ShiftRight => "shr",
            Self::ShiftRightUnsigned => "shru",
            Self::Xor => "xor",
            Self::MultiplyLowLow => "mpyll",
            Self::MultiplyLowLowUnsigned => "mpyllu",
            Self::MultiplyLowHigh => "mpylh",
            Self::MultiplyLowHighUnsigned => "mpylhu",
            Self::MultiplyHighHigh => "mpyhh",
            Self::MultiplyHighHighUnsigned => "mpyhhu",
            Self::MultiplyLow => "mpyl",
            Self::MultiplyLowUnsigned => "mpylu",
            Self::MultiplyHigh => "mpyh",
            Self::MultiplyHighUnsigned => "mpyhu",
            Self::MultiplyHighShift => "mpyhs",
        }
    }
    pub fn execute(&self, a: u32, b: u32) -> u32 {
        const fn lower_signed(r: u32) -> i32 {
            (((r as i32) << 16) & (0xffff_0000_u32 as i32)) >> 16
        }
        const fn higher_signed(r: u32) -> i32 {
            ((r as i32) >> 16) & (0xffffu32 as i32)
        }
        match self {
            Self::Add => a + b,
            Self::And => a & b,
            Self::AndComplement => (!a) & b,
            Self::Max => ((a as i32).max(b as i32)) as u32,
            Self::MaxUnsigned => a.max(b),
            Self::Min => ((a as i32).min(b as i32)) as u32,
            Self::MinUnsigned => a.min(b),
            Self::MultiplyHigh => ((a as i32) * higher_signed(b)) as u32,
            Self::MultiplyHighHigh => (higher_signed(a) * higher_signed(b)) as u32,
            Self::MultiplyHighHighUnsigned => ((a >> 16) & 0xffff) * ((b >> 16) & 0xffff),
            Self::MultiplyHighShift => a * ((b >> 16) as i16) as u32,
            Self::MultiplyHighUnsigned => a * ((b >> 16) & 0xffff),
            Self::MultiplyLow => ((a as i32) * lower_signed(b)) as u32,
            Self::MultiplyLowHigh => (lower_signed(a) * higher_signed(b)) as u32,
            Self::MultiplyLowHighUnsigned => (a & 0xffff) * ((b >> 16) & 0xffff),
            Self::MultiplyLowLow => (lower_signed(a) * lower_signed(b)) as u32,
            Self::MultiplyLowLowUnsigned => (a & 0xffff) * (b & 0xffff),
            Self::MultiplyLowUnsigned => a * (b & 0xffff),
            Self::Or => a | b,
            Self::OrComplement => (!a) | b,
            Self::Shift1Add => (a << 1) + b,
            Self::Shift2Add => (a << 2) + b,
            Self::Shift3Add => (a << 3) + b,
            Self::Shift4Add => (a << 4) + b,
            Self::ShiftLeft => a << b,
            Self::ShiftRight => ((a as i32) >> b) as u32,
            Self::ShiftRightUnsigned => a >> b,
            Self::Xor => a ^ b,
        }
    }
    pub const fn kind(self) -> Kind {
        match self {
            Self::MultiplyHigh
            | Self::MultiplyHighHigh
            | Self::MultiplyHighHighUnsigned
            | Self::MultiplyHighShift
            | Self::MultiplyHighUnsigned
            | Self::MultiplyLow
            | Self::MultiplyLowHigh
            | Self::MultiplyLowHighUnsigned
            | Self::MultiplyLowLow
            | Self::MultiplyLowLowUnsigned
            | Self::MultiplyLowUnsigned => Kind::Multiplication,
            _ => Kind::Arithmetic,
        }
    }
}

impl FromStr for BasicOpcode {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "add" => Self::Add,
            "and" => Self::And,
            "andc" => Self::AndComplement,
            "max" => Self::Max,
            "maxu" => Self::MaxUnsigned,
            "min" => Self::Min,
            "minu" => Self::MinUnsigned,
            "or" => Self::Or,
            "orc" => Self::OrComplement,
            "sh1add" => Self::Shift1Add,
            "sh2add" => Self::Shift2Add,
            "sh3add" => Self::Shift3Add,
            "sh4add" => Self::Shift4Add,
            "shl" => Self::ShiftLeft,
            "shr" => Self::ShiftRight,
            "shru" => Self::ShiftRightUnsigned,
            "xor" => Self::Xor,
            "mpyll" => Self::MultiplyLowLow,
            "mpyllu" => Self::MultiplyLowLowUnsigned,
            "mpylh" => Self::MultiplyLowHigh,
            "mpylhu" => Self::MultiplyLowHighUnsigned,
            "mpyhh" => Self::MultiplyHighHigh,
            "mpyhhu" => Self::MultiplyHighHighUnsigned,
            "mpyl" => Self::MultiplyLow,
            "mpylu" => Self::MultiplyLowUnsigned,
            "mpyh" => Self::MultiplyHigh,
            "mpyhu" => Self::MultiplyHighUnsigned,
            "mpyhs" => Self::MultiplyHighShift,
            _ => return Err(()),
        })
    }
}

impl Display for BasicOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BasicArgs {
    /// The first input register
    src1: Register,
    /// The second argument, either a register or an immediate
    src2: Operand,
    /// The destination register
    dst: Register,
}

impl FromStr for BasicArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the destination register
        if s.starts_with('=') {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        }
        let Some((dst, s)) = s.split_once('=') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = dst.len();
        let dst: Register =
            dst.parse()
                .map_err(|r: WithContext<RegisterParseError>| WithContext {
                    source: r.source.into(),
                    span: r.span_context(idx),
                    help: None,
                })?;
        if dst.bank != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: dst.bank,
                },
                span: (idx, 0).into(),
                help: None,
            });
        }
        // We're past the =, trim and get the first register
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        if s.starts_with(',') {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        }
        let Some((src1, s)) = s.split_once(',') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src1.len();
        let src1: Register =
            src1.parse()
                .map_err(|r: WithContext<RegisterParseError>| WithContext {
                    source: r.source.into(),
                    span: r.span_context(idx),
                    help: None,
                })?;
        if src1.bank != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: dst.bank,
                },
                span: (idx, 0).into(),
                help: None,
            });
        }
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // We're past the , this could either be a register or an immediate
        let Some(src2) = s.split_whitespace().next() else {
            return Err(WithContext {
                source: ParseError::NoValue,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src2.len();
        let src2 = if let Ok(r) = src2.parse::<Register>() {
            if r.bank != RegisterType::General {
                return Err(WithContext {
                    source: ParseError::WrongRegisterType {
                        wanted: RegisterType::General,
                        got: dst.bank,
                    },
                    span: (idx, 0).into(),
                    help: None,
                });
            }
            Operand::Register(r)
        } else if let Ok(i) = parse_num(src2) {
            Operand::Immediate(i)
        } else {
            return Err(WithContext {
                source: ParseError::BadValue(src2.to_owned()),
                span: (idx, src2.len()).into(),
                help: None,
            });
        };
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                span: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { src1, src2, dst })
        }
    }
}

impl BasicArgs {
    pub fn decode(&self, opcode: BasicOpcode, machine: &Machine) -> Outcome {
        let dst = Location::Register(self.dst);
        let value = opcode.execute(machine.gregs[self.src1.num], self.src2.resolve(machine));
        Outcome { value, dst }
    }
    pub fn inputs(&self) -> Vec<Location> {
        match self.src2 {
            Operand::Immediate(_) => vec![Location::Register(self.src1)],
            Operand::Register(r) => {
                vec![Location::Register(self.src1), Location::Register(r)]
            }
        }
    }
}

impl Display for BasicArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.src2 {
            Operand::Register(r) => f.write_fmt(format_args!(
                "$r0.{} = $r0.{}, $r0.{}",
                self.dst, self.src1, r
            )),
            Operand::Immediate(i) => f.write_fmt(format_args!(
                "$r0.{} = $r0.{}, 0x{:x}",
                self.dst, self.src1, i
            )),
        }
    }
}

// #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
// pub enum CarryOpcode {
//     AddCarry,
//     Divide,
// }

// impl CarryOpcode {
//     pub const fn code(&self) -> &'static str {
//         match self {
//             Self::AddCarry => "addcg",
//             Self::Divide => "divs",
//         }
//     }
//     pub const fn kind(&self) -> Kind {
//         Kind::Arithmetic
//     }
// }

// impl Display for CarryOpcode {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.write_str(self.code())
//     }
// }

// #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
// pub struct CarryArgs {
//     src1: Register,
//     src2: Register,
//     cin: Register,
//     dst: Register,
//     cout: Register,
// }
