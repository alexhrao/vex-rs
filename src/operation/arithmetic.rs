use std::{fmt::Display, str::FromStr};

use crate::{Location, Machine, Outcome};

use super::{
    check_cluster, reg_err, trim_start, DecodeError, Info, Kind, Operand, OperandParseError,
    ParseError, Register, RegisterClass, WithContext,
};

/// Basic Opcodes for Arithmetic
///
/// "Basic" here means that is follows the [`BasicArgs`] convention;
/// in other words, an instruction of the form
///
/// ```asm
/// <reg> = <reg>, <reg|imm>
/// ```
///
/// This encompasses most of the arithmetic operations, including all
/// multiplicative ones.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
pub enum BasicOpcode {
    /// Add two unsigned numbers together
    Add,
    /// Bitwise AND
    And,
    /// Bitwise AND while complementing (i.e., `!`) the first source register
    AndComplement,
    /// Signed maximum of the two operands
    MaxSigned,
    /// Unsigned maximum of the two operands
    MaxUnsigned,
    /// Signed minimum of the two operands
    MinSigned,
    /// Unsigned minimum of the two operands
    MinUnsigned,
    /// Bitwise OR
    Or,
    /// Bitwise OR while complementing (i.e., `!`) the first source register
    OrComplement,
    /// Shift the first source left by 1 bit and add the other source
    Shift1Add,
    /// Shift the first source left by 2 bits and add the other source
    Shift2Add,
    /// Shift the first source left by 3 bits and add the other source
    Shift3Add,
    /// Shift the first source left by 4 bits and add the other source
    Shift4Add,
    /// Shift the first source left by `<src2>` number of bits
    ShiftLeft,
    /// Shift the first source right by `<src2>` number of bits, retaining signedness
    ShiftRightSigned,
    /// Shift the first source right by `<src2>` number of bits
    ShiftRightUnsigned,
    /// Bitwise XOR
    Xor,
    /// Multiply lower 16 bits of both **signed** sources
    MultiplyLowLowSigned,
    /// Multiply lower 16 bits of both **unsigned** sources
    MultiplyLowLowUnsigned,
    /// Multiply lower 16 bits of the first source with the upper 16 bits
    /// of the second source, treating both as **signed**
    MultiplyLowHighSigned,
    /// Multiply lower 16 bits of the first source with the upper 16 bits
    /// of the second source, treating both as **unsigned**
    MultiplyLowHighUnsigned,
    /// Multiply higher 16 bits of both **signed** sources
    MultiplyHighHighSigned,
    /// Multiply lower 16 bits of both **unsigned** sources
    MultiplyHighHighUnsigned,
    /// Multiply the lower 16 bits of the second source by the full 32 bits
    /// of the first source, treating both as **signed**
    MultiplyLowSigned,
    /// Multiply the lower 16 bits of the second source by the full 32 bits
    /// of the first source, treating both as **unsigned**
    MultiplyLowUnsigned,
    /// Multiply the higher 16 bits of the second source by the full 32 bits
    /// of the first source, treating both as **signed**
    MultiplyHighSigned,
    /// Multiply the higher 16 bits of the second source by the full 32 bits
    /// of the first source, treating both as **unsigned**
    MultiplyHighUnsigned,
    /// Multiply the higher 16 bits of the second source by the full 32 bits
    /// of the first source, treating both as **signed**. However, this differs
    /// from [`MultiplyHigh`](`BasicOpcode::MultiplyHigh`) in that the higher
    /// 16 bits are shifted back into the higher position before multiplication
    MultiplyHighShift,
}

impl BasicOpcode {
    /// The opcode for this basic operation
    pub const fn code(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::And => "and",
            Self::AndComplement => "andc",
            Self::MaxSigned => "max",
            Self::MaxUnsigned => "maxu",
            Self::MinSigned => "min",
            Self::MinUnsigned => "minu",
            Self::Or => "or",
            Self::OrComplement => "orc",
            Self::Shift1Add => "sh1add",
            Self::Shift2Add => "sh2add",
            Self::Shift3Add => "sh3add",
            Self::Shift4Add => "sh4add",
            Self::ShiftLeft => "shl",
            Self::ShiftRightSigned => "shr",
            Self::ShiftRightUnsigned => "shru",
            Self::Xor => "xor",
            Self::MultiplyLowLowSigned => "mpyll",
            Self::MultiplyLowLowUnsigned => "mpyllu",
            Self::MultiplyLowHighSigned => "mpylh",
            Self::MultiplyLowHighUnsigned => "mpylhu",
            Self::MultiplyHighHighSigned => "mpyhh",
            Self::MultiplyHighHighUnsigned => "mpyhhu",
            Self::MultiplyLowSigned => "mpyl",
            Self::MultiplyLowUnsigned => "mpylu",
            Self::MultiplyHighSigned => "mpyh",
            Self::MultiplyHighUnsigned => "mpyhu",
            Self::MultiplyHighShift => "mpyhs",
        }
    }
    /// Execute the operation using the two 32-bit numbers
    pub fn execute(&self, a: u32, b: u32) -> u32 {
        const fn lower_signed(r: u32) -> i32 {
            (((r as i32) << 16) & (0xffff_0000_u32 as i32)) >> 16
        }
        const fn higher_signed(r: u32) -> i32 {
            ((r as i32) >> 16) & (0xffffu32 as i32)
        }
        match self {
            Self::Add => a.wrapping_add(b),
            Self::And => a & b,
            Self::AndComplement => (!a) & b,
            Self::MaxSigned => ((a as i32).max(b as i32)) as u32,
            Self::MaxUnsigned => a.max(b),
            Self::MinSigned => ((a as i32).min(b as i32)) as u32,
            Self::MinUnsigned => a.min(b),
            Self::MultiplyHighSigned => ((a as i32).wrapping_mul(higher_signed(b))) as u32,
            Self::MultiplyHighHighSigned => {
                (higher_signed(a).wrapping_mul(higher_signed(b))) as u32
            }
            Self::MultiplyHighHighUnsigned => ((a >> 16) & 0xffff).wrapping_mul((b >> 16) & 0xffff),
            Self::MultiplyHighShift => a.wrapping_mul(((b >> 16) as i16) as u32),
            Self::MultiplyHighUnsigned => a.wrapping_mul((b >> 16) & 0xffff),
            Self::MultiplyLowSigned => ((a as i32).wrapping_mul(lower_signed(b))) as u32,
            Self::MultiplyLowHighSigned => (lower_signed(a).wrapping_mul(higher_signed(b))) as u32,
            Self::MultiplyLowHighUnsigned => (a & 0xffff).wrapping_mul((b >> 16) & 0xffff),
            Self::MultiplyLowLowSigned => (lower_signed(a).wrapping_mul(lower_signed(b))) as u32,
            Self::MultiplyLowLowUnsigned => (a & 0xffff).wrapping_mul(b & 0xffff),
            Self::MultiplyLowUnsigned => a.wrapping_mul(b & 0xffff),
            Self::Or => a | b,
            Self::OrComplement => (!a) | b,
            Self::Shift1Add => (a << 1).wrapping_add(b),
            Self::Shift2Add => (a << 2).wrapping_add(b),
            Self::Shift3Add => (a << 3).wrapping_add(b),
            Self::Shift4Add => (a << 4).wrapping_add(b),
            Self::ShiftLeft => a << b,
            Self::ShiftRightSigned => ((a as i32) >> b) as u32,
            Self::ShiftRightUnsigned => a >> b,
            Self::Xor => a ^ b,
        }
    }
    /// Get the kind of this opcode
    pub const fn kind(self) -> Kind {
        match self {
            Self::MultiplyHighSigned
            | Self::MultiplyHighHighSigned
            | Self::MultiplyHighHighUnsigned
            | Self::MultiplyHighShift
            | Self::MultiplyHighUnsigned
            | Self::MultiplyLowSigned
            | Self::MultiplyLowHighSigned
            | Self::MultiplyLowHighUnsigned
            | Self::MultiplyLowLowSigned
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
            "max" => Self::MaxSigned,
            "maxu" => Self::MaxUnsigned,
            "min" => Self::MinSigned,
            "minu" => Self::MinUnsigned,
            "or" => Self::Or,
            "orc" => Self::OrComplement,
            "sh1add" => Self::Shift1Add,
            "sh2add" => Self::Shift2Add,
            "sh3add" => Self::Shift3Add,
            "sh4add" => Self::Shift4Add,
            "shl" => Self::ShiftLeft,
            "shr" => Self::ShiftRightSigned,
            "shru" => Self::ShiftRightUnsigned,
            "xor" => Self::Xor,
            "mpyll" => Self::MultiplyLowLowSigned,
            "mpyllu" => Self::MultiplyLowLowUnsigned,
            "mpylh" => Self::MultiplyLowHighSigned,
            "mpylhu" => Self::MultiplyLowHighUnsigned,
            "mpyhh" => Self::MultiplyHighHighSigned,
            "mpyhhu" => Self::MultiplyHighHighUnsigned,
            "mpyl" => Self::MultiplyLowSigned,
            "mpylu" => Self::MultiplyLowUnsigned,
            "mpyh" => Self::MultiplyHighSigned,
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

/// Arguments that follow the basic structure
///
/// This structure encompasses most VEX commands; it consists of
/// a destination register, a source register, and a second operand,
/// which will either be an immediate value or a register.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BasicArgs {
    /// The first input register
    pub(super) src1: Register,
    /// The second argument, either a register or an immediate
    pub(super) src2: Operand,
    /// The destination register
    pub(super) dst: Register,
}

impl FromStr for BasicArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the destination register
        let Some((dst, s)) = s.split_once('=') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = dst.len();
        let dst: Register = dst.parse().map_err(|r| reg_err(r, idx))?;
        if dst.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: dst.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        // We're past the =, trim and get the first register
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        let Some((src1, s)) = s.split_once(',') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src1.len();
        let src1: Register = src1.parse().map_err(|r| reg_err(r, idx))?;
        if src1.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src1.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        check_cluster(dst, src1, idx, val_len)?;
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // We're past the , this could either be a register or an immediate
        let mut splitter = s.split_whitespace();
        let Some(src2) = splitter.next() else {
            return Err(WithContext {
                source: ParseError::NoValue,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src2.len();
        let src2: Operand = src2.parse().map_err(|op: OperandParseError| WithContext {
            source: ParseError::BadOperand(src2.to_owned(), op),
            ctx: (idx, val_len).into(),
            help: None,
        })?;
        if let Operand::Register(r) = src2 {
            if r.class != RegisterClass::General {
                return Err(WithContext {
                    source: ParseError::WrongRegisterClass {
                        wanted: RegisterClass::General,
                        got: r.class,
                    },
                    ctx: (idx, 0).into(),
                    help: None,
                });
            }
            check_cluster(dst, r, idx, val_len)?;
        }
        idx += val_len + 1;
        let s = trim_start(splitter.next().unwrap_or_default(), &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { src1, src2, dst })
        }
    }
}

impl Info for BasicArgs {
    type Opcode = BasicOpcode;
    fn inputs(&self) -> Vec<Location> {
        match self.src2 {
            Operand::Immediate(_) => vec![Location::Register(self.src1)],
            Operand::Register(r) => {
                vec![Location::Register(self.src1), Location::Register(r)]
            }
        }
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn decode(&self, opcode: BasicOpcode, machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        // Make sure dst works
        machine.get_reg(self.dst)?;
        let dst = Location::Register(self.dst);
        let value = opcode.execute(machine.get_reg(self.src1)?, self.src2.resolve(machine)?);
        Ok(vec![Outcome { value, dst }])
    }
}

impl Display for BasicArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { dst, src1, src2 } = self;
        f.write_fmt(format_args!("{dst} = {src1}, {src2}"))
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum CarryOpcode {
    AddCarry,
    Divide,
}

impl CarryOpcode {
    pub const fn code(&self) -> &'static str {
        match self {
            Self::AddCarry => "addcg",
            Self::Divide => "divs",
        }
    }
    pub const fn kind(&self) -> Kind {
        Kind::Arithmetic
    }
}

impl Display for CarryOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

impl FromStr for CarryOpcode {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "addcg" => Self::AddCarry,
            "divs" => Self::Divide,
            _ => return Err(()),
        })
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct CarryArgs {
    pub(super) src1: Register,
    pub(super) src2: Register,
    pub(super) cin: Register,
    pub(super) dst: Register,
    pub(super) cout: Register,
}

impl FromStr for CarryArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the first destination register
        let Some((dst, s)) = s.split_once(',') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = dst.len();
        let dst: Register = dst.parse().map_err(|r| reg_err(r, idx))?;
        if dst.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: dst.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        // We're past the ',', trim and get the second output register
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        let Some((cout, s)) = s.split_once('=') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = cout.len();
        let cout: Register = cout.parse().map_err(|r| reg_err(r, idx))?;
        if cout.class != RegisterClass::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::Branch,
                    got: cout.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        check_cluster(dst, cout, idx, val_len)?;
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // We're past the =, get the input registers
        let Some((cin, s)) = s.split_once(',') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = cin.len();
        let cin: Register = cin.parse().map_err(|r| reg_err(r, idx))?;
        if cin.class != RegisterClass::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::Branch,
                    got: cin.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        check_cluster(dst, cin, idx, val_len)?;
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // Register s1
        let Some((src1, s)) = s.split_once(',') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src1.len();
        let src1: Register = src1.parse().map_err(|r| reg_err(r, idx))?;
        if src1.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src1.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        check_cluster(dst, src1, idx, val_len)?;
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // Register s2
        let mut splitter = s.split_whitespace();
        let Some(src2) = splitter.next() else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src2.len();
        let src2: Register = src2.parse().map_err(|r| reg_err(r, idx))?;
        if src2.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src2.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        check_cluster(dst, src2, idx, val_len)?;
        idx += val_len + 1;
        let s = trim_start(splitter.next().unwrap_or_default(), &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self {
                dst,
                cout,
                cin,
                src1,
                src2,
            })
        }
    }
}

impl Display for CarryArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            cout,
            dst,
            cin,
            src1,
            src2,
        } = self;
        f.write_fmt(format_args!("{dst}, {cout} = {cin}, {src1}, {src2}"))
    }
}

impl Info for CarryArgs {
    type Opcode = CarryOpcode;
    fn decode(&self, opcode: Self::Opcode, machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        match opcode {
            CarryOpcode::AddCarry => {
                let s1 = machine.get_reg(self.src1)?;
                let cin = machine.get_reg(self.cin)? & 0x1;
                let res = s1 + machine.get_reg(self.src2)? + cin;
                let carry = if cin == 1 {
                    if res <= s1 {
                        1u32
                    } else {
                        0u32
                    }
                } else if res < s1 {
                    1u32
                } else {
                    0u32
                };
                // Check destinations
                machine.get_reg(self.dst)?;
                machine.get_reg(self.cout)?;
                Ok(vec![
                    Outcome {
                        dst: Location::Register(self.dst),
                        value: res,
                    },
                    Outcome {
                        dst: Location::Register(self.cout),
                        value: carry,
                    },
                ])
            }
            CarryOpcode::Divide => {
                let s1 = machine.get_reg(self.src1)?;
                let cin = machine.get_reg(self.cin)? & 0x1;
                let tmp = (s1 << 1) | cin;
                let carry = (s1 >> 31) & 0x1;
                let s2 = machine.get_reg(self.src2)?;
                let res = if carry == 1 {
                    tmp.wrapping_add(s2)
                } else {
                    tmp.wrapping_sub(s2)
                };
                // Check destinations
                machine.get_reg(self.dst)?;
                machine.get_reg(self.cout)?;
                Ok(vec![
                    Outcome {
                        dst: Location::Register(self.dst),
                        value: res,
                    },
                    Outcome {
                        dst: Location::Register(self.cout),
                        value: carry,
                    },
                ])
            }
        }
    }
    fn inputs(&self) -> Vec<Location> {
        vec![
            Location::Register(self.cin),
            Location::Register(self.src1),
            Location::Register(self.src2),
        ]
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst), Location::Register(self.cout)]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SubArgs {
    pub(super) src1: Operand,
    pub(super) src2: Register,
    pub(super) dst: Register,
}

impl FromStr for SubArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the destination register
        let Some((dst, s)) = s.split_once('=') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = dst.len();
        let dst: Register = dst.parse().map_err(|r| reg_err(r, idx))?;
        if dst.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: dst.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        // We're past the =, trim and get the first operand (either register or immediate)
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        let Some((src1, s)) = s.split_once(',') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src1.len();
        let src1: Operand = src1.parse().map_err(|op: OperandParseError| WithContext {
            source: ParseError::BadOperand(src1.to_owned(), op),
            ctx: (idx, val_len).into(),
            help: None,
        })?;
        if let Operand::Register(r) = src1 {
            if r.class != RegisterClass::General {
                return Err(WithContext {
                    source: ParseError::WrongRegisterClass {
                        wanted: RegisterClass::General,
                        got: r.class,
                    },
                    ctx: (idx, 0).into(),
                    help: None,
                });
            }
            check_cluster(dst, r, idx, val_len)?;
        }
        idx += val_len + 1;
        // We're past the first operand. At this point it better be a register
        let mut splitter = s.split_whitespace();
        let Some(src2) = splitter.next() else {
            return Err(WithContext {
                source: ParseError::NoValue,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src2.len();
        let src2: Register = src2.parse().map_err(|r| reg_err(r, idx))?;
        if src2.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src2.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        check_cluster(dst, src2, idx, val_len)?;
        idx += val_len + 1;
        let s = trim_start(splitter.next().unwrap_or_default(), &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { src1, src2, dst })
        }
    }
}

impl Info for SubArgs {
    type Opcode = ();
    fn inputs(&self) -> Vec<Location> {
        match self.src1 {
            Operand::Immediate(_) => vec![Location::Register(self.src2)],
            Operand::Register(r) => {
                vec![Location::Register(r), Location::Register(self.src2)]
            }
        }
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn decode(&self, _opcode: (), machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        // Make sure dst works
        machine.get_reg(self.dst)?;
        let dst = Location::Register(self.dst);
        let value = self
            .src1
            .resolve(machine)?
            .wrapping_sub(machine.get_reg(self.src2)?);
        Ok(vec![Outcome { value, dst }])
    }
}

impl Display for SubArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { dst, src1, src2 } = self;
        f.write_fmt(format_args!("{dst} = {src1}, {src2}"))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExtendOpcode {
    Byte,
    Half,
    ZeroByte,
    ZeroHalf,
}

impl ExtendOpcode {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Byte => "sxtb",
            Self::Half => "sxth",
            Self::ZeroByte => "zxtb",
            Self::ZeroHalf => "zxth",
        }
    }
}

impl Display for ExtendOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

impl FromStr for ExtendOpcode {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "sxtb" => Self::Byte,
            "sxth" => Self::Half,
            "zxtb" => Self::ZeroByte,
            "zxth" => Self::ZeroHalf,
            _ => return Err(()),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExtendArgs {
    src: Register,
    dst: Register,
}

impl FromStr for ExtendArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the destination register
        let Some((dst, s)) = s.split_once('=') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = dst.len();
        let dst: Register = dst.parse().map_err(|r| reg_err(r, idx))?;
        if dst.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: dst.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        // We're past the =, trim and get the first register
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        let mut splitter = s.split_whitespace();
        let Some(src) = splitter.next() else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src.len();
        let src: Register = src.parse().map_err(|r| reg_err(r, idx))?;
        if src.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        check_cluster(dst, src, idx, val_len)?;
        idx += val_len + 1;
        let s = trim_start(splitter.next().unwrap_or_default(), &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { src, dst })
        }
    }
}

impl Display for ExtendArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { src, dst } = self;
        f.write_fmt(format_args!("{dst} = {src}"))
    }
}

impl Info for ExtendArgs {
    type Opcode = ExtendOpcode;
    fn inputs(&self) -> Vec<Location> {
        vec![Location::Register(self.src)]
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn decode(&self, opcode: Self::Opcode, machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        let src = machine.get_reg(self.src)?;
        let value = match opcode {
            ExtendOpcode::ZeroByte => src & 0xff,
            ExtendOpcode::ZeroHalf => src & 0xffff,
            ExtendOpcode::Byte => (((src << 24) as i32) >> 24) as u32,
            ExtendOpcode::Half => (((src << 16) as i32) >> 16) as u32,
        };
        let dst = Location::Register(self.dst);
        // Check the destination
        machine.get_reg(self.dst)?;
        Ok(vec![Outcome { dst, value }])
    }
}

#[cfg(test)]
mod test {
    use super::{
        super::test::{display, negative, positive},
        BasicArgs, BasicOpcode, CarryArgs, ExtendArgs,
    };
    use crate::{
        machine::test::test_machine,
        operation::{arithmetic::SubArgs, Info, Location, Operand, Register, RegisterClass},
        Outcome,
    };
    #[test]
    fn basic_parser() {
        positive(&[
            (
                "$r0.2 = $r0.3, $r0.4",
                BasicArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    src1: Register {
                        cluster: 0,
                        num: 3,
                        class: RegisterClass::General,
                    },
                    src2: Operand::Register(Register {
                        cluster: 0,
                        num: 4,
                        class: RegisterClass::General,
                    }),
                },
            ),
            (
                "$r0.2 = $r0.3,5",
                BasicArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    src1: Register {
                        cluster: 0,
                        num: 3,
                        class: RegisterClass::General,
                    },
                    src2: Operand::Immediate(5),
                },
            ),
            (
                "$r0.2 =$r0.3, 0x20 ",
                BasicArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    src1: Register {
                        cluster: 0,
                        num: 3,
                        class: RegisterClass::General,
                    },
                    src2: Operand::Immediate(0x20),
                },
            ),
        ]);

        negative::<BasicArgs, _>(&[
            "$r0.2 = $r0.3, $r0.4 f",
            "$r0.-2 = $r0.3, $r0.4",
            "$r0.2 = $r0.3, r0.4",
            "$r0.2 = $r1.3, $r0.4",
            "$b0.2 = $r0.3, $r0.4",
            "$r0.2 = $r0.3, 0x2g2",
            "$r0.2 = $r0.3, 123f",
            "$r0.2 = 0x1, 0x1",
            "$r0.2 = 0x1",
            "= $r0.3, $r0.4",
        ]);
    }

    #[test]
    fn basic_display() {
        display(&[
            (
                "$r0.1 = $r0.4, $r0.2",
                BasicArgs {
                    src1: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 4,
                    },
                    src2: Operand::Register(Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    }),
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                },
            ),
            (
                "$r0.1 = $r0.4, 0x20",
                BasicArgs {
                    src1: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 4,
                    },
                    src2: Operand::Immediate(0x20),
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                },
            ),
        ]);
    }

    #[test]
    fn basic_decode() {
        let mut machine = test_machine();
        let args = BasicArgs {
            src1: Register {
                cluster: 0,
                class: RegisterClass::General,
                num: 4,
            },
            src2: Operand::Immediate(0x20),
            dst: Register {
                cluster: 0,
                class: RegisterClass::General,
                num: 1,
            },
        };
        machine[args.src1] = 0xff;
        let res = args.decode(BasicOpcode::Or, &machine);
        assert!(res.is_ok());
        assert_eq!(
            vec![Outcome {
                dst: Location::Register(args.dst),
                value: 0xff
            }],
            res.unwrap()
        );
    }

    #[test]
    fn sub_parser() {
        positive(&[
            (
                "$r0.2 = $r0.0, $r0.1",
                SubArgs {
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    },
                    src1: Operand::Register(Register {
                        cluster: 0,
                        num: 0,
                        class: RegisterClass::General,
                    }),
                    src2: Register {
                        cluster: 0,
                        num: 1,
                        class: RegisterClass::General,
                    },
                },
            ),
            (
                "$r0.2 = 5  , $r0.1",
                SubArgs {
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    },
                    src1: Operand::Immediate(5),
                    src2: Register {
                        cluster: 0,
                        num: 1,
                        class: RegisterClass::General,
                    },
                },
            ),
        ]);
        negative::<SubArgs, _>(&[
            "$r0.2 = $r0.3, $r0.4 f",
            "$r0.-2 = $r0.3, $r0.4",
            "$r0.2 = $r0.3, r0.4",
            "$r0.2 = $r1.3, $r0.4",
            "$b0.2 = $r0.3, $r0.4",
            "$r0.2 = $r0.3, 0x22",
            "$r0.2 = 123f, $r0.3",
            "$r0.2 = 0x1, 0x1",
            "$r0.2 = 0x1",
            "= $r0.3, $r0.4",
        ]);
    }

    #[test]
    fn sub_display() {
        display(&[
            (
                "$r0.1 = $r0.4, $r0.2",
                SubArgs {
                    src2: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    },
                    src1: Operand::Register(Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 4,
                    }),
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                },
            ),
            (
                "$r0.1 = 0x20, $r0.4",
                SubArgs {
                    src2: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 4,
                    },
                    src1: Operand::Immediate(0x20),
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                },
            ),
        ]);
    }

    #[test]
    fn sub_decode() {
        let mut machine = test_machine();
        let args = SubArgs {
            src2: Register {
                cluster: 0,
                class: RegisterClass::General,
                num: 4,
            },
            src1: Operand::Immediate(0x20),
            dst: Register {
                cluster: 0,
                class: RegisterClass::General,
                num: 1,
            },
        };

        machine[args.src2] = 0x01;

        let res = args.decode((), &machine);
        assert!(res.is_ok());
        assert_eq!(
            vec![Outcome {
                dst: Location::Register(args.dst),
                value: 0x20 - 0x01,
            }],
            res.unwrap()
        );
    }

    #[test]
    fn carry_parser() {
        positive(&[
            (
                "   $r0.1, $b0.1 = $b0.2, $r0.2,    $r0.3         ",
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
            (
                "$r0.1,$b0.1=$b0.2,$r0.2,$r0.3",
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
        ]);

        negative::<CarryArgs, _>(&[
            "$r0.1,$b0.1=$b0.2,$r0.2$r0.3",
            "$r0.1$b0.1=$b0.2,$r0.2,$r0.3",
            "$r0.1,    $ b0.1=$b0.2,$r0.2,$r0.3",
            "$r0.1,$b0.1=$b0.2$r0.2,$r0.3",
            "$r0.1,$b0.1=$b0.2 $r0.2,$r0.3",
            "$r0.1 $b0.1=$b0.2,$r0.2,$r0.3",
            "$r0.1,$b0.1=$b0.2,$l0.2,$r0.3",
            "$r0.1,$b0.1=$b0.2,$r0.2,$l0.3",
            "$r0.1,$r0.1=$b0.2,$r0.2,$r0.3",
            "$r0.1,$b0.1=$l0.2,$r0.2,$r0.3",
            "$l0.0,$b0.1=$b0.2,$r0.2,$r0.3",
        ]);
    }

    #[test]
    fn carry_display() {
        display(&[
            (
                "$r0.1, $b0.1 = $b0.2, $r0.2, $r0.3",
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
            (
                "$r0.1, $b0.18 = $b0.2, $r0.2, $r0.3",
                CarryArgs {
                    cout: Register {
                        cluster: 0,
                        num: 18,
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
        ]);
    }

    #[test]
    fn extend_parser() {
        positive(&[
            (
                "$r0.2 = $r0.3   ",
                ExtendArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    src: Register {
                        cluster: 0,
                        num: 3,
                        class: RegisterClass::General,
                    },
                },
            ),
            (
                "$r0.2=$r0.3",
                ExtendArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    src: Register {
                        cluster: 0,
                        num: 3,
                        class: RegisterClass::General,
                    },
                },
            ),
        ]);

        negative::<ExtendArgs, _>(&[
            "$r0.2 = $r0.3 f",
            "$r0.-2 = $r0.3",
            "$r0.2 = r0.3",
            "$r0.2 = $r1.3",
            "$b0.2 = $r0.3",
            "$r0.2 = 0x1",
            "$r0.2",
            "= $r0.3",
        ]);
    }
}
