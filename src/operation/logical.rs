use std::{fmt::Display, str::FromStr};

use crate::{machine::Machine, Outcome};

use super::{
    reg_err, trim_start, DecodeError, Info, Location, Operand, OperandParseError, ParseError,
    Register, RegisterType, WithContext,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompareOpcode {
    /// Test for equality
    Equal,
    /// Test for inequality
    NotEqual,
    /// Test if the LHS is >= RHS, treating both as **signed**
    GreaterOrEqualSigned,
    /// Test if the LHS is >= RHS, treating both as **unsigned**
    GreaterOrEqualUnsigned,
    /// Test if the LHS is > RHS, treating both as **signed**
    GreaterSigned,
    /// Test if the LHS is > RHS, treating both as **unsigned**
    GreaterUnsigned,
    /// Test if the LHS is <= RHS, treating both as **signed**
    LesserOrEqualSigned,
    /// Test if the LHS is <= RHS, treating both as **unsigned**
    LesserOrEqualUnsigned,
    /// Test if the LHS is < RHS, treating both as **signed**
    LesserSigned,
    /// Test if the LHS is < RHS, treating both as **unsigned**
    LesserUnsigned,
}

impl CompareOpcode {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Equal => "cmpeq",
            Self::NotEqual => "cmpne",
            Self::GreaterSigned => "cmpgt",
            Self::GreaterUnsigned => "cmpgtu",
            Self::GreaterOrEqualSigned => "cmpge",
            Self::GreaterOrEqualUnsigned => "cmpgeu",
            Self::LesserSigned => "cmplt",
            Self::LesserUnsigned => "cmpltu",
            Self::LesserOrEqualSigned => "cmple",
            Self::LesserOrEqualUnsigned => "cmpleu",
        }
    }

    pub fn execute(&self, a: u32, b: u32) -> u32 {
        (match self {
            Self::Equal => a == b,
            Self::NotEqual => a != b,
            Self::GreaterSigned => (a as i32) > (b as i32),
            Self::GreaterUnsigned => a > b,
            Self::GreaterOrEqualSigned => (a as i32) >= (b as i32),
            Self::GreaterOrEqualUnsigned => a >= b,
            Self::LesserSigned => (a as i32) < (b as i32),
            Self::LesserUnsigned => a < b,
            Self::LesserOrEqualSigned => (a as i32) <= (b as i32),
            Self::LesserOrEqualUnsigned => a <= b,
        }) as u32
    }
}

impl FromStr for CompareOpcode {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "cmpeq" => Self::Equal,
            "cmpne" => Self::NotEqual,
            "cmpgt" => Self::GreaterSigned,
            "cmpgtu" => Self::GreaterUnsigned,
            "cmpge" => Self::GreaterOrEqualSigned,
            "cmpgeu" => Self::GreaterOrEqualUnsigned,
            "cmplt" => Self::LesserSigned,
            "cmpltu" => Self::LesserUnsigned,
            "cmple" => Self::LesserOrEqualSigned,
            "cmpleu" => Self::LesserOrEqualUnsigned,
            _ => return Err(()),
        })
    }
}

impl Display for CompareOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompareArgs {
    pub(super) src1: Register,
    pub(super) src2: Operand,
    pub(super) dst: Register,
}

impl FromStr for CompareArgs {
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
        if dst.class != RegisterType::General && dst.class != RegisterType::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::Branch,
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
        if src1.class != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: src1.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
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
            if r.class != RegisterType::General {
                return Err(WithContext {
                    source: ParseError::WrongRegisterType {
                        wanted: RegisterType::General,
                        got: r.class,
                    },
                    ctx: (idx, 0).into(),
                    help: None,
                });
            }
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

impl Info for CompareArgs {
    type Opcode = CompareOpcode;
    fn inputs(&self) -> Vec<super::Location> {
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
    fn decode(
        &self,
        opcode: CompareOpcode,
        machine: &Machine,
    ) -> Result<Vec<Outcome>, DecodeError> {
        // Make sure dst works
        machine.get_reg(self.dst)?;
        let dst = Location::Register(self.dst);
        let value = opcode.execute(machine.get_reg(self.src1)?, self.src2.resolve(machine)?);
        Ok(vec![Outcome { value, dst }])
    }
}

impl Display for CompareArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { dst, src1, src2 } = self;
        f.write_fmt(format_args!("{dst} = {src1}, {src2}"))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicalOpcode {
    /// Perform a logical `NAND`
    NotAnd,
    /// Perform a logical `NOR`
    NotOr,
    /// Perform a logical `OR`
    Or,
    /// Perform a logical `AND`
    And,
}

impl LogicalOpcode {
    pub const fn code(self) -> &'static str {
        match self {
            Self::NotAnd => "nandl",
            Self::NotOr => "norl",
            Self::Or => "orl",
            Self::And => "andl",
        }
    }

    pub fn execute(&self, a: u32, b: u32) -> u32 {
        match self {
            Self::NotAnd => {
                if a == 0 || b == 0 {
                    1
                } else {
                    0
                }
            }
            Self::NotOr => {
                if a == 0 && b == 0 {
                    1
                } else {
                    0
                }
            }
            Self::Or => {
                if a == 0 && b == 0 {
                    0
                } else {
                    1
                }
            }
            Self::And => {
                if a != 0 && b != 0 {
                    1
                } else {
                    0
                }
            }
        }
    }
}

impl FromStr for LogicalOpcode {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "nandl" => Self::NotAnd,
            "norl" => Self::NotOr,
            "or" => Self::Or,
            "andl" => Self::And,
            _ => return Err(()),
        })
    }
}

impl Display for LogicalOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LogicalArgs {
    pub(super) src1: Register,
    pub(super) src2: Register,
    pub(super) dst: Register,
}

impl FromStr for LogicalArgs {
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
        if dst.class != RegisterType::General && dst.class != RegisterType::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::Branch,
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
        if src1.class != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: src1.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // We're past the , this could either be a register or an immediate
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
        if src2.class != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: src2.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
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

impl Info for LogicalArgs {
    type Opcode = LogicalOpcode;
    fn inputs(&self) -> Vec<super::Location> {
        vec![Location::Register(self.src1), Location::Register(self.src2)]
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn decode(
        &self,
        opcode: LogicalOpcode,
        machine: &Machine,
    ) -> Result<Vec<Outcome>, DecodeError> {
        // Make sure dst works
        machine.get_reg(self.dst)?;
        let dst = Location::Register(self.dst);
        let value = opcode.execute(machine.get_reg(self.src1)?, machine.get_reg(self.src2)?);
        Ok(vec![Outcome { value, dst }])
    }
}

impl Display for LogicalArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { dst, src1, src2 } = self;
        f.write_fmt(format_args!("{dst} = {src1}, {src2}"))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SelectOpcode {
    /// Select the first choice if the condition is **true**; otherwise the second
    SelectTrue,
    /// Select the first choice if the condition is **false**; otherwise the second
    SelectFalse,
}

impl SelectOpcode {
    pub const fn code(self) -> &'static str {
        match self {
            Self::SelectTrue => "slct",
            Self::SelectFalse => "slctf",
        }
    }
}

impl FromStr for SelectOpcode {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "slct" => Self::SelectTrue,
            "slctf" => Self::SelectFalse,
            _ => return Err(()),
        })
    }
}

impl Display for SelectOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SelectArgs {
    pub(super) cond: Register,
    pub(super) src1: Register,
    pub(super) src2: Operand,
    pub(super) dst: Register,
}

impl FromStr for SelectArgs {
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
        if dst.class != RegisterType::General && dst.class != RegisterType::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::Branch,
                    got: dst.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        // We're past the =, trim and get the conditional register
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        let Some((cond, s)) = s.split_once(',') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = cond.len();
        let cond: Register = cond.parse().map_err(|r| reg_err(r, idx))?;
        if cond.class != RegisterType::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::Branch,
                    got: cond.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        // We're past the first ,, trim and get the first choice
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
        if src1.class != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: src1.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
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
            if r.class != RegisterType::General {
                return Err(WithContext {
                    source: ParseError::WrongRegisterType {
                        wanted: RegisterType::General,
                        got: r.class,
                    },
                    ctx: (idx, 0).into(),
                    help: None,
                });
            }
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
            Ok(Self {
                cond,
                src1,
                src2,
                dst,
            })
        }
    }
}

impl Info for SelectArgs {
    type Opcode = SelectOpcode;
    fn inputs(&self) -> Vec<super::Location> {
        match self.src2 {
            Operand::Immediate(_) => {
                vec![Location::Register(self.cond), Location::Register(self.src1)]
            }
            Operand::Register(r) => {
                vec![
                    Location::Register(self.cond),
                    Location::Register(self.src1),
                    Location::Register(r),
                ]
            }
        }
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn decode(&self, opcode: SelectOpcode, machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        // Make sure dst works
        machine.get_reg(self.dst)?;
        let dst = Location::Register(self.dst);
        let src1 = machine.get_reg(self.src1)?;
        let src2 = self.src2.resolve(machine)?;
        let cond = machine.get_reg(self.cond)? != 0;
        let value = match opcode {
            SelectOpcode::SelectTrue => {
                if cond {
                    src1
                } else {
                    src2
                }
            }
            SelectOpcode::SelectFalse => {
                if !cond {
                    src1
                } else {
                    src2
                }
            }
        };
        Ok(vec![Outcome { value, dst }])
    }
}

impl Display for SelectArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            dst,
            src1,
            src2,
            cond,
        } = self;
        f.write_fmt(format_args!("{dst} = {cond}, {src1}, {src2}"))
    }
}

#[cfg(test)]
mod test {
    use super::{
        super::test::{display, negative, positive},
        CompareArgs, CompareOpcode, LogicalArgs, LogicalOpcode,
    };
    use crate::{
        machine::test::test_machine,
        operation::{Info, Location, Operand, Register, RegisterType},
        Outcome,
    };
    #[test]
    fn compare_parser() {
        positive(&[
            (
                "$r0.2 = $r0.3, $r0.4",
                CompareArgs {
                    dst: Register {
                        num: 2,
                        class: RegisterType::General,
                    },
                    src1: Register {
                        num: 3,
                        class: RegisterType::General,
                    },
                    src2: Operand::Register(Register {
                        num: 4,
                        class: RegisterType::General,
                    }),
                },
            ),
            (
                "$b0.2 = $r0.3,5",
                CompareArgs {
                    dst: Register {
                        num: 2,
                        class: RegisterType::Branch,
                    },
                    src1: Register {
                        num: 3,
                        class: RegisterType::General,
                    },
                    src2: Operand::Immediate(5),
                },
            ),
            (
                "$b0.2 =$r0.3, 0x20 ",
                CompareArgs {
                    dst: Register {
                        num: 2,
                        class: RegisterType::Branch,
                    },
                    src1: Register {
                        num: 3,
                        class: RegisterType::General,
                    },
                    src2: Operand::Immediate(0x20),
                },
            ),
        ]);

        negative::<CompareArgs, _>(&[
            "$r0.2 = $r0.3, $r0.4 f",
            "$b0.-2 = $r0.3, $r0.4",
            "$r0.2 = $r0.3, r0.4",
            "$r0.2 = $r1.3, $r0.4",
            "$r0.2 = $r0.3, 0x2g2",
            "$r0.2 = $r0.3, 123f",
            "$r0.2 = 0x1, 0x1",
            "$r0.2 = 0x1",
            "= $r0.3, $r0.4",
        ]);
    }

    #[test]
    fn compare_display() {
        display(&[
            (
                "$r0.1 = $r0.4, $r0.2",
                CompareArgs {
                    src1: Register {
                        class: RegisterType::General,
                        num: 4,
                    },
                    src2: Operand::Register(Register {
                        class: RegisterType::General,
                        num: 2,
                    }),
                    dst: Register {
                        class: RegisterType::General,
                        num: 1,
                    },
                },
            ),
            (
                "$b0.1 = $r0.4, 0x20",
                CompareArgs {
                    src1: Register {
                        class: RegisterType::General,
                        num: 4,
                    },
                    src2: Operand::Immediate(0x20),
                    dst: Register {
                        class: RegisterType::Branch,
                        num: 1,
                    },
                },
            ),
        ]);
    }

    #[test]
    fn compare_decode() {
        let mut machine = test_machine();
        let args = CompareArgs {
            src1: Register {
                class: RegisterType::General,
                num: 4,
            },
            src2: Operand::Immediate(0x20),
            dst: Register {
                class: RegisterType::Branch,
                num: 1,
            },
        };
        machine[args.src1] = 0x20;
        let res = args.decode(CompareOpcode::Equal, &machine);
        assert!(res.is_ok());
        assert_eq!(
            vec![Outcome {
                dst: Location::Register(args.dst),
                value: 0x1,
            }],
            res.unwrap()
        );
    }

    #[test]
    fn logical_parser() {
        positive(&[
            (
                "$r0.2 = $r0.3, $r0.4",
                LogicalArgs {
                    dst: Register {
                        num: 2,
                        class: RegisterType::General,
                    },
                    src1: Register {
                        num: 3,
                        class: RegisterType::General,
                    },
                    src2: Register {
                        num: 4,
                        class: RegisterType::General,
                    },
                },
            ),
            (
                "$b0.2 = $r0.3, $r0.4",
                LogicalArgs {
                    dst: Register {
                        num: 2,
                        class: RegisterType::Branch,
                    },
                    src1: Register {
                        num: 3,
                        class: RegisterType::General,
                    },
                    src2: Register {
                        num: 4,
                        class: RegisterType::General,
                    },
                },
            ),
        ]);

        negative::<LogicalArgs, _>(&[
            "$r0.2 = $r0.3, $r0.4 f",
            "$b0.-2 = $r0.3, $r0.4",
            "$r0.2 = $r0.3, r0.4",
            "$r0.2 = $r1.3, $r0.4",
            "$r0.2 = $r0.3, 0x2g2",
            "$r0.2 = $r0.3, 123",
            "$r0.2 = 0x1, 0x1",
            "$r0.2 = 0x1",
            "= $r0.3, $r0.4",
        ]);
    }

    #[test]
    fn logical_display() {
        display(&[
            (
                "$r0.1 = $r0.4, $r0.2",
                LogicalArgs {
                    src1: Register {
                        class: RegisterType::General,
                        num: 4,
                    },
                    src2: Register {
                        class: RegisterType::General,
                        num: 2,
                    },
                    dst: Register {
                        class: RegisterType::General,
                        num: 1,
                    },
                },
            ),
            (
                "$b0.1 = $r0.4, $r0.2",
                LogicalArgs {
                    src1: Register {
                        class: RegisterType::General,
                        num: 4,
                    },
                    src2: Register {
                        class: RegisterType::General,
                        num: 2,
                    },
                    dst: Register {
                        class: RegisterType::Branch,
                        num: 1,
                    },
                },
            ),
        ]);
    }

    #[test]
    fn logical_decode() {
        let mut machine = test_machine();
        let args = LogicalArgs {
            src1: Register {
                class: RegisterType::General,
                num: 4,
            },
            src2: Register {
                class: RegisterType::General,
                num: 5,
            },
            dst: Register {
                class: RegisterType::Branch,
                num: 1,
            },
        };
        machine[args.src1] = 0x1;
        machine[args.src2] = 0x1;
        let res = args.decode(LogicalOpcode::And, &machine);
        assert!(res.is_ok());
        assert_eq!(
            vec![Outcome {
                dst: Location::Register(args.dst),
                value: 0x1,
            }],
            res.unwrap()
        );
    }
}
