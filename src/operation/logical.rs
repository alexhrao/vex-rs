//! Logical operations
//!
//! These operations concern things like conditionals and basic
//! logical commands (e.g., `AND`, etc.). Note that this does
//! **not** include functionality for doing something based on
//! these conditionals.
use std::{fmt::Display, str::FromStr};

use super::{
    check_cluster, DecodeError, Info, Location, Machine, Operand, Outcome, ParseError, ParseState,
    Register, RegisterClass, WithContext,
};

/// Codes for comparison operations
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
    /// Textual representation of this command
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
    /// Execute the command with the two sources
    pub fn execute(self, a: u32, b: u32) -> u32 {
        #[allow(clippy::cast_possible_wrap)]
        u32::from(match self {
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
        })
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

/// Arguments for comparison
///
/// Note that on the surface, this appears to be the same
/// as the [basic `Args`](`super::arithmetic::Args`) used for arithmetic.
/// However, those arguments require the destination to be a general-purpose
/// register; for comparisons, that destination can be either general-purpose
/// or branch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompareArgs {
    /// The first source register
    pub(super) src1: Register,
    /// The second source, either a register or a literal
    pub(super) src2: Operand,
    /// Where to put the value
    pub(super) dst: Register,
}

impl FromStr for CompareArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = ParseState::new(s);
        // Chomp the destination register
        let (dst, ctx) = s.chomp_register('=')?;
        if dst.class != RegisterClass::General && dst.class != RegisterClass::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::Branch,
                    got: dst.class,
                },
                ctx,
                help: None,
            });
        }
        // We're past the =, get the first register
        let (src1, ctx) = s.chomp_register(',')?;
        if src1.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src1.class,
                },
                ctx,
                help: None,
            });
        }
        check_cluster(dst, src1, ctx)?;
        // We're past the , this could either be a register or an immediate
        let (src2, ctx) = s.chomp_operand(' ')?;
        if let Operand::Register(r) = src2 {
            if r.class != RegisterClass::General {
                return Err(WithContext {
                    source: ParseError::WrongRegisterClass {
                        wanted: RegisterClass::General,
                        got: r.class,
                    },
                    ctx,
                    help: None,
                });
            }
            check_cluster(dst, r, ctx)?;
        }
        s.finish()?;
        Ok(Self { src1, src2, dst })
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

/// Commands for simple logical operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Opcode {
    /// Perform a logical `NAND`
    NotAnd,
    /// Perform a logical `NOR`
    NotOr,
    /// Perform a logical `OR`
    Or,
    /// Perform a logical `AND`
    And,
}

impl Opcode {
    /// Textual representation of this command
    pub const fn code(self) -> &'static str {
        match self {
            Self::NotAnd => "nandl",
            Self::NotOr => "norl",
            Self::Or => "orl",
            Self::And => "andl",
        }
    }
    /// Execute the command's functionality
    pub fn execute(self, a: u32, b: u32) -> u32 {
        match self {
            Self::NotAnd => u32::from(a == 0 || b == 0),
            Self::NotOr => u32::from(a == 0 && b == 0),
            Self::Or => u32::from(!(a == 0 && b == 0)),
            Self::And => u32::from(a != 0 && b != 0),
        }
    }
}

impl FromStr for Opcode {
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

impl Display for Opcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

/// Arguments for logical operations. No immediates are allowed
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Args {
    /// The first source register
    pub(super) src1: Register,
    /// The second source register
    pub(super) src2: Register,
    /// The destination register
    pub(super) dst: Register,
}

impl FromStr for Args {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = ParseState::new(s);
        // Chomp the destination register
        let (dst, ctx) = s.chomp_register('=')?;
        if dst.class != RegisterClass::General && dst.class != RegisterClass::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::Branch,
                    got: dst.class,
                },
                ctx,
                help: None,
            });
        }
        // We're past the =, get the first register

        let (src1, ctx) = s.chomp_register(',')?;
        if src1.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src1.class,
                },
                ctx,
                help: None,
            });
        }
        check_cluster(dst, src1, ctx)?;
        // We're past the , there's another register
        let (src2, ctx) = s.chomp_register(' ')?;
        if src2.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src2.class,
                },
                ctx,
                help: None,
            });
        }
        check_cluster(dst, src2, ctx)?;
        s.finish()?;
        Ok(Self { src1, src2, dst })
    }
}

impl Info for Args {
    type Opcode = Opcode;
    fn inputs(&self) -> Vec<super::Location> {
        vec![Location::Register(self.src1), Location::Register(self.src2)]
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn decode(&self, opcode: Opcode, machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        // Make sure dst works
        machine.get_reg(self.dst)?;
        let dst = Location::Register(self.dst);
        let value = opcode.execute(machine.get_reg(self.src1)?, machine.get_reg(self.src2)?);
        Ok(vec![Outcome { value, dst }])
    }
}

impl Display for Args {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { dst, src1, src2 } = self;
        f.write_fmt(format_args!("{dst} = {src1}, {src2}"))
    }
}

/// Commands for selecting a value based on a condition
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SelectOpcode {
    /// Select the first choice if the condition is **true**; otherwise the second
    SelectTrue,
    /// Select the first choice if the condition is **false**; otherwise the second
    SelectFalse,
}

impl SelectOpcode {
    /// Textual representation of this command
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

/// Arguments for conditional selection
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SelectArgs {
    /// Condition to use for choosing. If general purpose, it is
    /// considered false (`0x0`) if its value is `0`; otherwise, it
    /// will be considered true (`0x1`)
    pub(super) cond: Register,
    /// The value to choose if the condition is true
    pub(super) src1: Register,
    /// The value to choose if the condition is false
    pub(super) src2: Operand,
    /// The destination register
    pub(super) dst: Register,
}

impl FromStr for SelectArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = ParseState::new(s);
        // Chomp the destination register
        let (dst, ctx) = s.chomp_register('=')?;
        if dst.class != RegisterClass::General && dst.class != RegisterClass::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::Branch,
                    got: dst.class,
                },
                ctx,
                help: None,
            });
        }
        // We're past the =, trim and get the conditional register
        let (cond, ctx) = s.chomp_register(',')?;
        if cond.class != RegisterClass::Branch {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::Branch,
                    got: cond.class,
                },
                ctx,
                help: None,
            });
        }
        check_cluster(dst, cond, ctx)?;
        // We're past the first ,, trim and get the first choice
        let (src1, ctx) = s.chomp_register(',')?;
        if src1.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src1.class,
                },
                ctx,
                help: None,
            });
        }
        check_cluster(dst, src1, ctx)?;
        // We're past the , this could either be a register or an immediate
        let (src2, ctx) = s.chomp_operand(' ')?;
        if let Operand::Register(r) = src2 {
            if r.class != RegisterClass::General {
                return Err(WithContext {
                    source: ParseError::WrongRegisterClass {
                        wanted: RegisterClass::General,
                        got: r.class,
                    },
                    ctx,
                    help: None,
                });
            }
            check_cluster(dst, r, ctx)?;
        }
        s.finish()?;
        Ok(Self {
            cond,
            src1,
            src2,
            dst,
        })
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
                if cond {
                    src2
                } else {
                    src1
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
        Args, CompareArgs, CompareOpcode, Opcode,
    };
    use crate::{
        machine::test::decode,
        operation::{Action, Location, Operand, Outcome, Register, RegisterClass},
    };
    #[test]
    fn compare_parser() {
        positive(&[
            (
                "$r0.2 = $r0.3, $r0.4",
                CompareArgs {
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
                "$b0.2 = $r0.3,5",
                CompareArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::Branch,
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
                "$b0.2 =$r0.3, 0x20 ",
                CompareArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::Branch,
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
                "$b0.1 = $r0.4, 0x20",
                CompareArgs {
                    src1: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 4,
                    },
                    src2: Operand::Immediate(0x20),
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::Branch,
                        num: 1,
                    },
                },
            ),
        ]);
    }

    #[test]
    fn compare_decode() {
        let args = CompareArgs {
            src1: Register {
                cluster: 0,
                class: RegisterClass::General,
                num: 4,
            },
            src2: Operand::Immediate(0x20),
            dst: Register {
                cluster: 0,
                class: RegisterClass::Branch,
                num: 1,
            },
        };
        let action = Action::Compare(CompareOpcode::Equal, args);
        let res = decode(action, |m| {
            m[args.src1] = 0x20;
        });
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
                Args {
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
                    src2: Register {
                        cluster: 0,
                        num: 4,
                        class: RegisterClass::General,
                    },
                },
            ),
            (
                "$b0.2 = $r0.3, $r0.4",
                Args {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::Branch,
                    },
                    src1: Register {
                        cluster: 0,
                        num: 3,
                        class: RegisterClass::General,
                    },
                    src2: Register {
                        cluster: 0,
                        num: 4,
                        class: RegisterClass::General,
                    },
                },
            ),
        ]);

        negative::<Args, _>(&[
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
                Args {
                    src1: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 4,
                    },
                    src2: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    },
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                },
            ),
            (
                "$b0.1 = $r0.4, $r0.2",
                Args {
                    src1: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 4,
                    },
                    src2: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    },
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::Branch,
                        num: 1,
                    },
                },
            ),
        ]);
    }

    #[test]
    fn logical_decode() {
        // let mut machine = test_machine();
        let args = Args {
            src1: Register {
                cluster: 0,
                class: RegisterClass::General,
                num: 4,
            },
            src2: Register {
                cluster: 0,
                class: RegisterClass::General,
                num: 5,
            },
            dst: Register {
                cluster: 0,
                class: RegisterClass::Branch,
                num: 1,
            },
        };
        let action = Action::Logical(Opcode::And, args);
        let res = decode(action, |m| {
            m[args.src1] = 0x1;
            m[args.src2] = 0x1;
        });
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
