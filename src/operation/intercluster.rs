//! Operations for moving values between clusters
//!
//! Typically, an operation will require that all of its registers reside within
//! the same cluster. The commands implemented here facilitate the movement of
//! values into the right registers.
//!
//! Moving a value is accomplished by a pair of `SEND` and `RECV` commands that
//! use the same `path`. For example:
//!
//! ``` plain
//! SEND $r1.2, 0x1234
//! RECV $r0.2 = 0x1234
//! ```
//!
//! Will send the value in `$r1.2` into register `$r0.2`.
use std::{fmt::Display, str::FromStr};

use crate::{
    machine::Machine,
    operation::{Location, Outcome},
};

use super::{
    help, DecodeError, Info, ParseError, ParseState, Register, RegisterClass, WithContext,
};

/// Arguments for the `mov` instruction, which moves a
/// defined [constant](`MoveArgs::payload`)'s address into a register
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MoveArgs {
    /// The destination register
    pub(super) dst: Register,
    /// The "payload"
    pub(super) payload: String,
}

impl FromStr for MoveArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = ParseState::new(s);
        // Chomp the destination register
        let (dst, ctx) = s.chomp_register('=')?;
        if dst.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: dst.class,
                },
                ctx,
                help: None,
            });
        }

        // Just... look inside parenthesis?
        s.trim_start();
        s.expect('(').map_err(|e| WithContext {
            help: Some(help::BAD_PAYLOAD),
            ..e
        })?;
        let ParseState { s, mut idx } = s;
        let Some((payload, s)) = s.split_once(')') else {
            return Err(WithContext {
                source: ParseError::Unexpected {
                    wanted: ')'.into(),
                    got: s.chars().next().into(),
                },
                ctx: (idx + s.len()).into(),
                help: Some(help::BAD_PAYLOAD),
            });
        };
        let payload = payload.to_owned();
        idx += payload.len();
        // Finish up parsing
        ParseState { s, idx }.finish()?;
        Ok(Self { dst, payload })
    }
}

impl Display for MoveArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { dst, payload } = self;
        f.write_fmt(format_args!("{dst} = ({payload})"))
    }
}

impl Info for MoveArgs {
    type Opcode = ();
    fn inputs(&self) -> Vec<Location> {
        Vec::new()
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn decode(
        &self,
        _opcode: Self::Opcode,
        machine: &Machine,
    ) -> Result<Vec<Outcome>, super::DecodeError> {
        machine.get_reg(self.dst)?;
        Ok(Vec::new())
    }
}

/// Arguments necessary to send a value to another cluster
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SendArgs {
    /// The source register
    src: Register,
    /// The path identifier
    path: u32,
}

impl FromStr for SendArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = ParseState::new(s);
        // Chomp the source register (Literally nothing is off limits here)
        let (src, _) = s.chomp_register(',')?;
        // Now it should be some space and an immediate
        let (path, _) = s.chomp_imm(' ')?;
        s.finish()?;
        Ok(Self { src, path })
    }
}

impl Display for SendArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { src, path } = self;
        f.write_fmt(format_args!("{src}, 0x{path:02x}"))
    }
}

impl Info for SendArgs {
    type Opcode = ();
    fn inputs(&self) -> Vec<Location> {
        vec![Location::Register(self.src)]
    }
    fn outputs(&self) -> Vec<Location> {
        Vec::new()
    }
    fn decode(
        &self,
        _opcode: Self::Opcode,
        machine: &Machine,
    ) -> Result<Vec<Outcome>, DecodeError> {
        machine.get_reg(self.src)?;
        Ok(Vec::new())
    }
}

/// Arguments necessary for receiving a value
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecvArgs {
    /// The destination register
    dst: Register,
    /// The path identifier
    path: u32,
}

impl FromStr for RecvArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = ParseState::new(s);
        // Chomp the dst register
        let (dst, _) = s.chomp_register('=')?;
        let (path, _) = s.chomp_imm(' ')?;
        s.finish()?;
        Ok(Self { dst, path })
    }
}

impl Display for RecvArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { dst, path } = self;
        f.write_fmt(format_args!("{dst} = 0x{path:02x}"))
    }
}

impl Info for RecvArgs {
    type Opcode = ();
    fn inputs(&self) -> Vec<Location> {
        Vec::new()
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn decode(
        &self,
        _opcode: Self::Opcode,
        machine: &Machine,
    ) -> Result<Vec<Outcome>, DecodeError> {
        // TODO: How do I get the register value from the corresponding SEND?
        machine.get_reg(self.dst)?;
        todo!()
    }
}

#[cfg(test)]
mod test {
    use crate::{
        machine::test::test_machine,
        operation::{Info, Outcome, Register, RegisterClass},
    };

    use super::{
        super::test::{display, negative, positive},
        MoveArgs, RecvArgs, SendArgs,
    };

    #[test]
    fn mov_parser() {
        positive(&[
            (
                "$r0.2 = (PAYLOAD)",
                MoveArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    payload: String::from("PAYLOAD"),
                },
            ),
            (
                "$r0.2 =()",
                MoveArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    payload: String::from(""),
                },
            ),
            (
                "$r1.3 =     (   P A Y L +-=90878654342567 jkj;ljdskfla;jfkld;sjgfa[]O A D )         ",
                MoveArgs {
                    dst: Register {
                        cluster: 1,
                        num: 3,
                        class: RegisterClass::General,
                    },
                    payload: String::from("   P A Y L +-=90878654342567 jkj;ljdskfla;jfkld;sjgfa[]O A D "),
                },
            ),
        ]);

        negative::<MoveArgs, _>(&[
            "$r0.2 = ()()",
            "$r0.2 = (",
            "$r0.2 = )",
            // For now
            "$r0.2 = (())",
            "$r0.2 = $r0.3",
            "$r0.2",
            " = ",
        ]);
    }

    #[test]
    fn mov_display() {
        display(&[(
            "$r0.2 = (PAYLOAD)",
            MoveArgs {
                dst: Register {
                    cluster: 0,
                    class: RegisterClass::General,
                    num: 2,
                },
                payload: String::from("PAYLOAD"),
            },
        )]);
    }

    #[test]
    fn mov_decode() {
        let mut machine = test_machine();
        let args = MoveArgs {
            dst: Register {
                cluster: 0,
                class: RegisterClass::General,
                num: 2,
            },
            payload: String::from("PAYLOAD"),
        };
        let res = args.decode((), &mut machine);
        assert!(res.is_ok());
        assert_eq!(Vec::<Outcome>::new(), res.unwrap());
    }

    #[test]
    fn send_parser() {
        positive(&[
            (
                "$r0.2, 0x1234",
                SendArgs {
                    src: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    path: 0x1234,
                },
            ),
            (
                "      $r0.2,      1234      ",
                SendArgs {
                    src: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    path: 1234,
                },
            ),
        ]);

        negative::<SendArgs, _>(&[
            "$r0.2, ",
            "",
            "$",
            "1234",
            "$r0.2, fdsa",
            "$r0.2, 0x123g",
            "$r0.2, 0x123 g",
        ]);
    }

    #[test]
    fn send_display() {
        display(&[(
            "$r0.2, 0x1234",
            SendArgs {
                src: Register {
                    cluster: 0,
                    class: RegisterClass::General,
                    num: 2,
                },
                path: 0x1234,
            },
        )]);
    }
    #[test]
    fn recv_parser() {
        positive(&[
            (
                "$r0.2 = 0x1234",
                RecvArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    path: 0x1234,
                },
            ),
            (
                "      $r0.2     =      1234      ",
                RecvArgs {
                    dst: Register {
                        cluster: 0,
                        num: 2,
                        class: RegisterClass::General,
                    },
                    path: 1234,
                },
            ),
        ]);

        negative::<RecvArgs, _>(&[
            "$r0.2 = ",
            "",
            "$0.1 = 0x1234",
            "1234",
            "$r0.2 = fdsa",
            "$r0.2 = 0x123g",
            "$r0.2 = 0x123 g",
        ]);
    }

    #[test]
    fn recv_display() {
        display(&[(
            "$r0.2 = 0x1234",
            RecvArgs {
                dst: Register {
                    cluster: 0,
                    class: RegisterClass::General,
                    num: 2,
                },
                path: 0x1234,
            },
        )]);
    }
}
