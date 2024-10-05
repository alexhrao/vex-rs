use std::{fmt::Display, str::FromStr};

use crate::{machine::Machine, operation::Location, Outcome};

use super::{
    help, parse_num, reg_err, trim_start, DecodeError, Info, ParseError, Register, RegisterType,
    UnexpectedValue, WithContext,
};

/// Arguments for the `mov` instruction
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MoveArgs {
    /// The destination register
    pub(super) dst: Register,
    /// The "payload" (?)
    pub(super) payload: String,
}

impl FromStr for MoveArgs {
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
        if dst.class != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: dst.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }

        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // Just... look inside parenthesis?
        if !s.starts_with('(') {
            return Err(WithContext {
                source: ParseError::UnexpectedCharacter {
                    wanted: '(',
                    got: UnexpectedValue(s.chars().next()),
                },
                ctx: (idx, 0).into(),
                help: Some(help::BAD_PAYLOAD.into()),
            });
        }
        let Some((payload, s)) = s.split_once(')') else {
            return Err(WithContext {
                source: ParseError::UnexpectedCharacter {
                    wanted: ')',
                    got: UnexpectedValue(s.chars().next()),
                },
                ctx: (idx + s.len(), 0).into(),
                help: Some(help::BAD_PAYLOAD.into()),
            });
        };
        // Add back the )
        let payload = format!("{payload})");
        idx += payload.len();
        let s = trim_start(s, &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { dst, payload })
        }
    }
}

impl Display for MoveArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { dst, payload } = self;
        f.write_fmt(format_args!("{dst} = {payload}"))
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
    ) -> Result<Vec<crate::Outcome>, super::DecodeError> {
        machine.get_reg(self.dst)?;
        Ok(Vec::new())
    }
}

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
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the source register
        let Some((src, s)) = s.split_once(',') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = src.len();
        let src = src.parse().map_err(|r| reg_err(r, idx))?;
        // Now it should be some space and an immediate
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        let mut splitter = s.split_whitespace();
        let Some(path) = splitter.next() else {
            return Err(WithContext {
                source: ParseError::NoValue,
                ctx: (idx).into(),
                help: None,
            });
        };
        let val_len = path.len();
        let path = parse_num(path).map_err(|e| WithContext {
            source: ParseError::BadImmediate(e),
            ctx: (idx, val_len).into(),
            help: None,
        })?;
        idx += val_len + 1;
        let s = trim_start(splitter.next().unwrap_or_default(), &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { src, path })
        }
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
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the dst register
        let Some((dst, s)) = s.split_once('=') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = dst.len();
        let dst = dst.parse().map_err(|r| reg_err(r, idx))?;
        // Now it should be some space and an immediate
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        let mut splitter = s.split_whitespace();
        let Some(path) = splitter.next() else {
            return Err(WithContext {
                source: ParseError::NoValue,
                ctx: (idx).into(),
                help: None,
            });
        };
        let val_len = path.len();
        let path = parse_num(path).map_err(|e| WithContext {
            source: ParseError::BadImmediate(e),
            ctx: (idx, val_len).into(),
            help: None,
        })?;
        idx += val_len + 1;
        let s = trim_start(splitter.next().unwrap_or_default(), &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { dst, path })
        }
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
