use std::{fmt::Display, str::FromStr};

use crate::{machine::Machine, operation::Location};

use super::{
    trim_start, Info, ParseError, Register, RegisterParseError, RegisterType, UnexpectedValue,
    WithContext,
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
        if s.starts_with('=') {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        let Some((dst, s)) = s.split_once('=') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = dst.len();
        let dst: Register =
            dst.parse()
                .map_err(|r: WithContext<RegisterParseError>| WithContext {
                    source: r.source.into(),
                    ctx: r.span_context(idx),
                    help: None,
                })?;
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
                help: Some(String::from(
                    "mov instructions require a payload in parentheses, like (_?STRINGPACKET.1...)",
                )),
            });
        }
        let Some((payload, s)) = s.split_once(')') else {
            return Err(WithContext {
                source: ParseError::UnexpectedCharacter {
                    wanted: ')',
                    got: UnexpectedValue(s.chars().next()),
                },
                ctx: (idx + s.len() - 1, 0).into(),
                help: Some(String::from(
                    "mov instructions require a payload in parentheses, like (_?STRINGPACKET.1...)",
                )),
            });
        };
        // Add back the )
        let payload = format!("{payload})");
        idx += payload.len();
        let s = trim_start(s, &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len() - 1).into(),
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
