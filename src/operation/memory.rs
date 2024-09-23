use std::{fmt::Display, str::FromStr};

use crate::{Location, Machine, Outcome};

use super::{
    parse_num, trim_start, ParseError, Register, RegisterParseError, RegisterType, WithContext,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
pub enum LoadOpcode {
    Word,
    HalfWordSigned,
    HalfWordUnsigned,
    ByteSigned,
    ByteUnsigned,
}

impl LoadOpcode {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Word => "ldw",
            Self::HalfWordSigned => "ldh",
            Self::HalfWordUnsigned => "ldhu",
            Self::ByteSigned => "ldb",
            Self::ByteUnsigned => "ldbu",
        }
    }
}

impl FromStr for LoadOpcode {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "ldw" => Self::Word,
            "ldh" => Self::HalfWordSigned,
            "ldhu" => Self::HalfWordUnsigned,
            "ldb" => Self::ByteSigned,
            "ldbu" => Self::ByteUnsigned,
            _ => return Err(()),
        })
    }
}

impl Display for LoadOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoadArgs {
    base: Register,
    offset: u32,
    dst: Register,
}

impl FromStr for LoadArgs {
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
        // We're past the =, trim and get the offset
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        if s.starts_with('[') {
            return Err(WithContext {
                source: ParseError::NoOffset,
                span: (idx, 0).into(),
                help: None,
            });
        }
        let Some((offset, s)) = s.split_once('[') else {
            return Err(WithContext {
                source: ParseError::NoOffset,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = offset.len();
        let offset = parse_num(offset).map_err(|e| WithContext {
            source: ParseError::BadOffset(e),
            span: (idx, val_len).into(),
            help: None,
        })?;
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // We're now at the [reg]. get to the next ]
        if s.starts_with(']') {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        }
        let Some((base, s)) = s.split_once(']') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = base.len();
        let base = base
            .parse()
            .map_err(|e: WithContext<RegisterParseError>| WithContext {
                source: ParseError::BadRegister(e.source),
                span: e.span_context(idx),
                help: None,
            })?;
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                span: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { base, offset, dst })
        }
    }
}

impl LoadArgs {
    pub fn inputs(&self) -> Vec<Location> {
        vec![Location::Register(self.base), Location::Memory(0)]
    }
    pub fn decode(self, opcode: LoadOpcode, machine: &Machine) -> Outcome {
        let addr = (machine[self.base] + self.offset) as usize;
        let value = u32::from_ne_bytes(machine.mem[addr..addr + 4].try_into().unwrap());
        let value = match opcode {
            LoadOpcode::Word => value,
            LoadOpcode::HalfWordSigned | LoadOpcode::HalfWordUnsigned => value & 0xffff,
            LoadOpcode::ByteSigned | LoadOpcode::ByteUnsigned => value & 0xff,
        };
        Outcome {
            dst: Location::Register(self.dst),
            value,
        }
    }
}

impl Display for LoadArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "$r0.{} = 0x{:x}[$r0.{}]",
            self.dst, self.offset, self.base
        ))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
pub enum StoreOpcode {
    Word,
    HalfWord,
    Byte,
}

impl StoreOpcode {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Word => "stw",
            Self::HalfWord => "sth",
            Self::Byte => "stb",
        }
    }
}

impl FromStr for StoreOpcode {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "stw" => Self::Word,
            "sth" => Self::HalfWord,
            "stb" => Self::Byte,
            _ => return Err(()),
        })
    }
}

impl Display for StoreOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StoreArgs {
    base: Register,
    offset: u32,
    src: Register,
}

impl FromStr for StoreArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the offset
        if s.starts_with('[') {
            return Err(WithContext {
                source: ParseError::NoOffset,
                span: (idx, 0).into(),
                help: None,
            });
        }
        let Some((offset, s)) = s.split_once('[') else {
            return Err(WithContext {
                source: ParseError::NoOffset,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = offset.len();
        let offset = parse_num(offset).map_err(|e| WithContext {
            source: ParseError::BadOffset(e),
            span: (idx, val_len).into(),
            help: None,
        })?;
        idx += val_len + 1;
        // Chomp the base register
        let s = trim_start(s, &mut idx);
        if s.starts_with(']') {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        }
        let Some((base, _)) = s.split_once(']') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = base.len();
        let base = base
            .parse()
            .map_err(|e: WithContext<RegisterParseError>| WithContext {
                source: ParseError::BadRegister(e.source),
                span: e.span_context(idx),
                help: None,
            })?;
        idx += val_len + 1;
        // Chomp the source register
        let s = trim_start(s, &mut idx);
        if !s.starts_with('=') {
            return Err(WithContext {
                source: ParseError::UnexpectedCharacter {
                    wanted: '=',
                    got: super::UnexpectedValue(s.chars().next()),
                },
                span: (idx, 0).into(),
                help: None,
            });
        }
        let s = &s[1..];
        idx += 1;
        let s = trim_start(s, &mut idx);
        let Some(src) = s.split_whitespace().next() else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                span: (idx, 0).into(),
                help: None,
            });
        };

        let val_len = src.len();
        let src: Register =
            src.parse()
                .map_err(|r: WithContext<RegisterParseError>| WithContext {
                    source: r.source.into(),
                    span: r.span_context(idx),
                    help: None,
                })?;
        if src.bank != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: src.bank,
                },
                span: (idx, 0).into(),
                help: None,
            });
        }
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                span: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { base, offset, src })
        }
    }
}

impl StoreArgs {
    pub fn inputs(&self) -> Vec<Location> {
        vec![Location::Register(self.base), Location::Register(self.src)]
    }
    pub fn decode(&self, _opcode: StoreOpcode, machine: &Machine) -> Outcome {
        let addr = (machine[self.base] + self.offset) as usize;
        Outcome {
            dst: Location::Memory(addr),
            value: machine[self.src],
        }
    }
}

impl Display for StoreArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "0x{:x}[$r0.{}] = $r0.{}",
            self.offset, self.base, self.src
        ))
    }
}

#[cfg(test)]
mod test {

    use super::super::{ParseError, RegisterParseError};
    use super::LoadArgs;

    #[test]
    fn load_parse_errors() {
        let inst = " $r1.2 = 0x24[$r0.1] ## restore ## t16";
        let e = inst.parse::<LoadArgs>().unwrap_err();
        assert_eq!(3, e.span.offset());
        assert!(matches!(
            e.source,
            ParseError::BadRegister(RegisterParseError::Cluster)
        ));
    }
}
