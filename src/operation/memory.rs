use std::{fmt::Display, str::FromStr};

use crate::{operation::Alignment, Location, Machine, Outcome};

use super::{
    parse_num, reg_err, trim_start, DecodeError, Info, ParseError, Register, RegisterParseError,
    RegisterType, WithContext,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
pub enum LoadOpcode {
    Word,
    HalfWordSigned,
    HalfWordUnsigned,
    ByteSigned,
    ByteUnsigned,
}

impl From<LoadOpcode> for Alignment {
    fn from(value: LoadOpcode) -> Self {
        match value {
            LoadOpcode::ByteSigned | LoadOpcode::ByteUnsigned => Self::Byte,
            LoadOpcode::HalfWordSigned | LoadOpcode::HalfWordUnsigned => Self::Half,
            LoadOpcode::Word => Self::Word,
        }
    }
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
    pub(crate) base: Register,
    pub(crate) offset: u32,
    pub(crate) dst: Register,
}

impl FromStr for LoadArgs {
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
        // We're past the =, trim and get the offset
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        let Some((offset, s)) = s.split_once('[') else {
            return Err(WithContext {
                source: ParseError::NoOffset,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = offset.len();
        let offset = parse_num(offset).map_err(|e| WithContext {
            source: ParseError::BadOffset(e),
            ctx: (idx, val_len).into(),
            help: None,
        })?;
        idx += val_len + 1;
        let s = trim_start(s, &mut idx);
        // We're now at the [reg]. get to the next ]
        let Some((base, s)) = s.split_once(']') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = base.len();
        let base: Register =
            base.parse()
                .map_err(|e: WithContext<RegisterParseError>| WithContext {
                    source: ParseError::BadRegister(e.source),
                    ctx: e.span_context(idx),
                    help: None,
                })?;
        idx += val_len + 1;
        if base.class != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: base.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        let s = trim_start(s, &mut idx);
        if !s.is_empty() {
            Err(WithContext {
                source: ParseError::ExpectedEnd(s.to_owned()),
                ctx: (idx, s.len()).into(),
                help: None,
            })
        } else {
            Ok(Self { base, offset, dst })
        }
    }
}

impl Info for LoadArgs {
    type Opcode = LoadOpcode;
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Register(self.dst)]
    }
    fn inputs(&self) -> Vec<Location> {
        vec![
            Location::Register(self.base),
            Location::Memory(0, Alignment::default()),
        ]
    }
    fn decode(&self, opcode: LoadOpcode, machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        let addr = (machine.get_reg(self.base)? + self.offset) as usize;
        let value = machine.read_memory(addr, opcode.into())?.as_u32();
        // Make sure destination register works
        machine.get_reg(self.dst)?;
        Ok(vec![Outcome {
            dst: Location::Register(self.dst),
            value,
        }])
    }
}

impl Display for LoadArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{} = 0x{:02x}[{}]",
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
    pub const fn alignment(self) -> Alignment {
        match self {
            Self::Word => Alignment::Word,
            Self::HalfWord => Alignment::Half,
            Self::Byte => Alignment::Byte,
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
    pub(crate) base: Register,
    pub(crate) offset: u32,
    pub(crate) src: Register,
}

impl FromStr for StoreArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut idx = 0;
        let s = trim_start(s, &mut idx);
        // Chomp the offset
        let Some((offset, s)) = s.split_once('[') else {
            return Err(WithContext {
                source: ParseError::NoOffset,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = offset.len();
        let offset = parse_num(offset).map_err(|e| WithContext {
            source: ParseError::BadOffset(e),
            ctx: (idx, val_len).into(),
            help: None,
        })?;
        idx += val_len + 1;
        // Chomp the base register
        let s = trim_start(s, &mut idx);
        let Some((base, s)) = s.split_once(']') else {
            return Err(WithContext {
                source: ParseError::NoRegister,
                ctx: (idx, 0).into(),
                help: None,
            });
        };
        let val_len = base.len();
        let base: Register =
            base.parse()
                .map_err(|e: WithContext<RegisterParseError>| WithContext {
                    source: ParseError::BadRegister(e.source),
                    ctx: e.span_context(idx),
                    help: None,
                })?;
        if base.class != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: base.class,
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        idx += val_len + 1;
        // Chomp the source register
        let s = trim_start(s, &mut idx);
        if !s.starts_with('=') {
            return Err(WithContext {
                source: ParseError::UnexpectedCharacter {
                    wanted: '=',
                    got: super::UnexpectedValue(s.chars().next()),
                },
                ctx: (idx, 0).into(),
                help: None,
            });
        }
        let s = &s[1..];
        idx += 1;
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
        if src.class != RegisterType::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterType {
                    wanted: RegisterType::General,
                    got: src.class,
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
            Ok(Self { base, offset, src })
        }
    }
}

impl Info for StoreArgs {
    type Opcode = StoreOpcode;
    fn inputs(&self) -> Vec<Location> {
        vec![Location::Register(self.base), Location::Register(self.src)]
    }
    fn outputs(&self) -> Vec<Location> {
        vec![Location::Memory(0, Alignment::default())]
    }
    fn decode(&self, opcode: StoreOpcode, machine: &Machine) -> Result<Vec<Outcome>, DecodeError> {
        let addr = (machine.get_reg(self.base)? + self.offset) as usize;
        let value = machine.get_reg(self.src)?;
        // Make sure the destination address works
        machine.read_memory(addr, opcode.alignment())?;
        Ok(vec![Outcome {
            value,
            dst: Location::Memory(addr, opcode.alignment()),
        }])
    }
}

impl Display for StoreArgs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { offset, base, src } = self;
        f.write_fmt(format_args!("0x{offset:02x}[{base}] = {src}"))
    }
}

#[cfg(test)]
mod test {

    use crate::operation::{Register, RegisterType};

    use super::{LoadArgs, StoreArgs};

    use super::super::test::{display, negative, positive};

    #[test]
    fn load_parser() {
        positive(&[
            (
                " $r0.4 = 0x20 [ $r0.1]",
                LoadArgs {
                    base: Register {
                        num: 1,
                        class: RegisterType::General,
                    },
                    offset: 0x20,
                    dst: Register {
                        num: 4,
                        class: RegisterType::General,
                    },
                },
            ),
            (
                "$r0.4=5[$r0.1]",
                LoadArgs {
                    base: Register {
                        num: 1,
                        class: RegisterType::General,
                    },
                    offset: 5,
                    dst: Register {
                        num: 4,
                        class: RegisterType::General,
                    },
                },
            ),
            (
                "        $r0.4       = 5     [$r0.1]    ",
                LoadArgs {
                    base: Register {
                        num: 1,
                        class: RegisterType::General,
                    },
                    offset: 5,
                    dst: Register {
                        num: 4,
                        class: RegisterType::General,
                    },
                },
            ),
        ]);

        negative::<LoadArgs, _>(&[
            "$r0.2 = 0x24[$r0.1]  f",
            "$r0.-1 =' 0x24[$r0.1]",
            "$r0.2 = 0xg24[$r0.1]",
            "$r0.2 = 0x24[r0.1]",
            "$r0.2 = 0x24[$b0.1]",
            "$r0.2 = [$r0.1]",
            "$r0.2 = 0x24[]",
            "= 0x24[$r0.1]",
        ]);
    }

    #[test]
    fn load_display() {
        display(&[
            (
                "$r0.2 = 0x24[$r0.1]",
                LoadArgs {
                    base: Register {
                        class: RegisterType::General,
                        num: 1,
                    },
                    dst: Register {
                        class: RegisterType::General,
                        num: 2,
                    },
                    offset: 0x24,
                },
            ),
            (
                "$r0.2 = 0x01[$r0.1]",
                LoadArgs {
                    base: Register {
                        class: RegisterType::General,
                        num: 1,
                    },
                    dst: Register {
                        class: RegisterType::General,
                        num: 2,
                    },
                    offset: 0x1,
                },
            ),
        ])
    }

    #[test]
    fn store_parser() {
        positive(&[
            (
                "0x20[$r0.1]=$r0.4",
                StoreArgs {
                    base: Register {
                        num: 1,
                        class: RegisterType::General,
                    },
                    offset: 0x20,
                    src: Register {
                        num: 4,
                        class: RegisterType::General,
                    },
                },
            ),
            (
                "   5      [ $r0.1      ]    =        $r0.4   ",
                StoreArgs {
                    base: Register {
                        num: 1,
                        class: RegisterType::General,
                    },
                    offset: 5,
                    src: Register {
                        num: 4,
                        class: RegisterType::General,
                    },
                },
            ),
        ]);

        negative::<StoreArgs, _>(&[
            "0x24[$r0.1] = $r0.2  f",
            "0xg24[$r0.1] = $r0.2",
            "0x24[r0.1] =' $r0.2",
            "0x24[$b0.1] = $r0.2",
            "[$r0.1] = $r0.2",
            "0x24[] = $r0.2",
            "0x24[$r0.1] =",
        ]);
    }

    #[test]
    fn store_display() {
        display(&[
            (
                "0x01[$r0.1] = $r0.2",
                StoreArgs {
                    base: Register {
                        class: RegisterType::General,
                        num: 1,
                    },
                    src: Register {
                        class: RegisterType::General,
                        num: 2,
                    },
                    offset: 1,
                },
            ),
            (
                "0x24[$r0.1] = $r0.2",
                StoreArgs {
                    base: Register {
                        class: RegisterType::General,
                        num: 1,
                    },
                    src: Register {
                        class: RegisterType::General,
                        num: 2,
                    },
                    offset: 0x24,
                },
            ),
        ])
    }
}
