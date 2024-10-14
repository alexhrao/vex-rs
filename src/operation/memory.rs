//! Memory operations
//!
//! In general, Vex operations must only concern registers. Things like
//! adding numbers or branching can **only** depend on values that already
//! exist in registers.
//!
//! While perhaps toy programs can subsist solely on registers, more
//! complex programs will need to "spill" into memory. Operations in this
//! module facilitate this.
use std::{fmt::Display, str::FromStr};

use crate::machine::Machine;
use crate::operation::{Alignment, Location, Outcome};

use super::{
    check_cluster, DecodeError, Info, ParseError, ParseState, Register, RegisterClass, WithContext,
};

/// Opcodes for operations that load from memory
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
pub enum LoadOpcode {
    /// Load an entire 32-bit word
    Word,
    /// Load a short (16 bits), respecting the signedness
    HalfWordSigned,
    /// Load an unsigned short (16 bits)
    HalfWordUnsigned,
    /// Load a byte (8 bits), respecting the signedness
    ByteSigned,
    /// Load an unsigned byte (8 bits)
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
    /// Generate a textual representation of this opcode
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

/// Arguments for a load operation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LoadArgs {
    /// The "base" register. This provides the base address in memory
    pub(crate) base: Register,
    /// The offset in memory. This is relative to the [`base`](`LoadArgs::base`) register.
    pub(crate) offset: u32,
    /// The destination register; where the value from memory will be stored
    pub(crate) dst: Register,
}

impl FromStr for LoadArgs {
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
        // We're past the =, trim and get the offset
        let (offset, _) = s.chomp_offset()?;
        // We're now at the [reg]. get to the next ]
        let (base, ctx) = s.chomp_register(']')?;
        if base.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: base.class,
                },
                ctx,
                help: None,
            });
        }
        check_cluster(dst, base, ctx)?;
        s.finish()?;
        Ok(Self { base, offset, dst })
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

/// Opcodes for operations that store data in memory
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
pub enum StoreOpcode {
    /// Store an entire 32-bit word
    Word,
    /// Store a 16-bit short
    HalfWord,
    /// Store a single 8-bit byte
    Byte,
}

impl StoreOpcode {
    /// Get a textual representation of this opcode
    pub const fn code(self) -> &'static str {
        match self {
            Self::Word => "stw",
            Self::HalfWord => "sth",
            Self::Byte => "stb",
        }
    }
    /// Get the expected alignment for this operation
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

/// Arguments for operations that store data in memory
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StoreArgs {
    /// The base address in memory
    pub(crate) base: Register,
    /// The offset into memory. This is relative to the [base](`StoreArgs::base`)
    pub(crate) offset: u32,
    /// The data to be stored
    pub(crate) src: Register,
}

impl FromStr for StoreArgs {
    type Err = WithContext<ParseError>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = ParseState::new(s);
        // Chomp the offset
        let (offset, _) = s.chomp_offset()?;
        // Chomp the base register
        let (base, ctx) = s.chomp_register(']')?;
        if base.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: base.class,
                },
                ctx,
                help: None,
            });
        }
        s.trim_start();
        s.expect('=')?;
        s.trim_start();
        let (src, ctx) = s.chomp_register(' ')?;
        if src.class != RegisterClass::General {
            return Err(WithContext {
                source: ParseError::WrongRegisterClass {
                    wanted: RegisterClass::General,
                    got: src.class,
                },
                ctx,
                help: None,
            });
        }
        check_cluster(base, src, ctx)?;
        s.finish()?;
        Ok(Self { base, offset, src })
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

    use crate::operation::{Register, RegisterClass};

    use super::{LoadArgs, StoreArgs};

    use super::super::test::{display, negative, positive};

    #[test]
    fn load_parser() {
        positive(&[
            (
                " $r0.4 = 0x20 [ $r0.1]",
                LoadArgs {
                    base: Register {
                        cluster: 0,
                        num: 1,
                        class: RegisterClass::General,
                    },
                    offset: 0x20,
                    dst: Register {
                        cluster: 0,
                        num: 4,
                        class: RegisterClass::General,
                    },
                },
            ),
            (
                "$r0.4=5[$r0.1]",
                LoadArgs {
                    base: Register {
                        cluster: 0,
                        num: 1,
                        class: RegisterClass::General,
                    },
                    offset: 5,
                    dst: Register {
                        cluster: 0,
                        num: 4,
                        class: RegisterClass::General,
                    },
                },
            ),
            (
                "        $r0.4       = 5     [   $r0.1        ]    ",
                LoadArgs {
                    base: Register {
                        cluster: 0,
                        num: 1,
                        class: RegisterClass::General,
                    },
                    offset: 5,
                    dst: Register {
                        cluster: 0,
                        num: 4,
                        class: RegisterClass::General,
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
            "$r0.2 = 0x00[$r1.1]",
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
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    },
                    offset: 0x24,
                },
            ),
            (
                "$r0.2 = 0x01[$r0.1]",
                LoadArgs {
                    base: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                    dst: Register {
                        cluster: 0,
                        class: RegisterClass::General,
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
                        cluster: 0,
                        num: 1,
                        class: RegisterClass::General,
                    },
                    offset: 0x20,
                    src: Register {
                        cluster: 0,
                        num: 4,
                        class: RegisterClass::General,
                    },
                },
            ),
            (
                "   5      [ $r0.1      ]    =        $r0.4   ",
                StoreArgs {
                    base: Register {
                        cluster: 0,
                        num: 1,
                        class: RegisterClass::General,
                    },
                    offset: 5,
                    src: Register {
                        cluster: 0,
                        num: 4,
                        class: RegisterClass::General,
                    },
                },
            ),
        ]);

        negative::<StoreArgs, _>(&[
            "0x24[$r0.1] = $r0.2  f",
            "0x24[$r0.1] = $r1.2",
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
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                    src: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    },
                    offset: 1,
                },
            ),
            (
                "0x24[$r0.1] = $r0.2",
                StoreArgs {
                    base: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 1,
                    },
                    src: Register {
                        cluster: 0,
                        class: RegisterClass::General,
                        num: 2,
                    },
                    offset: 0x24,
                },
            ),
        ])
    }
}
