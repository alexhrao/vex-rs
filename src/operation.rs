use std::fmt::Display;
use crate::{Machine, Outcome, Operand, Location};


trait Opcode {
    fn code(&self) -> &'static str;
}

trait Decode {
    fn decode(&self, machine: &Machine) -> Option<Outcome>;
}

// TODO: newtype for general, branch regs?
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Register {
    General(usize),
    Branch(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Arithmetic2 {
    opcode: ArithmeticOpcode,
    /// The first input register
    src1: usize,
    /// The second argument, either a register or an immediate
    src2: Operand,
    /// The destination register
    dst: usize,
}

impl Decode for Arithmetic2 {
    fn decode(&self, machine: &Machine) -> Option<Outcome> {
        let dst = Location::Register(self.dst);
        let a1 = machine.regs[self.src1];
        let a2 = self.src2.resolve(&machine.regs);

        let value = match self.opcode {
            ArithmeticOpcode::Add => a1 + a2,
            ArithmeticOpcode::AddCarry => panic!(),
            ArithmeticOpcode::And => a1 & a2,
            ArithmeticOpcode::AndCarry => panic!(),
            ArithmeticOpcode::Max => panic!(),
            ArithmeticOpcode::MaxUnsigned => a1.max(a2),
            ArithmeticOpcode::Min => panic!(),
            ArithmeticOpcode::MinUnsigned => a1.min(a2),
            ArithmeticOpcode::MultiplyHigh => panic!(),
            ArithmeticOpcode::MultiplyHighHigh => panic!(),
            ArithmeticOpcode::MultiplyHighHighUnsigned => panic!(),
            ArithmeticOpcode::MultiplyHighShift => panic!(),
            ArithmeticOpcode::MultiplyHighUnsigned => panic!(),
            ArithmeticOpcode::MultiplyLow => panic!(),
            ArithmeticOpcode::MultiplyLowHigh => panic!(),
            ArithmeticOpcode::MultiplyLowHighUnsigned => panic!(),
            ArithmeticOpcode::MultiplyLowLow => panic!(),
            ArithmeticOpcode::MultiplyLowLowUnsigned => panic!(),
            ArithmeticOpcode::MultiplyLowUnsigned => panic!(),
            ArithmeticOpcode::Or => a1 | a2,
            ArithmeticOpcode::OrCarry => panic!(),
            ArithmeticOpcode::Shift1Add => (a1 << 1) + a2,
            ArithmeticOpcode::Shift2Add => (a1 << 2) + a2,
            ArithmeticOpcode::Shift3Add => (a1 << 3) + a2,
            ArithmeticOpcode::Shift4Add => (a1 << 4) + a2,
            ArithmeticOpcode::ShiftLeft => a1 << a2,
            ArithmeticOpcode::ShiftRight => panic!(),
            ArithmeticOpcode::ShiftRightUnsigned => a1 >> a2,
            ArithmeticOpcode::Xor => a1 ^ a2,
        };
        Some(Outcome { dst, value })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Division {
    dst_reg: usize,
    dst_carry: usize,
    src_carry: usize,
    src1: usize,
    src2: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SignExtend {
    /// The opcode
    opcode: SignExtendOpcode,
    /// The source register
    src: usize,
    /// The destination register
    dst: usize,
}

impl Decode for SignExtend {
    fn decode(&self, machine: &Machine) -> Option<Outcome> {
        let s = machine.regs[self.src];
        let value = match self.opcode {
            SignExtendOpcode::Byte => panic!(),
            SignExtendOpcode::Half => panic!(),
            SignExtendOpcode::ZeroByte => s & 0xff,
            SignExtendOpcode::ZeroHalf => s & 0xffff,
        };
        Some(Outcome {
            dst: Location::Register(self.dst),
            value,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum SignExtendOpcode {
    Byte,
    Half,
    ZeroByte,
    ZeroHalf,
}

impl Opcode for SignExtendOpcode {
    fn code(&self) -> &'static str {
        match self {
            Self::Byte => "sxtb",
            Self::Half => "sxth",
            Self::ZeroByte => "zxtb",
            Self::ZeroHalf => "zxth",

        }
    }
}

impl Display for SignExtendOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ArithmeticOpcode {
    Add,
    AddCarry,
    And,
    AndCarry,
    Max,
    MaxUnsigned,
    Min,
    MinUnsigned,
    Or,
    OrCarry,
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
// enum ArithmeticOpcode {
//     Add,
//     AddCG,
//     And,
//     AndC,
//     Max,
//     MaxU,
//     Min,
//     MinU,
//     Or,
//     OrC,
//     Sh1Add,
//     Sh2Add,
//     Sh3Add,
//     Sh4Add,
//     Shl,
//     Shr,
//     ShrU,
//     Xor,
//     MpyLL,
//     MpyLLU,
//     MpyLH,
//     MpyLHU,
//     MpyHH,
//     MpyHHU,
//     MpyL,
//     MpyLU,
//     MpyH,
//     MpyHU,
//     MpyHS,
// }

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum CompareOpcode {
    Eq,
    GreaterEq,
    GreaterEqUnsigned,
    Greater,
    GreaterUnsigned,
    LessEq,
    LessEqUnsigned,
    Less,
    LessUnsigned,
    NotEq,
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum LogicalOpcode {
    NotAnd,
    NotOr,
    Or,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Compare {
    opcode: CompareOpcode,
    dst: Register,
    src1: usize,
    src2: Operand,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Logical {
    opcode: LogicalOpcode,
    dst: Register,
    src1: usize,
    src2: usize,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Send {
    src: usize,
    imm: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Recv {
    dst: usize,
    imm: u32,
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Operation2 {
    Arithmetic(Arithmetic2),
    SignExtend(SignExtend),
    Division(Division),
    Compare(Compare),
    Logical(Logical),
    Send(Send),
    Recv(Recv),
}

impl Decode for Operation2 {
    fn decode(&self, machine: &Machine) -> Option<Outcome> {
        match self {
            Self::Arithmetic(args) => args.decode(machine),
            Self::SignExtend(args) => args.decode(machine),
            Self::Compare(_) => panic!(),
            Self::Division(_) => panic!(),
            Self::Logical(_) => panic!(),
            Self::Send(_) => panic!(),
            Self::Recv(_) => panic!(),
        }
    }
}