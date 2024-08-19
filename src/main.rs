use clap::Parser;
use regex::Regex;
use std::sync::LazyLock;
use std::{fs, num::ParseIntError, str::FromStr};

const NUM_REGS: usize = 64;

#[derive(thiserror::Error, Debug)]
#[error("Instruction failed to parse")]
struct InstructionParseError {}

impl From<ParseIntError> for InstructionParseError {
    fn from(_: ParseIntError) -> Self {
        Self {}
    }
}

fn parse_num(num: &str) -> Result<u32, ParseIntError> {
    if num.starts_with("0x") {
        u32::from_str_radix(num.trim_start_matches("0x"), 16)
    } else {
        num.parse()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Memory {
    base: usize,
    offset: u32,
    reg: usize,
}

impl FromStr for Memory {
    type Err = InstructionParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        static LDW: LazyLock<Regex> = LazyLock::new(|| {
            Regex::new(r"^\$r0\.(\d+)\s*=\s*([0-9a-fA-Fx]+)\[\$r0\.(\d+)\]").unwrap()
        });
        static STW: LazyLock<Regex> = LazyLock::new(|| {
            Regex::new(r"^([0-9a-fA-Fx]+)\[\$r0\.(\d+)\]\s*=\s*\$r0\.(\d+)").unwrap()
        });
        if let Some(caps) = LDW.captures(s) {
            let base = caps.get(3).unwrap().as_str().parse()?;
            let reg = caps.get(1).unwrap().as_str().parse()?;
            let offset = parse_num(caps.get(2).unwrap().as_str())?;
            Ok(Self { base, reg, offset })
        } else if let Some(caps) = STW.captures(s) {
            let base = caps.get(2).unwrap().as_str().parse()?;
            let reg = caps.get(3).unwrap().as_str().parse()?;
            let offset = parse_num(caps.get(1).unwrap().as_str())?;
            Ok(Self { base, reg, offset })
        } else {
            panic!()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Operand {
    Register(usize),
    Immediate(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Arithmetic {
    src1: usize,
    src2: Operand,
    dst: usize,
}

impl FromStr for Arithmetic {
    type Err = InstructionParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // $r0.10 = $r0.10, $r0.7   ## bblock 10, line 23,  t114,  t4,  t108
        // $r0.10 = $r0.10, 0x20  ## bblock 10, line 23,  t114,  t4,  t108
        static REGS: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(r"^\$r0\.(\d+)\s*=\s*\$r0\.(\d+),\s*\$r0\.(\d+)").unwrap());
        static IMMS: LazyLock<Regex> = LazyLock::new(|| {
            Regex::new(r"^\$r0\.(\d+)\s*=\s*\$r0\.(\d+),\s*([0-9a-fA-Fx]+)").unwrap()
        });

        if let Some(caps) = REGS.captures(s) {
            let src1 = caps.get(2).unwrap().as_str().parse()?;
            let src2 = Operand::Register(caps.get(3).unwrap().as_str().parse()?);
            let dst = caps.get(1).unwrap().as_str().parse()?;
            Ok(Self { src1, src2, dst })
        } else if let Some(caps) = IMMS.captures(s) {
            let src1 = caps.get(2).unwrap().as_str().parse()?;
            let src2 = Operand::Immediate(parse_num(caps.get(3).unwrap().as_str())?);
            let dst = caps.get(1).unwrap().as_str().parse()?;
            Ok(Self { src1, src2, dst })
        } else {
            panic!()
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Move {
    dst: usize,
    payload: String,
}

impl FromStr for Move {
    type Err = InstructionParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        static MOV: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(r"^\$r0\.(\d+)\s*=\s*([^#]+)").unwrap());
        let caps = MOV.captures(s).unwrap();
        let dst = caps.get(1).unwrap().as_str().parse()?;
        let payload = caps.get(2).unwrap().as_str().trim().to_owned();

        Ok(Self { dst, payload })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Operation {
    Load(Memory),
    Store(Memory),
    Add(Arithmetic),
    MultiplyLU(Arithmetic),
    MultiplyHS(Arithmetic),
    Mov(Move),
}

impl Operation {
    pub fn execute(&self, regs: &mut [u32], mem: &mut [u32]) {
        match self {
            Self::Add(args) => {
                regs[args.dst] = regs[args.src1]
                    + match args.src2 {
                        Operand::Register(r) => regs[r],
                        Operand::Immediate(i) => i,
                    };
            }
            Self::MultiplyLU(args) => {
                let s2: u32 = match args.src2 {
                    Operand::Register(r) => regs[r] as u16,
                    Operand::Immediate(i) => i as u16,
                }
                .into();
                regs[args.dst] = regs[args.src1] * s2;
            }
            Self::MultiplyHS(args) => {
                let s2 = (match args.src2 {
                    Operand::Register(r) => regs[r],
                    Operand::Immediate(i) => i,
                } >> 16) as i16;
                // TODO
                regs[args.dst] = regs[args.src1] * s2 as u32;
            }
            Self::Load(args) => {
                regs[args.reg] = mem[((regs[args.base] / 4) + (args.offset / 4)) as usize];
            }
            Self::Mov(_) => {
                // ??
            }
            x => {
                println!("{x:?}");
                panic!("Ah shit");
            }
        };
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Instruction {
    pub cluster: usize,
    pub op: Operation,
}

impl FromStr for Instruction {
    type Err = InstructionParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        //         c0    add $r0.10 = $r0.10, $r0.7   ## bblock 10, line 23,  t114,  t4,  t108
        static BASE: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(r"^\s*c([01])\s+(\w+)\s+(.*)$").unwrap());
        let caps = BASE.captures(s).ok_or(InstructionParseError {})?;
        let cluster = caps
            .get(1)
            .ok_or(InstructionParseError {})?
            .as_str()
            .parse()?;
        let raw = caps.get(3).ok_or(InstructionParseError {})?.as_str();

        let op = match caps.get(2).ok_or(InstructionParseError {})?.as_str() {
            "ldw" => Operation::Load(raw.parse()?),
            "stw" => Operation::Store(raw.parse()?),
            "add" => Operation::Add(raw.parse()?),
            "mpylu" => Operation::MultiplyLU(raw.parse()?),
            "mpyhs" => Operation::MultiplyHS(raw.parse()?),
            "mov" => Operation::Mov(raw.parse()?),
            _ => panic!(),
        };
        Ok(Instruction { cluster, op })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Group {
    insts: Vec<Instruction>,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
enum Violation {
    #[error("Overflowed max number of slots ({0} used)")]
    TooManyOperations(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Group {group}, Instruction {inst:?}: {source}")]
struct VerificationError {
    group: usize,
    inst: Option<usize>,
    source: Violation,
}

fn check(args: &Args, groups: &[Group]) -> Result<(), VerificationError> {
    for (g, group) in groups.iter().enumerate() {
        if group.insts.len() > args.slots {
            return Err(VerificationError { group: g, inst: None, source: Violation::TooManyOperations(group.insts.len()) })
        }
    }
    Ok(())
}

#[derive(clap::Parser, Debug)]
struct Args {
    /// Number of slots
    #[arg(long, short, default_value_t=4)]
    slots: usize,
    /// Number of integer units 
    #[arg(long, short, default_value_t=4)]
    alu: usize,
    /// Number of multipliers
    #[arg(long, default_value_t=2)]
    mul: usize,
    /// Number of memory units
    #[arg(long, default_value_t=1)]
    mem: usize,
    /// Basic Block file
    file: String,
    /// Numbers
    nums: Vec<u32>,
}

fn main() -> color_eyre::eyre::Result<()>{
    color_eyre::install()?;
    let args = Args::parse();
    let mut regs = vec![0u32; NUM_REGS];
    let mut mem = vec![0u32; 4096];
    for (m, n) in ((0x18 / 4)..=(0x2c/4)).zip(args.nums.iter().skip(1)) {
        mem[m] = *n;
    }
    mem[0x30/4] = args.nums[8];
    regs[3] = args.nums[9];

    let backing = fs::read_to_string(&args.file).unwrap();
    let lines = backing
        .lines()
        .skip_while(|&l| l != "#### BEGIN BASIC BLOCK ####")
        .take_while(|&l| l != "#### END BASIC BLOCK ####");
    let mut groups: Vec<Group> = vec![];
    let mut group = Group {
        insts: vec![],
    };
    for line in lines {
        if line.starts_with(";;") {
            // eject
            groups.push(group);
            group = Group { insts: vec![] };
        } else if let Ok(inst) = line.parse() {
            group.insts.push(inst);
        }
    }
    if let Err(e) = check(&args, &groups) {
        panic!("{e}");
    }
    for g in &groups {
        for i in &g.insts {
            i.op.execute(&mut regs, &mut mem);
        }
    }
    // for i in insts {
    //     i.op.execute(&mut regs, &mut mem);
    // }
    println!("{}", regs[4]);
    Ok(())
}