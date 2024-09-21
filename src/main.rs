use clap::Parser;
use miette::{Diagnostic, IntoDiagnostic, NamedSource, SourceSpan};
use regex::Regex;
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::Display;
use std::iter;
use std::sync::LazyLock;
use std::{fs, num::ParseIntError, str::FromStr};
use strum::IntoEnumIterator;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
enum Resource {
    Alu,
    Mul,
    Mem,
}

impl Display for Resource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Alu => "ALU",
            Self::Mem => "MEM",
            Self::Mul => "MUL",
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Kind {
    Arithmetic,
    Multiplication,
    Load,
    Store,
    Intercluster,
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Arithmetic => "Arithmetic",
            Self::Multiplication => "Multiplication",
            Self::Load => "Load",
            Self::Store => "Store",
            Self::Intercluster => "Intercluster Communication",
        })
    }
}

impl From<Kind> for Resource {
    fn from(value: Kind) -> Self {
        match value {
            Kind::Arithmetic | Kind::Intercluster => Self::Alu,
            Kind::Load | Kind::Store => Self::Mem,
            Kind::Multiplication => Self::Mul,
        }
    }
}

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
enum Operand {
    Register(usize),
    Immediate(u32),
}

impl Operand {
    pub fn resolve(self, regs: &[u32]) -> u32 {
        match self {
            Self::Register(r) => regs[r],
            Self::Immediate(i) => i,
        }
    }
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
            let src1 = caps
                .get(2)
                .ok_or(InstructionParseError {})?
                .as_str()
                .parse()?;
            let src2 = Operand::Register(
                caps.get(3)
                    .ok_or(InstructionParseError {})?
                    .as_str()
                    .parse()?,
            );
            let dst = caps
                .get(1)
                .ok_or(InstructionParseError {})?
                .as_str()
                .parse()?;
            Ok(Self { src1, src2, dst })
        } else if let Some(caps) = IMMS.captures(s) {
            let src1 = caps
                .get(2)
                .ok_or(InstructionParseError {})?
                .as_str()
                .parse()?;
            let src2 = Operand::Immediate(parse_num(
                caps.get(3).ok_or(InstructionParseError {})?.as_str(),
            )?);
            let dst = caps
                .get(1)
                .ok_or(InstructionParseError {})?
                .as_str()
                .parse()?;
            Ok(Self { src1, src2, dst })
        } else {
            Err(InstructionParseError {})
        }
    }
}

impl Display for Arithmetic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.src2 {
            Operand::Register(r) => f.write_fmt(format_args!(
                "$r0.{} = $r0.{}, $r0.{}",
                self.dst, self.src1, r
            )),
            Operand::Immediate(i) => f.write_fmt(format_args!(
                "$r0.{} = $r0.{}, 0x{:x}",
                self.dst, self.src1, i
            )),
        }
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
            Err(InstructionParseError {})
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Location {
    Register(usize),
    Memory(usize),
}

impl Location {
    pub fn sanitize(self) -> Self {
        match self {
            Self::Register(r) => Self::Register(r),
            Self::Memory(_) => Self::Memory(0),
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Location::Memory(m) => f.write_fmt(format_args!("Memory[0x{m:4x}]")),
            Location::Register(r) => f.write_fmt(format_args!("$r0.{r}")),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Operation {
    Load(Memory),
    Store(Memory),
    Add(Arithmetic),
    And(Arithmetic),
    AndC(Arithmetic),
    Max(Arithmetic),
    MaxU(Arithmetic),
    MultiplyLU(Arithmetic),
    MultiplyHS(Arithmetic),
    Mov(Move),
}

impl Operation {
    pub fn cmd(&self) -> &'static str {
        match self {
            Self::Add(_) => "add",
            Self::And(_) => "and",
            Self::AndC(_) => "andc",
            Self::Max(_) => "max",
            Self::MaxU(_) => "maxu",
            Self::Mov(_) => "mov",
            Self::MultiplyHS(_) => "mpyhs",
            Self::MultiplyLU(_) => "mpylu",
            Self::Load(_) => "load",
            Self::Store(_) => "stw",
        }
    }
}

impl Operation {
    pub fn kind(&self) -> Kind {
        match self {
            Self::Add(_) | Self::And(_) | Self::AndC(_) | Self::Max(_) | Self::MaxU(_) => {
                Kind::Arithmetic
            }
            Self::Load(_) => Kind::Load,
            Self::Store(_) => Kind::Store,
            Self::MultiplyHS(_) | Self::MultiplyLU(_) => Kind::Multiplication,
            Self::Mov(_) => Kind::Intercluster,
        }
    }
    pub fn inputs(&self) -> Vec<Location> {
        match self {
            Self::Add(args)
            | Self::MultiplyHS(args)
            | Self::MultiplyLU(args)
            | Self::And(args)
            | Self::AndC(args)
            | Self::Max(args)
            | Self::MaxU(args) => match args.src2 {
                Operand::Immediate(_) => vec![Location::Register(args.src1)],
                Operand::Register(r2) => {
                    vec![Location::Register(args.src1), Location::Register(r2)]
                }
            },
            // By definition we don't know WHERE in memory
            Self::Load(mem) => vec![Location::Register(mem.base), Location::Memory(0)],
            Self::Store(mem) => vec![Location::Register(mem.base), Location::Register(mem.reg)],
            Self::Mov(_) => vec![],
        }
    }
    pub fn decode(&self, machine: &Machine) -> Option<Outcome> {
        let Machine { regs, mem, .. } = machine;
        match self {
            Self::Add(args) => Some(Outcome {
                dst: Location::Register(args.dst),
                value: regs[args.src1] + args.src2.resolve(regs),
            }),
            Self::And(args) => Some(Outcome {
                dst: Location::Register(args.dst),
                value: regs[args.src1] & args.src2.resolve(regs),
            }),
            Self::AndC(args) => Some(Outcome {
                dst: Location::Register(args.dst),
                value: !regs[args.src1] & args.src2.resolve(regs),
            }),
            Self::Max(args) => Some(Outcome {
                dst: Location::Register(args.dst),
                value: (regs[args.src1] as i32).max(args.src2.resolve(regs) as i32) as u32,
            }),
            Self::MaxU(args) => Some(Outcome {
                dst: Location::Register(args.dst),
                value: regs[args.src1].max(args.src2.resolve(regs)),
            }),
            Self::MultiplyLU(args) => Some(Outcome {
                dst: Location::Register(args.dst),
                value: regs[args.src1] * (args.src2.resolve(regs) & 0xffff),
            }),
            Self::MultiplyHS(args) => {
                let s2 = (match args.src2 {
                    Operand::Register(r) => regs[r],
                    Operand::Immediate(i) => i,
                } >> 16) as i16;
                Some(Outcome {
                    dst: Location::Register(args.dst),
                    value: regs[args.src1] * s2 as u32,
                })
            }
            Self::Load(args) => {
                let addr = (regs[args.base] + args.offset) as usize;
                Some(Outcome {
                    dst: Location::Register(args.reg),
                    value: u32::from_ne_bytes(mem[addr..addr + 4].try_into().unwrap()),
                })
            }
            Self::Store(args) => {
                let addr = (regs[args.base] + args.offset) as usize;
                Some(Outcome {
                    dst: Location::Memory(addr),
                    value: regs[args.reg],
                })
            }
            Self::Mov(_) => None,
        }
    }
}

impl Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let inst = self.cmd();
        let body = match self {
            Self::Load(mem) => format!("$r0.{} = 0x{:x}[$r0.{}]", mem.reg, mem.offset, mem.base),
            Self::Store(mem) => format!("0x{:x}[$r0.{}] = $r0.{}", mem.offset, mem.base, mem.reg),
            Self::Add(alu)
            | Self::MultiplyHS(alu)
            | Self::MultiplyLU(alu)
            | Self::And(alu)
            | Self::AndC(alu)
            | Self::Max(alu)
            | Self::MaxU(alu) => format!("{alu}"),
            Self::Mov(mov) => format!("$r0.{} = {}", mov.dst, mov.payload),
        };
        f.write_fmt(format_args!("{inst} {body}"))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Instruction {
    pub ctx: Option<(usize, SourceSpan)>,
    pub cluster: usize,
    pub op: Operation,
}

impl Instruction {
    pub fn summary(&self) -> String {
        let out = format!("{} instruction", self.op.cmd());
        if let Some((line, _)) = self.ctx {
            out + &format!(" on line {line}")
        } else {
            out
        }
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Instruction { cluster, op, .. } = self;
        f.write_fmt(format_args!("c{cluster} {op}"))
    }
}

impl FromStr for Instruction {
    type Err = InstructionParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
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
            "and" => Operation::And(raw.parse()?),
            "andc" => Operation::AndC(raw.parse()?),
            "max" => Operation::Max(raw.parse()?),
            "maxu" => Operation::MaxU(raw.parse()?),
            "mpylu" => Operation::MultiplyLU(raw.parse()?),
            "mpyhs" => Operation::MultiplyHS(raw.parse()?),
            "mov" => Operation::Mov(raw.parse()?),
            _ => return Err(InstructionParseError {}),
        };
        Ok(Instruction {
            cluster,
            op,
            ctx: None,
        })
    }
}

impl Instruction {
    pub fn with_context(self, ctx: (usize, SourceSpan)) -> Self {
        Instruction {
            ctx: Some(ctx), ..self
        }
    }
}

/// Describes how a result should be committed
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Outcome {
    /// The value to be committed
    value: u32,
    /// The location to store
    dst: Location,
}

impl Outcome {
    /// Commit this outcome to memory or the register bank
    pub fn commit(&self, regs: &mut [u32], mem: &mut [u8]) {
        match self.dst {
            Location::Memory(m) => {
                mem[m..m + 4].copy_from_slice(&self.value.to_ne_bytes());
            }
            Location::Register(r) => {
                regs[r] = self.value;
            }
        }
    }
}

impl Display for Outcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{} = {}", self.dst, self.value))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Issued<'a> {
    source: &'a Instruction,
    start_cycle: usize,
    finish_cycle: usize,
    result: Option<Outcome>,
}

impl<'a> Display for Issued<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let outcome = if let Some(c) = &self.result {
            Cow::Owned(format!("Result: {c}"))
        } else {
            Cow::Borrowed("<No Effect>")
        };
        f.write_fmt(format_args!(
            "{} instruction issued in cycle {}. {outcome}",
            self.source.op.cmd(),
            self.start_cycle
        ))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ContentionType {
    ReadWrite(Instruction, Instruction),
    WriteRead(Instruction, Instruction),
    WriteWrite(Instruction, Instruction),
}

impl ContentionType {
    fn get_insts(&self) -> (&Instruction, &Instruction) {
        match self {
            Self::ReadWrite(i1, i2) | Self::WriteRead(i1, i2) | Self::WriteWrite(i1, i2) => {
                (i1, i2)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
enum Violation {
    TooManyOperations(Instruction),
    ResourceOverflow(Instruction, Resource),
    RegisterContention(usize, ContentionType),
    MemoryContention(ContentionType),
}

impl Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&match self {
            Violation::MemoryContention(t) => match t {
                ContentionType::WriteWrite(i1, i2) => format!(
                    "The {} writes to memory, but so does the {}",
                    i1.summary(),
                    i2.summary(),
                ),
                ContentionType::ReadWrite(i1, i2) | ContentionType::WriteRead(i2, i1) => {
                    format!(
                        "The {} reads from memory, but the {} writes to memory",
                        i1.summary(),
                        i2.summary(),
                    )
                }
            },
            Violation::RegisterContention(r, t) => match t {
                ContentionType::WriteWrite(i1, i2) => format!(
                    "The {} writes to register $r0.{r}, but so does the {}",
                    i1.summary(),
                    i2.summary()
                ),
                ContentionType::ReadWrite(i1, i2) | ContentionType::WriteRead(i2, i1) => {
                    format!(
                        "The {} reads from register $r0.{r}, but the {} writes to it",
                        i1.summary(),
                        i2.summary()
                    )
                }
            },
            Violation::ResourceOverflow(i, r) => {
                format!("The {} overflowed the {r} unit", i.summary())
            }
            Violation::TooManyOperations(i) => {
                format!("The {} overflowed max number of slots", i.summary())
            }
        })?;
        f.write_str(". This has undefined behavior and is not allowed.")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Machine<'a> {
    regs: Vec<u32>,
    mem: Vec<u8>,
    alus: Vec<Issued<'a>>,
    muls: Vec<Issued<'a>>,
    mems: Vec<Issued<'a>>,
    num_slots: usize,
    num_alus: usize,
    num_muls: usize,
    num_mems: usize,
    alu_latency: usize,
    mul_latency: usize,
    store_latency: usize,
    load_latency: usize,
    pending_reads: HashMap<Location, Vec<Issued<'a>>>,
    pending_writes: HashMap<Location, Issued<'a>>,
}

impl<'a> Machine<'a> {
    pub fn latency(&self, kind: Kind) -> usize {
        match kind {
            Kind::Arithmetic | Kind::Intercluster => self.alu_latency,
            Kind::Multiplication => self.mul_latency,
            Kind::Load => self.load_latency,
            Kind::Store => self.store_latency,
        }
    }
    pub fn capacity(&self, resource: Resource) -> usize {
        match resource {
            Resource::Alu => self.num_alus,
            Resource::Mem => self.num_mems,
            Resource::Mul => self.num_muls,
        }
    }
    pub fn resource(&self, resource: Resource) -> &Vec<Issued<'a>> {
        match resource {
            Resource::Alu => &self.alus,
            Resource::Mem => &self.mems,
            Resource::Mul => &self.muls,
        }
    }
    fn resource_mut(&mut self, resource: Resource) -> &mut Vec<Issued<'a>> {
        match resource {
            Resource::Alu => &mut self.alus,
            Resource::Mem => &mut self.mems,
            Resource::Mul => &mut self.muls,
        }
    }
    pub fn issue<I>(&mut self, insts: I, cycle: usize) -> Result<(), Box<Violation>>
    where
        I: IntoIterator<Item = &'a Instruction>,
    {
        for (count, i) in insts.into_iter().enumerate() {
            if count > self.num_slots {
                return Err(Box::new(Violation::TooManyOperations(i.clone())));
            }
            // if any input is in our list of pending writes, bail
            for l in i.op.inputs() {
                if let Some(prev) = self.pending_writes.get(&l) {
                    // So, someone is writing to this location. That's a problem
                    return Err(Box::new(match l {
                        Location::Memory(_) => Violation::MemoryContention(
                            ContentionType::WriteRead(prev.source.clone(), i.clone()),
                        ),
                        Location::Register(r) => Violation::RegisterContention(
                            r,
                            ContentionType::WriteRead(prev.source.clone(), i.clone()),
                        ),
                    }));
                }
            }
            // Add our inputs to the list of pending reads...?
            // But when do these get removed? When do we clear the pending stuff? Comparing instructions is annoying,
            // and since the hash map isn't keyed by cycle... we don't know when to remove these.
            //
            // Idea: Just add more information. Simplest is instead of Location -> &Instruction, make it
            //  Location -> (&Instruction, usize). In this way, now we know when to remove it. We still have
            //  to iterate over all pending reads and pending writes though on each cycle...
            //  Also wait this won't work, that key isn't unique. If 2 instructions READ the same reg, that's
            //  fine, but the first to complete will remove it. No, what we need is a way of pairing an instruction
            //  with its outcome. Perhaps every instruction could have a monotonically-increasing ID? OR every
            //  Issued<'a> could have an ID associated with it... I'm not sure. But we could use that ID as a key
            //  to get an outcome, and THAT could tell us when to
            //
            //  Alternatively... what if we just key by finish cycle? So [finish cycle] -> Vec<Location>.
            //  Then, when we hit that cycle, clear that key. The only problem here is that every issue we
            //  have to iterate over all values; we don't get saved by a hash map. We could maybe make those
            //  hash sets, and then each time we issue we create one giant hash set? Right now that seems
            //  to be the best option. Performance wise, we could keep that hash set along with us, but the
            //  problem there is that now we've got two sources of truth that must be kept in sync.
            let c = i.op.decode(self);
            // Now, we are writing to something. We need to check BOTH pending reads and pending writes
            if let Some(outcome) = &c {
                if let Some(prev) = self.pending_writes.get(&outcome.dst) {
                    return Err(Box::new(match outcome.dst {
                        Location::Memory(_) => Violation::MemoryContention(
                            ContentionType::WriteWrite(prev.source.clone(), i.clone()),
                        ),
                        Location::Register(r) => Violation::RegisterContention(
                            r,
                            ContentionType::WriteWrite(prev.source.clone(), i.clone()),
                        ),
                    }));
                }
                if let Some(issued) = self.pending_reads.get(&outcome.dst) {
                    if let Some(prev) = issued.iter().min_by_key(|i| i.start_cycle) {
                        return Err(Box::new(match outcome.dst {
                            Location::Memory(_) => Violation::MemoryContention(
                                ContentionType::ReadWrite(prev.source.clone(), i.clone()),
                            ),
                            Location::Register(r) => Violation::RegisterContention(
                                r,
                                ContentionType::ReadWrite(prev.source.clone(), i.clone()),
                            ),
                        }));
                    }
                }
            }
            let k = i.op.kind();
            let r = k.into();
            let latency = self.latency(k);
            let cap = self.capacity(r);
            let units = self.resource_mut(r);
            if units.len() == cap {
                return Err(Box::new(Violation::ResourceOverflow(i.clone(), r)));
            }
            let issued = Issued {
                source: i,
                start_cycle: cycle,
                finish_cycle: cycle + latency,
                result: c,
            };
            units.push(issued);
            // At this point, we need to update our pending reads and pending writes
            for l in i.op.inputs() {
                self.pending_reads
                    .entry(l.sanitize())
                    .or_default()
                    .push(issued);
            }
            if let Some(outcome) = c {
                // Should have already been checked
                if let Some(imp) = self.pending_writes.insert(outcome.dst.sanitize(), issued) {
                    panic!(
                        "Pending writes should not have been populated, but was with {}",
                        imp.source
                    );
                }
            }
        }
        Ok(())
    }
    pub fn commit(&mut self, cycle: usize) -> Vec<Issued<'a>> {
        let mut committed: Vec<Issued<'a>> = vec![];
        for r in Resource::iter() {
            let mut kept = vec![];
            let resource = self.resource_mut(r);
            for i in resource.drain(..) {
                if i.finish_cycle == cycle {
                    // Note that any contention was found in issuance
                    committed.push(i);
                } else {
                    kept.push(i);
                }
            }
            *resource = kept;
        }

        for c in committed.iter().filter_map(|r| r.result.as_ref()) {
            c.commit(&mut self.regs, &mut self.mem);
            // Clean it up
            self.pending_writes.remove(&c.dst);
        }
        // Clean up pending reads
        for insts in self.pending_reads.values_mut() {
            insts.retain(|i| i.finish_cycle > cycle);
        }

        // TODO:
        // 1. QUESTION: Register access -- if an instruction is WRITING to a register in this cycle, NOBODY else
        //      should be referencing that register in any way
        // 2. QUESTION: What exactly are the semantics here? Which of the following is allowed:
        //      a. Same VLIW inst: A LOAD that reads R1, and an ADD that reads R1
        //      b. Same VLIW inst: A LOAD that reads R1, and an ADD that writes R1
        //      c. Same VLIW inst: A LOAD that writes R1, and an ADD that writes R1
        //      d. A LOAD that reads from R1 **and writes** to R1
        //      e. A LOAD that reads from R1; next cycle, an ADD that writes R1
        //      f. A LOAD that writes to R1; next cycle, an ADD that reads R1
        //      g. An ADD that writes to R1; next cycle, a LOAD that reads R1 (if allowed, what is R1?)
        // 3. Be more precise about instruction vs operation
        // 4. When are results committed? In other words, Suppose in cycle 0 we issue r1 = r2 + r3.
        //      In cycle 1, is r1 now finished?
        // 5. That we contain enough groups to finish out (?)
        // 6. should we catch the following:
        // R1 = LDW(0x20, R2)
        // ;;
        // R1 = ADD(R3, R4)
        // ;;
        // ;; <-- We've mutated a register WHILE LDW is mutating said register.
        //
        // So, does an instruction get a lease on input/output registers for
        //  the entirety of its latency? If the LDW lasts 100 cycles, does that mean
        //  NOBODY can write to R1 in that 100 cycles, even if it finishes before/after?
        //  My opinion is yes; at decode time, the values are sent, and that the value
        //  is not written until exactly the last cycle
        committed
    }
}

fn format_slot<'a>(slot: Option<&'a Issued<'a>>) -> String {
    format!(
        "{}",
        if let Some(inst) = slot {
            Cow::Owned(format!("{inst}"))
        } else {
            Cow::Borrowed("<Empty>")
        }
    )
}

impl<'a> Display for Machine<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for u in [Resource::Alu, Resource::Mem, Resource::Mul].into_iter() {
            f.write_fmt(format_args!("{u}:\n"))?;
            self.resource(u)
                .iter()
                .map(Some)
                .chain(iter::repeat(None).take(self.capacity(u) - self.resource(u).len()))
                .enumerate()
                .try_for_each(|(s, i)| f.write_fmt(format_args!("\t{s}: {}\n", format_slot(i))))?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
struct Group(Vec<Instruction>);

impl Display for Group {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in &self.0 {
            f.write_fmt(format_args!("{i}\n"))?;
        }
        f.write_str(";;")
    }
}

#[derive(clap::Parser, Debug)]
#[command(version)]
struct Args {
    /// Number of slots
    #[arg(long, short, default_value_t = 4)]
    num_slots: usize,
    /// Number of integer resources
    #[arg(long, default_value_t = 4)]
    alu_slots: usize,
    /// Latency for ALU operations
    #[arg(long, default_value_t = 1)]
    alu_latency: usize,
    /// Number of multipliers
    #[arg(long, default_value_t = 2)]
    mul_slots: usize,
    /// Latency for MUL operations
    #[arg(long, default_value_t = 2)]
    mul_latency: usize,
    /// Number of memory resources
    #[arg(long, default_value_t = 1)]
    mem_slots: usize,
    /// Latency for LOAD operations
    #[arg(long, default_value_t = 3)]
    load_latency: usize,
    /// Latency for STORE operations
    #[arg(long, default_value_t = 3)]
    store_latency: usize,
    /// Assert to print debugging information; useful if your code is failing
    /// to compile or producing... interesting results
    #[arg(long, short, default_value_t = false)]
    verbose: bool,
    /// Size of memory, in bytes
    #[arg(long, default_value_t = 4096)]
    mem_size: usize,
    /// Number of registers
    #[arg(long, default_value_t = 64)]
    num_regs: usize,
    /// Basic Block file
    file: String,
    /// Numbers (inputs for your VEX code)
    nums: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, thiserror::Error)]
enum ParameterError {
    #[error("Memory must be at least 4 bytes; given {0}")]
    NotEnoughMemory(usize),
    #[error("Memory must be aligned to 4 bytes; given {0}")]
    BadMemoryAlign(usize),
    #[error("At least two registers are required")]
    NotEnoughRegisters,
    #[error("At least one slot is required")]
    NotEnoughSlots,
    #[error("At least one {0} is required")]
    NotEnoughUnit(Resource),
    #[error("Latency for {0} must be non-zero")]
    ZeroLatency(Kind),
    #[error("Exactly 10 numbers must be provided; {0} given")]
    InvalidArguments(usize),
    #[error("Input file `{0}` not found")]
    FileNotFound(String),
}

impl<'a> Machine<'a> {
    pub fn new(args: &Args) -> Result<Machine<'a>, ParameterError> {
        if args.mem_size < 4 {
            return Err(ParameterError::NotEnoughMemory(args.mem_size));
        }
        if (args.mem_size % 4) != 0 {
            return Err(ParameterError::BadMemoryAlign(args.mem_size));
        }
        if args.num_regs < 2 {
            return Err(ParameterError::NotEnoughRegisters);
        }
        if args.num_slots == 0 {
            return Err(ParameterError::NotEnoughSlots);
        }
        if args.mul_slots == 0 {
            return Err(ParameterError::NotEnoughUnit(Resource::Mul));
        }
        if args.alu_slots == 0 {
            return Err(ParameterError::NotEnoughUnit(Resource::Alu));
        }
        if args.mem_slots == 0 {
            return Err(ParameterError::NotEnoughUnit(Resource::Mem));
        }
        if args.load_latency == 0 {
            return Err(ParameterError::ZeroLatency(Kind::Load));
        }
        if args.alu_latency == 0 {
            return Err(ParameterError::ZeroLatency(Kind::Arithmetic));
        }
        if args.store_latency == 0 {
            return Err(ParameterError::ZeroLatency(Kind::Store));
        }
        if args.mul_latency == 0 {
            return Err(ParameterError::ZeroLatency(Kind::Multiplication));
        }
        if args.nums.len() != 10 {
            return Err(ParameterError::InvalidArguments(args.nums.len()));
        }
        let mut mem = vec![0u8; args.mem_size];
        let mut regs = vec![0u32; args.num_regs];
        for (m, n) in (0x18..=0x2c).step_by(4).zip(args.nums.iter().skip(1)) {
            mem[m..m + 4].copy_from_slice(&n.to_ne_bytes());
        }
        mem[0x30..0x34].copy_from_slice(&args.nums[8].to_ne_bytes());
        regs[3] = args.nums[9];
        Ok(Machine {
            mem,
            regs,
            num_slots: args.num_slots,
            num_alus: args.alu_slots,
            alu_latency: args.alu_latency,
            num_muls: args.mul_slots,
            mul_latency: args.mul_latency,
            num_mems: args.mem_slots,
            load_latency: args.load_latency,
            store_latency: args.store_latency,
            alus: Vec::with_capacity(args.alu_slots),
            mems: Vec::with_capacity(args.mem_slots),
            muls: Vec::with_capacity(args.mul_slots),
            pending_reads: HashMap::new(),
            pending_writes: HashMap::new(),
        })
    }
}

#[derive(Debug, thiserror::Error)]
#[error("Line {lineno}: {line}")]
struct ParseError {
    lineno: usize,
    line: String,
    source: InstructionParseError,
}

#[derive(Error, Debug, Diagnostic)]
#[error("Undefined Behavior")]
#[diagnostic()]
struct ExecutionDiagnostic {
    #[help]
    violation: Violation,
    #[source_code]
    src: NamedSource<String>,
    #[label = "Offending Instruction"]
    curr: Option<SourceSpan>,
    #[label = "Previous Instruction"]
    prev: Option<SourceSpan>,
}

fn main() -> miette::Result<()> {
    miette::set_hook(Box::new(|_| {
        Box::new(
            miette::MietteHandlerOpts::new()
                .terminal_links(true)
                .width(120)
                .break_words(true)
                .wrap_lines(true)
                .context_lines(5)
                .build(),
        )
    }))
    .into_diagnostic()?;
    let args = Args::parse();
    let backing = fs::read_to_string(&args.file)
        .map_err(|_| ParameterError::FileNotFound(args.file.clone()))
        .into_diagnostic()?
        // Sanitize line endings
        .lines()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n");
    let lines: Vec<(usize, SourceSpan, &str)> = backing.lines()
        .enumerate()
        .fold(vec![], |mut v, (i, line)| {
            let start_idx = if let Some((_, span, _)) = v.last() {
                span.offset() + span.len() + 1
            } else {
                0
            };
            v.push((i + 1, (start_idx, line.len()).into(), line));
            v
        });

    let mut groups: Vec<Group> = vec![];
    let mut group = Group::default();
    let inst_lines = lines.iter()
        .skip_while(|&&(_, _, l)| l != "#### BEGIN BASIC BLOCK ####")
        .skip(1)
        .take_while(|&&(_, _, l)| l != "#### END BASIC BLOCK ####")
        .filter(|&&(_, _, l)| !l.trim_start().starts_with('#'));
    for &(i, span, line) in inst_lines {
        if line.trim_start().starts_with(";;") {
            // eject
            groups.push(group);
            group = Group::default();
        } else {
            let inst: Instruction = line
                .parse()
                .map_err(|source| ParseError {
                    lineno: i,
                    line: line.to_owned(),
                    source,
                })
                .into_diagnostic()?;
            group.0.push(inst.with_context((i, span)));
        }
    }
    // Push one more to ensure we have a cycle to clear the last of the pending
    groups.push(Group::default());
    let groups = groups;

    let mut machine = Machine::new(&args).into_diagnostic()?;

    for (cycle, g) in groups.iter().enumerate() {
        // Resolve anything that would finish this cycle
        let resolved = machine.commit(cycle);
        if args.verbose {
            println!("{} resolved in cycle {cycle}:", resolved.len());
            for r in resolved {
                println!("\t* {r}");
            }
        }
        // What is about to be issued?
        if args.verbose {
            println!("{}/{} slots filled:", g.0.len(), machine.num_slots);
            for (s, inst) in g.0.iter().enumerate() {
                println!("\t{s}: {inst}");
            }
        }
        // Issue instructions to their respective resources
        if let Err(e) = machine.issue(&g.0, cycle) {
            let (prev, curr) = match &*e {
                Violation::ResourceOverflow(i, _) | Violation::TooManyOperations(i) => {
                    (None, i.ctx.map(|(_, s)| s))
                }
                Violation::RegisterContention(_, c) | Violation::MemoryContention(c) => {
                    let (i1, i2) = c.get_insts();
                    (i1.ctx.map(|(_, s)| s), i2.ctx.map(|(_, s)| s))
                }
            };
            Err(ExecutionDiagnostic {
                src: NamedSource::new(
                    &args.file,
                    backing.clone(),
                ),
                prev, curr, violation: *e,
            })?;
        }
        if args.verbose {
            println!("Machine state at the end of cycle {cycle}:\n{machine}");
        }
    }
    println!("{} in {} cycles", machine.regs[4], groups.len());
    Ok(())
}
