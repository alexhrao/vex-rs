//! Vex Simulator, written in Rust

use clap::Parser;
use miette::{Diagnostic, IntoDiagnostic, NamedSource, SourceSpan};
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::Display;
use std::fs;
use std::iter;
use std::ops::{Index, IndexMut};
use strum::IntoEnumIterator;
use thiserror::Error;

mod operation;

use operation::{Instruction, Kind, Location, ParseError, Register, RegisterType, WithContext};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
enum Resource {
    Alu,
    Mul,
    Load,
    Store,
}

impl Display for Resource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Alu => "Arithmetic & Logic",
            Self::Load => "Memory Load",
            Self::Store => "Memory Store",
            Self::Mul => "Multiplier",
        })
    }
}

// #[derive(Clone, Debug, PartialEq, Eq, Hash)]
// struct Move {
//     dst: usize,
//     payload: String,
// }

// impl FromStr for Move {
//     type Err = ();

//     fn from_str(s: &str) -> Result<Self, Self::Err> {
//         static MOV: LazyLock<Regex> =
//             LazyLock::new(|| Regex::new(r"^\$r0\.(\d+)\s*=\s*([^#]+)").unwrap());
//         let caps = MOV.captures(s).unwrap();
//         let dst = caps.get(1).unwrap().as_str().parse().map_err(|_| ())?;
//         let payload = caps.get(2).unwrap().as_str().trim().to_owned();

//         Ok(Self { dst, payload })
//     }
// }

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
    pub fn commit(&self, machine: &mut Machine) {
        match self.dst {
            Location::Memory(m) => {
                machine.mem[m..m + 4].copy_from_slice(&self.value.to_ne_bytes());
            }
            Location::Register(r) => {
                machine[r] = self.value;
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
        let outcome = self
            .result
            .as_ref()
            .map_or(Cow::Borrowed("<No Effect>"), |c| {
                Cow::Owned(format!("Result: {c}"))
            });
        f.write_fmt(format_args!(
            "{} instruction issued in cycle {}. {outcome}",
            self.source.op.code(),
            self.start_cycle
        ))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ContentionType {
    ReadWrite(Instruction, Instruction),
    WriteRead(Instruction, Instruction),
    WriteWrite(Instruction, Instruction),
}

impl ContentionType {
    const fn get_insts(&self) -> (&Instruction, &Instruction) {
        match self {
            Self::ReadWrite(i1, i2) | Self::WriteRead(i1, i2) | Self::WriteWrite(i1, i2) => {
                (i1, i2)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Hash)]
enum Violation {
    TooManyOperations(Instruction),
    ResourceOverflow(Instruction, Resource),
    RegisterContention(Register, ContentionType),
    MemoryContention(ContentionType),
}

impl Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&match self {
            Self::MemoryContention(t) => match t {
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
            Self::RegisterContention(r, t) => match t {
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
            Self::ResourceOverflow(i, r) => format!("The {} overflowed the {r} unit", i.summary()),
            Self::TooManyOperations(i) => {
                format!("The {} overflowed max number of slots", i.summary())
            }
        })?;
        f.write_str(". This has undefined behavior and is not allowed.")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Machine<'a> {
    gregs: Vec<u32>,
    bregs: Vec<u32>,
    mem: Vec<u8>,
    alus: Vec<Issued<'a>>,
    muls: Vec<Issued<'a>>,
    loads: Vec<Issued<'a>>,
    stores: Vec<Issued<'a>>,
    num_slots: usize,
    num_alus: usize,
    num_muls: usize,
    num_loads: usize,
    num_stores: usize,
    alu_latency: usize,
    mul_latency: usize,
    store_latency: usize,
    load_latency: usize,
    pending_reads: HashMap<Location, Vec<Issued<'a>>>,
    pending_writes: HashMap<Location, Issued<'a>>,
}

impl<'a> Index<Register> for Machine<'a> {
    type Output = u32;
    fn index(&self, index: Register) -> &Self::Output {
        match index.bank {
            RegisterType::Branch => &self.bregs[index.num],
            RegisterType::General => &self.gregs[index.num],
            RegisterType::Link => todo!(),
        }
    }
}

impl<'a> IndexMut<Register> for Machine<'a> {
    fn index_mut(&mut self, index: Register) -> &mut Self::Output {
        match index.bank {
            RegisterType::Branch => &mut self.bregs[index.num],
            RegisterType::General => &mut self.gregs[index.num],
            RegisterType::Link => todo!(),
        }
    }
}

impl<'a> Machine<'a> {
    pub fn latency(&self, kind: Kind) -> usize {
        match kind.into() {
            Resource::Alu => self.alu_latency,
            Resource::Mul => self.mul_latency,
            Resource::Load => self.load_latency,
            Resource::Store => self.store_latency,
        }
    }
    pub const fn capacity(&self, resource: Resource) -> usize {
        match resource {
            Resource::Alu => self.num_alus,
            Resource::Load => self.num_loads,
            Resource::Store => self.num_stores,
            Resource::Mul => self.num_muls,
        }
    }
    pub const fn resource(&self, resource: Resource) -> &Vec<Issued<'a>> {
        match resource {
            Resource::Alu => &self.alus,
            Resource::Load => &self.loads,
            Resource::Store => &self.stores,
            Resource::Mul => &self.muls,
        }
    }
    fn resource_mut(&mut self, resource: Resource) -> &mut Vec<Issued<'a>> {
        match resource {
            Resource::Alu => &mut self.alus,
            Resource::Load => &mut self.loads,
            Resource::Store => &mut self.stores,
            Resource::Mul => &mut self.muls,
        }
    }
    // fn check(&self, reg: &Register) -> Result<(), ()> {
    //     if reg.num < match reg.bank {
    //         RegisterType::Branch => self.bregs.len(),
    //         RegisterType::General => self.gregs.len(),
    //         RegisterType::Link => todo!(),
    //     } {
    //         Ok(())
    //     } else {
    //         Err(())
    //     }
    // }
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
            if let Some(ref outcome) = c {
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
            c.commit(self);
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
        slot.map_or(Cow::Borrowed("<Empty>"), |inst| Cow::Owned(format!(
            "{inst}"
        )))
    )
}

impl<'a> Display for Machine<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for u in Resource::iter() {
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
    /// Number of memory load resources
    #[arg(long, default_value_t = 1)]
    load_slots: usize,
    /// Number of memory store resources
    #[arg(long, default_value_t = 1)]
    store_slots: usize,
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
    /// Number of general-purpose registers
    #[arg(long, default_value_t = 64)]
    num_regs: usize,
    /// Number of branch registers
    #[arg(long, default_value_t = 8)]
    num_bregs: usize,
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
    #[error("At least two general registers are required")]
    NotEnoughRegisters,
    #[error("At least one branch register is required")]
    NotEnoughBranchRegisters,
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
    pub fn new(args: &Args) -> Result<Self, ParameterError> {
        if args.mem_size < 4 {
            return Err(ParameterError::NotEnoughMemory(args.mem_size));
        }
        if (args.mem_size % 4) != 0 {
            return Err(ParameterError::BadMemoryAlign(args.mem_size));
        }
        if args.num_regs < 2 {
            return Err(ParameterError::NotEnoughRegisters);
        }
        if args.num_bregs < 1 {
            return Err(ParameterError::NotEnoughBranchRegisters);
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
        if args.load_slots == 0 {
            return Err(ParameterError::NotEnoughUnit(Resource::Load));
        }
        if args.store_slots == 0 {
            return Err(ParameterError::NotEnoughUnit(Resource::Store));
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
            gregs: regs,
            bregs: vec![0u32; args.num_bregs],
            num_slots: args.num_slots,
            num_alus: args.alu_slots,
            alu_latency: args.alu_latency,
            num_muls: args.mul_slots,
            mul_latency: args.mul_latency,
            num_loads: args.load_slots,
            num_stores: args.store_slots,
            load_latency: args.load_latency,
            store_latency: args.store_latency,
            alus: Vec::with_capacity(args.alu_slots),
            loads: Vec::with_capacity(args.load_slots),
            stores: Vec::with_capacity(args.store_slots),
            muls: Vec::with_capacity(args.mul_slots),
            pending_reads: HashMap::new(),
            pending_writes: HashMap::new(),
        })
    }
}

#[derive(Error, Debug, Clone, PartialEq, Eq, Hash, Diagnostic)]
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

#[derive(Error, Debug, Clone, PartialEq, Eq, Diagnostic)]
#[error("Parsing Failure")]
struct ParseDiagnostic {
    element: &'static str,
    source: ParseError,
    #[label = "{element}"]
    problem: SourceSpan,
    #[source_code]
    src: NamedSource<String>,
    #[help]
    help: Option<String>,
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
    let lines: Vec<(usize, SourceSpan, &str)> =
        backing
            .lines()
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
    let inst_lines = lines
        .iter()
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
            let inst: Instruction = line.parse().map_err(|p: WithContext<ParseError>| {
                let problem = p.span_context(span.offset());
                let element = p.source.element();
                let source = p.source;
                ParseDiagnostic {
                    element,
                    problem,
                    source,
                    src: NamedSource::new(&args.file, backing.clone()),
                    help: p.help,
                }
            })?;
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
                src: NamedSource::new(&args.file, backing.clone()),
                prev,
                curr,
                violation: *e,
            })?;
        }
        if args.verbose {
            println!("Machine state at the end of cycle {cycle}:\n{machine}");
        }
    }
    println!("{} in {} cycles", machine.gregs[4], groups.len());
    Ok(())
}
