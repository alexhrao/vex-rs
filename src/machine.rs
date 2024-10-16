use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::HashMap,
    fmt::Display,
    iter,
    num::Wrapping,
    ops::{Index, IndexMut},
};

use bon::Builder;
use strum::IntoEnumIterator;
use thiserror::Error;

use crate::{
    operation::{
        Action, Alignment, DecodeError, Instruction, Location, Operation, Outcome, Register,
        RegisterClass, Resource,
    },
    program::Program,
};

/// The zero register. This one should **never** be written to
pub const ZERO_REG: Register = Register {
    cluster: 0,
    num: 0,
    class: RegisterClass::General,
};

/// The output register. This is where the final numeric result goes
pub const OUTPUT_REG: Register = Register {
    cluster: 0,
    num: 4,
    class: RegisterClass::General,
};

/// An issued operation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Issued<'a> {
    source: Pending<'a>,
    results: Vec<Outcome>,
}

impl<'a> Display for Issued<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{} instruction issued in cycle {}. ",
            self.source.operation.action.code(),
            self.source.issued,
        ))?;
        let outcome = self
            .results
            .iter()
            .map(|o| format!("Result: {o}"))
            .collect::<Vec<_>>()
            .join("; ");
        f.write_str(&outcome)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pending<'a> {
    issued: Wrapping<usize>,
    finished: Wrapping<usize>,
    operation: &'a Operation,
}

impl<'a> PartialOrd for Pending<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a> Ord for Pending<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let ord = self.issued.cmp(&other.issued);
        if ord == Ordering::Equal {
            self.finished.cmp(&other.finished)
        } else {
            ord
        }
    }
}

/// A type of memory or register contention
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ContentionType {
    /// The first operation is reading from the same location that the second
    /// operation is writing to
    ReadWrite(Operation, Operation),
    /// The first operation is writing to the same location that the second
    /// operation is reading from
    WriteRead(Operation, Operation),
    /// Both operations are writing to the same location
    WriteWrite(Operation, Operation),
}

impl ContentionType {
    /// Get the instructions associated with this contention
    pub const fn get_insts(&self) -> (&Operation, &Operation) {
        match self {
            Self::ReadWrite(i1, i2) | Self::WriteRead(i1, i2) | Self::WriteWrite(i1, i2) => {
                (i1, i2)
            }
        }
    }
}

/// A runtime violation
#[derive(Debug, Clone, PartialEq, Eq, Error, Hash)]
pub enum Violation {
    /// Too many operations were contained in the same instruction
    TooManyOperations(Operation),
    /// The given operation overflowed the given resource
    ResourceOverflow(Operation, Resource),
    /// Two operations contested for rights to a register
    RegisterContention(Register, ContentionType),
    /// Two operations contested for rights to memory
    MemoryContention(ContentionType),
    /// A non-existent register was referenced
    RegisterOutOfBounds(Operation, Register),
    /// Memory was read before it was initialized
    UninitializedMemory(Operation, usize, Alignment),
    /// A value's address did not respect the necessary alignment
    UnalignedAddress(Operation, usize, Alignment),
    /// A write to a read-only location was attempted
    InvalidWrite(Operation, Location),
    /// An intercluster `SEND` or `RECV` did not have a pair
    UnpairedIntercluster(Operation, u32),
    /// Multiple `SEND`s or `RECV`s contested for the same intercluster path
    PathContention(Operation, Operation, u32),
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
                    "The {} writes to register {r}, but so does the {}",
                    i1.summary(),
                    i2.summary()
                ),
                ContentionType::ReadWrite(i1, i2) | ContentionType::WriteRead(i2, i1) => {
                    format!(
                        "The {} reads from register {r}, but the {} writes to it",
                        i1.summary(),
                        i2.summary()
                    )
                }
            },
            Self::ResourceOverflow(i, r) => format!("The {} overflowed the {r} unit", i.summary()),
            Self::TooManyOperations(i) => {
                format!("The {} overflowed max number of slots", i.summary())
            }
            Self::RegisterOutOfBounds(_, r) => {
                format!("The register {r} exceeds the register bank bounds")
            }
            Self::UninitializedMemory(_, m, a) => {
                format!("The {a}-aligned address {m} exceeds the bounds of memory when")
            }
            Self::UnalignedAddress(_, m, a) => {
                format!("The address {m} is not correctly aligned to the {a} boundary")
            }
            Self::InvalidWrite(_, loc) => {
                format!("The instruction tried to write to {loc}")
            }
            Self::UnpairedIntercluster(_, path) => {
                format!("The instruction specified path 0x{path:x}, but no other instruction referenced this path")
            }
            Self::PathContention(_, _, path) => {
                format!("The path 0x{path:x} was referenced in the same manner more than once")
            }
        })?;
        f.write_str(". This has undefined behavior and is not allowed.")
    }
}

/// A value from memory that respects alignment
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryValue {
    /// A single byte
    Byte(u8),
    /// A single short
    Half(u16),
    /// A single word
    Word(u32),
}

impl MemoryValue {
    /// Get the value as a 32-bit unsigned integer
    pub fn as_u32(self) -> u32 {
        match self {
            Self::Byte(b) => u32::from(b),
            Self::Half(h) => u32::from(h),
            Self::Word(w) => w,
        }
    }
    /// Create a new value using the given alignment
    pub const fn new(value: u32, size: Alignment) -> Self {
        match size {
            #[allow(clippy::cast_possible_truncation)]
            Alignment::Byte => Self::Byte(value as u8),
            #[allow(clippy::cast_possible_truncation)]
            Alignment::Half => Self::Half(value as u16),
            Alignment::Word => Self::Word(value),
        }
    }
    const fn alignment(self) -> Alignment {
        match self {
            Self::Byte(_) => Alignment::Byte,
            Self::Half(_) => Alignment::Half,
            Self::Word(_) => Alignment::Word,
        }
    }
}

impl From<&[u8]> for MemoryValue {
    fn from(value: &[u8]) -> Self {
        match value.len() {
            1 => Self::Byte(value[0]),
            2 => Self::Half(u16::from_be_bytes(value.try_into().unwrap())),
            4 => Self::Word(u32::from_be_bytes(value.try_into().unwrap())),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Cluster {
    general: Vec<u32>,
    branch: Vec<u32>,
}

/// Cluster configuration
#[derive(Debug)]
pub struct ClusterConfig {
    /// Number of general-purpose registers this cluster should have
    pub regs: usize,
    /// Number of branch registers this cluster should have
    pub branch: usize,
}

impl TryFrom<ClusterConfig> for Cluster {
    type Error = ConstructionError;
    fn try_from(value: ClusterConfig) -> Result<Self, Self::Error> {
        if value.branch <= 1 || value.regs == 0 {
            Err(ConstructionError::ZeroRegisters)
        } else {
            Ok(Self {
                general: vec![0u32; value.regs],
                branch: vec![0u32; value.branch],
            })
        }
    }
}

/// Arguments for creating a machine
#[derive(Builder)]
pub struct Args<'a> {
    /// The cluster(s) this machine will have
    pub clusters: Vec<ClusterConfig>,
    /// The instruction width
    pub num_slots: usize,
    /// The number of Arithmetic & Logic units
    pub num_alus: usize,
    /// The number of Multipliers
    pub num_muls: usize,
    /// The number of memory load units
    pub num_loads: usize,
    /// The number of memory store units
    pub num_stores: usize,
    /// The number of units available for intercluster copies
    pub num_copies: usize,
    /// Latency for Arithmetic & Logic operations
    pub alu_latency: usize,
    /// Latency for multiplication
    pub mul_latency: usize,
    /// Latency for store operations
    pub store_latency: usize,
    /// Latency for load operations
    pub load_latency: usize,
    /// Latency for intercluster copy operations
    pub copy_latency: usize,
    /// The program to load into this machine
    pub program: &'a Program,
}

/// Problems during machine construction
#[derive(Debug, Clone, PartialEq, Eq, Hash, Error)]
pub enum ConstructionError {
    /// No latency can ever be 0
    #[error("Resource {0} must have non-zero latency")]
    ZeroLatency(Resource),
    /// All resources require at least one unit
    #[error("Resource {0} must have at least one unit")]
    ZeroCapacity(Resource),
    /// A machine requires at least one cluster
    #[error("You must have at least one cluster")]
    ZeroClusters,
    /// All clusters must have ample registers
    #[error("All clusters must have a non-zero number of general and branch registers")]
    ZeroRegisters,
    /// You must provide an instruction width of at least one operation
    #[error("You must have at least one operation slot")]
    ZeroSlots,
}

impl<'a> TryFrom<Args<'a>> for Machine<'a> {
    type Error = ConstructionError;
    fn try_from(value: Args<'a>) -> Result<Self, Self::Error> {
        let clusters = value
            .clusters
            .into_iter()
            .map(Cluster::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        if value.alu_latency == 0 {
            return Err(ConstructionError::ZeroLatency(Resource::Arithmetic));
        }
        if value.load_latency == 0 {
            return Err(ConstructionError::ZeroLatency(Resource::Load));
        }
        if value.mul_latency == 0 {
            return Err(ConstructionError::ZeroLatency(Resource::Multiplication));
        }
        if value.store_latency == 0 {
            return Err(ConstructionError::ZeroLatency(Resource::Store));
        }
        if value.copy_latency == 0 {
            return Err(ConstructionError::ZeroLatency(Resource::Copy));
        }
        if value.num_alus == 0 {
            return Err(ConstructionError::ZeroCapacity(Resource::Arithmetic));
        }
        if value.num_loads == 0 {
            return Err(ConstructionError::ZeroCapacity(Resource::Load));
        }
        if value.num_muls == 0 {
            return Err(ConstructionError::ZeroCapacity(Resource::Multiplication));
        }
        if value.num_stores == 0 {
            return Err(ConstructionError::ZeroCapacity(Resource::Store));
        }
        if value.num_slots == 0 {
            return Err(ConstructionError::ZeroSlots);
        }
        if value.num_copies == 0 {
            return Err(ConstructionError::ZeroCapacity(Resource::Copy));
        }
        Ok(Self {
            cycle: Wrapping(0),
            pc: 0,
            alu_latency: value.alu_latency,
            alus: Vec::with_capacity(value.num_alus),
            clusters,
            load_latency: value.load_latency,
            loads: Vec::with_capacity(value.num_loads),
            memory: HashMap::new(),
            num_slots: value.num_slots,
            mul_latency: value.mul_latency,
            muls: Vec::with_capacity(value.num_muls),
            num_alus: value.num_alus,
            num_loads: value.num_loads,
            num_muls: value.num_muls,
            num_stores: value.num_stores,
            // Multiply by 2, since they come in pairs
            num_copies: value.num_copies * 2,
            store_latency: value.store_latency,
            stores: Vec::with_capacity(value.num_stores),
            copy_latency: value.copy_latency,
            copies: Vec::with_capacity(value.num_copies),
            pending_reads: HashMap::new(),
            pending_writes: HashMap::new(),
            program: value.program,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum PathSignal {
    Sent(u32),
    Waiting(usize),
}

/// Abstract Simulation Machine
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Machine<'a> {
    cycle: Wrapping<usize>,
    pc: usize,
    num_slots: usize,
    num_alus: usize,
    num_muls: usize,
    num_loads: usize,
    num_stores: usize,
    num_copies: usize,
    clusters: Vec<Cluster>,
    alus: Vec<Issued<'a>>,
    muls: Vec<Issued<'a>>,
    loads: Vec<Issued<'a>>,
    stores: Vec<Issued<'a>>,
    copies: Vec<Issued<'a>>,
    alu_latency: usize,
    mul_latency: usize,
    store_latency: usize,
    load_latency: usize,
    copy_latency: usize,
    memory: HashMap<usize, u8>,
    /// Pending reads. The key is the location read, while
    /// the value is the operation responsible for the read,
    /// plus the cycle in which this read will have finished
    pending_reads: HashMap<Location, Vec<Pending<'a>>>,
    /// Pending writes. The key is the location written to, while
    /// the value is the operation responsible for the write,
    /// plus cycle in which this write will have finished
    pending_writes: HashMap<Location, Pending<'a>>,
    /// The program I'm reading from. Interestingly, the Machine **cannot**
    /// own this program. What we're saying here is that this program
    /// will **not** change over the lifetime of this machine. That means
    /// we can take references to instructions within this program freely,
    /// because such references will only live as long as the machine (which
    /// is the same as the program). If we owned it, those references would
    /// either be invalid after we exited the cycle (since the reference was
    /// taken in the program), or we'd need a mutable borrow over the lifetime
    /// of this Machine, because otherwise a different mutable borrow of this
    /// machine could invalidate those program references
    program: &'a Program,
}

impl<'a> Index<Register> for Machine<'a> {
    type Output = u32;
    fn index(&self, index: Register) -> &Self::Output {
        let cluster = &self.clusters[index.cluster];
        match index.class {
            RegisterClass::Branch => &cluster.branch[index.num],
            RegisterClass::General => &cluster.general[index.num],
            RegisterClass::Link => todo!(),
        }
    }
}

impl<'a> IndexMut<Register> for Machine<'a> {
    fn index_mut(&mut self, index: Register) -> &mut Self::Output {
        let cluster = &mut self.clusters[index.cluster];
        match index.class {
            RegisterClass::Branch => &mut cluster.branch[index.num],
            RegisterClass::General => &mut cluster.general[index.num],
            RegisterClass::Link => todo!(),
        }
    }
}

impl<'a> Machine<'a> {
    pub(crate) const fn latency(&self, resource: Resource) -> usize {
        match resource {
            Resource::Arithmetic => self.alu_latency,
            Resource::Multiplication => self.mul_latency,
            Resource::Load => self.load_latency,
            Resource::Store => self.store_latency,
            Resource::Copy => self.copy_latency,
        }
    }
    pub(crate) const fn capacity(&self, resource: Resource) -> usize {
        match resource {
            Resource::Arithmetic => self.num_alus,
            Resource::Load => self.num_loads,
            Resource::Store => self.num_stores,
            Resource::Multiplication => self.num_muls,
            Resource::Copy => self.num_copies,
        }
    }
    pub(crate) const fn resource(&self, resource: Resource) -> &Vec<Issued<'a>> {
        match resource {
            Resource::Arithmetic => &self.alus,
            Resource::Load => &self.loads,
            Resource::Store => &self.stores,
            Resource::Multiplication => &self.muls,
            Resource::Copy => &self.copies,
        }
    }
    fn resource_mut(&mut self, resource: Resource) -> &mut Vec<Issued<'a>> {
        match resource {
            Resource::Arithmetic => &mut self.alus,
            Resource::Load => &mut self.loads,
            Resource::Store => &mut self.stores,
            Resource::Multiplication => &mut self.muls,
            Resource::Copy => &mut self.copies,
        }
    }
    pub(crate) fn get_reg(&self, r: Register) -> Result<u32, DecodeError> {
        let c = self
            .clusters
            .get(r.cluster)
            .ok_or(DecodeError::InvalidRegister(r))?;

        match r.class {
            RegisterClass::Branch => c.branch.get(r.num),
            RegisterClass::General => c.general.get(r.num),
            RegisterClass::Link => todo!(),
        }
        .copied()
        .ok_or(DecodeError::InvalidRegister(r))
    }
    /// Read a value from memory. This will error if the address doesn't have
    /// the correct [`Alignment`], or if any byte in the address range is uninitialized
    pub fn read_memory(&self, addr: usize, align: Alignment) -> Result<MemoryValue, DecodeError> {
        if addr.rem_euclid(align.offset()) != 0 {
            Err(DecodeError::MisalignedAccess(addr, align))
        } else {
            let bytes = (addr..addr + align.offset())
                .map(|a| {
                    self.memory
                        .get(&a)
                        .copied()
                        .ok_or(DecodeError::UninitializedRead(a, align))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(MemoryValue::from(bytes.as_ref()))
        }
    }
    /// Write a value to memory. This will error if the address doesn't have
    /// the correct [`Alignment`].
    pub fn write_memory(&mut self, addr: usize, value: MemoryValue) -> Result<(), DecodeError> {
        let align = value.alignment();
        if addr.rem_euclid(align.offset()) != 0 {
            Err(DecodeError::MisalignedAccess(addr, align))
        } else {
            let value = match value {
                MemoryValue::Byte(b) => b as u32,
                MemoryValue::Half(h) => h as u32,
                MemoryValue::Word(w) => w,
            }
            .to_be_bytes();
            for (a, v) in (addr..addr + align.offset()).zip(value.into_iter()) {
                self.memory.insert(a, v);
            }
            Ok(())
        }
    }
    /// Get the instruction that is about to be issued, if any. This will return `None`
    /// only if there are no more instructions to execute.
    pub fn on_deck(&self) -> Option<&'a Instruction> {
        self.program.insts.get(self.pc)
    }
    pub fn pending(&self) -> impl Iterator<Item = &Pending<'a>> {
        self.pending_writes
            .values()
            .chain(self.pending_reads.values().flat_map(|v| v.iter()))
    }
    /// Get the current cycle
    pub fn cycle(&self) -> usize {
        self.cycle.0
    }
    /// Get the instruction width
    pub fn slots(&self) -> usize {
        self.num_slots
    }
    /// Run the program to completion
    pub fn run(&mut self) -> Result<(), Box<Violation>> {
        loop {
            if self.on_deck().is_none() {
                break;
            }
            self.step()?;
        }
        Ok(())
    }
    pub fn step(&mut self) -> Result<Vec<Issued<'a>>, Box<Violation>> {
        if self.on_deck().is_none() {
            return Ok(vec![]);
        }
        let committed = self.commit();
        self.issue()?;
        Ok(committed)
    }
    fn issue(&mut self) -> Result<bool, Box<Violation>> {
        let ops = match self.on_deck() {
            None => return Ok(false),
            Some(i) => i.0.iter().enumerate(),
        };
        // The current cycle
        let cycle = self.cycle;
        // What paths I have seen; value is the last operation to use that path
        let mut seen_sends: HashMap<u32, &Operation> = HashMap::new();
        let mut seen_recvs: HashMap<u32, &Operation> = HashMap::new();
        let mut paths: HashMap<u32, (PathSignal, &Operation)> = HashMap::new();
        for (count, op) in ops {
            if count > self.num_slots {
                return Err(Box::new(Violation::TooManyOperations(op.clone())));
            }
            // If any output would write to the zero register, bail
            for out in op.action.outputs() {
                if matches!(out, Location::Register(ZERO_REG)) {
                    return Err(Box::new(Violation::InvalidWrite(op.clone(), out)));
                }
            }
            // if any input is in our list of pending writes, bail
            for l in op.action.inputs() {
                if let Some(&Pending {
                    operation: prev, ..
                }) = self.pending_writes.get(&l)
                {
                    // So, someone is writing to this location. That's a problem
                    return Err(Box::new(match l {
                        Location::Memory(_, _) => Violation::MemoryContention(
                            ContentionType::WriteRead(prev.clone(), op.clone()),
                        ),
                        Location::Register(r) => Violation::RegisterContention(
                            r,
                            ContentionType::WriteRead(prev.clone(), op.clone()),
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
            // let c = op.action.decode(self);
            // Now, we are writing to something. We need to check BOTH pending reads and pending writes

            // Decode step will check if the inputs or the outputs exceed bounds or are not aligned
            let mut results = op.action.decode(self).map_err(|de| {
                let op = op.clone();
                Box::new(match de {
                    DecodeError::UninitializedRead(addr, align) => {
                        Violation::UninitializedMemory(op, addr, align)
                    }
                    DecodeError::InvalidRegister(r) => Violation::RegisterOutOfBounds(op, r),
                    DecodeError::MisalignedAccess(addr, align) => {
                        Violation::UnalignedAddress(op, addr, align)
                    }
                })
            })?;
            // We'll need this later
            let dsts: Vec<_> = results.iter().map(|r| r.dst).collect();
            for c in &results {
                if let Some(&Pending {
                    operation: prev, ..
                }) = self.pending_writes.get(&c.dst)
                {
                    return Err(Box::new(match c.dst {
                        Location::Memory(_, _) => Violation::MemoryContention(
                            ContentionType::WriteWrite(prev.clone(), op.clone()),
                        ),
                        Location::Register(r) => Violation::RegisterContention(
                            r,
                            ContentionType::WriteWrite(prev.clone(), op.clone()),
                        ),
                    }));
                }
                if let Some(&Pending {
                    operation: prev, ..
                }) = self.pending_reads.get(&c.dst).and_then(|v| v.iter().min())
                {
                    return Err(Box::new(match c.dst {
                        Location::Memory(_, _) => Violation::MemoryContention(
                            ContentionType::ReadWrite(prev.clone(), op.clone()),
                        ),
                        Location::Register(r) => Violation::RegisterContention(
                            r,
                            ContentionType::ReadWrite(prev.clone(), op.clone()),
                        ),
                    }));
                }
            }

            let r = op.action.kind();
            let latency = self.latency(r);
            let cap = self.capacity(r);

            if let Action::Send(ref args) = op.action {
                let value = self[args.src];
                if let Some(&prev) = seen_sends.get(&args.path) {
                    // prev was a send on this path. Bail
                    return Err(Box::new(Violation::PathContention(
                        prev.clone(),
                        op.clone(),
                        args.path,
                    )));
                }
                seen_sends.insert(args.path, op);
                if let Some((sr, op1)) = paths.remove(&args.path) {
                    match sr {
                        PathSignal::Waiting(idx) => {
                            let unit = self.resource_mut(r);
                            // Resolve that result
                            unit[idx].results[0].value = value;
                        }
                        PathSignal::Sent(_) => {
                            return Err(Box::new(Violation::PathContention(
                                op1.clone(),
                                op.clone(),
                                args.path,
                            )));
                        }
                    };
                } else {
                    // Haven't seen this one yet. Just add it
                    paths.insert(args.path, (PathSignal::Sent(self[args.src]), op));
                }
            } else if let Action::Recv(ref args) = op.action {
                if let Some(&prev) = seen_recvs.get(&args.path) {
                    // prev was a send on this path. Bail
                    return Err(Box::new(Violation::PathContention(
                        prev.clone(),
                        op.clone(),
                        args.path,
                    )));
                }
                seen_recvs.insert(args.path, op);
                if let Some((sr, op1)) = paths.remove(&args.path) {
                    match sr {
                        PathSignal::Waiting(_) => {
                            return Err(Box::new(Violation::PathContention(
                                op1.clone(),
                                op.clone(),
                                args.path,
                            )));
                        }
                        PathSignal::Sent(v) => {
                            results[0].value = v;
                        }
                    }
                } else {
                    // I haven't seen a send for this yet. Add the next index as a bookmark
                    paths.insert(args.path, (PathSignal::Waiting(self.resource(r).len()), op));
                }
            }

            let units = self.resource_mut(r);
            if units.len() == cap {
                return Err(Box::new(Violation::ResourceOverflow(op.clone(), r)));
            }
            let pending = Pending {
                operation: op,
                issued: cycle,
                finished: cycle + Wrapping(latency),
            };
            units.push(Issued {
                source: pending,
                results,
            });
            // At this point, we need to update our pending reads and pending writes
            for l in op.action.inputs() {
                self.pending_reads
                    .entry(l.sanitize())
                    .or_default()
                    .push(pending);
            }
            for d in dsts {
                // Should have already been checked
                if let Some(Pending {
                    operation: prev, ..
                }) = self.pending_writes.insert(d.sanitize(), pending)
                {
                    panic!("Pending writes should not have been populated, but was with {prev}");
                }
            }
        }
        if let Some((&p, &(_, op))) = paths.iter().next() {
            Err(Box::new(Violation::UnpairedIntercluster(op.clone(), p)))
        } else {
            self.cycle += 1;
            self.pc += 1;
            Ok(true)
        }
    }
    fn commit(&mut self) -> Vec<Issued<'a>> {
        let cycle = self.cycle;
        let mut committed: Vec<Issued<'a>> = vec![];
        for r in Resource::iter() {
            let mut kept = vec![];
            let resource = self.resource_mut(r);
            for i in resource.drain(..) {
                if i.source.finished == cycle {
                    // Note that any contention was found in issuance
                    committed.push(i);
                } else {
                    kept.push(i);
                }
            }
            *resource = kept;
        }

        // Pending reads and writes
        for c in committed.iter().flat_map(|r| r.results.iter()) {
            c.commit(self);
            assert!(
                self.pending_writes.remove(&c.dst).is_some(),
                "Removed write was not marked as pending: {c}"
            );
        }
        for pending in self.pending_reads.values_mut() {
            pending.retain(|p| p.finished > cycle);
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
        // 5. That we contain enough instructions to finish out (?)
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

#[cfg(test)]
pub(crate) mod test {
    use std::collections::HashMap;

    use crate::{
        operation::{Action, DecodeError, Instruction, Operation, Outcome},
        program::Program,
    };

    use super::{Args, ClusterConfig, Machine};
    pub fn decode<S>(action: Action, setup: S) -> Result<Vec<Outcome>, DecodeError>
    where
        S: FnOnce(&mut Machine),
    {
        let p = Program {
            labels: HashMap::new(),
            insts: vec![Instruction(vec![Operation {
                ctx: None,
                cluster: 0,
                action: action.clone(),
            }])],
        };
        let mut machine = test_machine(&p);
        setup(&mut machine);
        action.decode(&machine)
    }
    pub fn test_machine<'a>(program: &'a Program) -> Machine<'a> {
        Args {
            alu_latency: 1,
            clusters: vec![ClusterConfig {
                branch: 128,
                regs: 128,
            }],
            copy_latency: 1,
            load_latency: 3,
            mul_latency: 2,
            num_alus: 4,
            num_copies: 1,
            num_loads: 1,
            num_muls: 2,
            num_slots: 4,
            num_stores: 1,
            store_latency: 1,
            program,
        }
        .try_into()
        .unwrap()
        // Machine {
        //     clusters: vec![Cluster {
        //         general: vec![0u32; 128],
        //         branch: vec![0u32; 128],
        //     }],
        //     memory: HashMap::new(),
        //     alus: vec![],
        //     muls: vec![],
        //     loads: vec![],
        //     stores: vec![],
        //     copies: vec![],
        //     num_slots: 4,
        //     num_alus: 4,
        //     num_muls: 2,
        //     num_loads: 1,
        //     num_stores: 1,
        //     num_copies: 1,
        //     alu_latency: 1,
        //     mul_latency: 2,
        //     store_latency: 3,
        //     load_latency: 3,
        //     copy_latency: 1,
        //     pending_reads: HashMap::new(),
        //     pending_writes: HashMap::new(),
        //     symbols: HashMap::new(),
        // }
    }
}
