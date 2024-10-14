use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::HashMap,
    fmt::Display,
    iter,
    ops::{Index, IndexMut},
};

use bon::Builder;
use strum::IntoEnumIterator;
use thiserror::Error;

use crate::operation::{
    Alignment, DecodeError, Location, Operation, Outcome, Register, RegisterClass, Resource,
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
struct Pending<'a> {
    issued: usize,
    finished: usize,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ContentionType {
    ReadWrite(Operation, Operation),
    WriteRead(Operation, Operation),
    WriteWrite(Operation, Operation),
}

impl ContentionType {
    pub const fn get_insts(&self) -> (&Operation, &Operation) {
        match self {
            Self::ReadWrite(i1, i2) | Self::WriteRead(i1, i2) | Self::WriteWrite(i1, i2) => {
                (i1, i2)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Hash)]
pub enum Violation {
    TooManyOperations(Operation),
    ResourceOverflow(Operation, Resource),
    RegisterContention(Register, ContentionType),
    MemoryContention(ContentionType),
    RegisterOutOfBounds(Operation, Register),
    MemoryOutOfBounds(Operation, usize, Alignment),
    UnalignedAddress(Operation, usize, Alignment),
    InvalidWrite(Operation, Location),
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
            Self::MemoryOutOfBounds(_, m, a) => {
                format!("The {a}-aligned address {m} exceeds the bounds of memory when")
            }
            Self::UnalignedAddress(_, m, a) => {
                format!("The address {m} is not correctly aligned to the {a} boundary")
            }
            Self::InvalidWrite(_, loc) => {
                format!("The instruction tried to write to {loc}")
            }
        })?;
        f.write_str(". This has undefined behavior and is not allowed.")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryValue {
    Byte(u8),
    Half(u16),
    Word(u32),
}

impl MemoryValue {
    pub fn as_u32(self) -> u32 {
        match self {
            Self::Byte(b) => u32::from(b),
            Self::Half(h) => u32::from(h),
            MemoryValue::Word(w) => w,
        }
    }
    pub fn new(value: u32, size: Alignment) -> Self {
        match size {
            #[allow(clippy::cast_possible_truncation)]
            Alignment::Byte => Self::Byte(value as u8),
            #[allow(clippy::cast_possible_truncation)]
            Alignment::Half => Self::Half(value as u16),
            Alignment::Word => Self::Word(value),
        }
    }
    fn alignment(self) -> Alignment {
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
    pub general: Vec<u32>,
    pub branch: Vec<u32>,
}

#[derive(Debug)]
pub struct ClusterConfig {
    pub num_regs: usize,
    pub num_branch: usize,
}

impl TryFrom<ClusterConfig> for Cluster {
    type Error = ConstructionError;
    fn try_from(value: ClusterConfig) -> Result<Self, Self::Error> {
        if value.num_branch <= 1 || value.num_regs == 0 {
            Err(ConstructionError::ZeroRegisters)
        } else {
            Ok(Self {
                general: vec![0u32; value.num_regs],
                branch: vec![0u32; value.num_branch],
            })
        }
    }
}

#[derive(Builder)]
pub struct Args {
    pub clusters: Vec<ClusterConfig>,
    pub num_slots: usize,
    pub num_alus: usize,
    pub num_muls: usize,
    pub num_loads: usize,
    pub num_stores: usize,
    pub mem_size: usize,
    pub alu_latency: usize,
    pub mul_latency: usize,
    pub store_latency: usize,
    pub load_latency: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Error)]
pub enum ConstructionError {
    #[error("Resource {0} must have non-zero latency")]
    ZeroLatency(Resource),
    #[error("Resource {0} must have non-zero latency")]
    ZeroCapacity(Resource),
    #[error("You must have at least one cluster")]
    ZeroClusters,
    #[error("All clusters must have a non-zero number of general and branch registers")]
    ZeroRegisters,
    #[error("You must have at least one operation slot")]
    ZeroSlots,
    #[error("There must be at least 4 bytes of memory")]
    BadMemory,
}

impl<'a> TryFrom<Args> for Machine<'a> {
    type Error = ConstructionError;
    fn try_from(value: Args) -> Result<Self, Self::Error> {

        let clusters = value.clusters.into_iter()
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
        if value.mem_size < 4 {
            return Err(ConstructionError::BadMemory);
        }
        Ok(Self {
            alu_latency: value.alu_latency,
            alus: Vec::with_capacity(value.num_alus),
            clusters,
            load_latency: value.load_latency,
            loads: Vec::with_capacity(value.num_loads),
            mem: vec![0u8; value.mem_size],
            num_slots: value.num_slots,
            mul_latency: value.mul_latency,
            muls: Vec::with_capacity(value.num_muls),
            num_alus: value.num_alus,
            num_loads: value.num_loads,
            num_muls: value.num_muls,
            num_stores: value.num_stores,
            store_latency: value.store_latency,
            stores: Vec::with_capacity(value.num_stores),
            pending_reads: HashMap::new(),
            pending_writes: HashMap::new(),
            symbols: HashMap::new(),
        })
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Machine<'a> {
    num_slots: usize,
    num_alus: usize,
    num_muls: usize,
    num_loads: usize,
    num_stores: usize,
    clusters: Vec<Cluster>,
    mem: Vec<u8>,
    alus: Vec<Issued<'a>>,
    muls: Vec<Issued<'a>>,
    loads: Vec<Issued<'a>>,
    stores: Vec<Issued<'a>>,
    alu_latency: usize,
    mul_latency: usize,
    store_latency: usize,
    load_latency: usize,
    /// Pending reads. The key is the location read, while
    /// the value is the operation responsible for the read,
    /// plus the cycle in which this read will have finished
    pending_reads: HashMap<Location, Vec<Pending<'a>>>,
    /// Pending writes. The key is the location written to, while
    /// the value is the operation responsible for the write,
    /// plus cycle in which this write will have finished
    pending_writes: HashMap<Location, Pending<'a>>,
    /// Symbols that map to addresses (? or are they just constants?)
    symbols: HashMap<String, usize>,
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
        }
    }
    pub(crate) const fn capacity(&self, resource: Resource) -> usize {
        match resource {
            Resource::Arithmetic => self.num_alus,
            Resource::Load => self.num_loads,
            Resource::Store => self.num_stores,
            Resource::Multiplication => self.num_muls,
        }
    }
    pub(crate) const fn resource(&self, resource: Resource) -> &Vec<Issued<'a>> {
        match resource {
            Resource::Arithmetic => &self.alus,
            Resource::Load => &self.loads,
            Resource::Store => &self.stores,
            Resource::Multiplication => &self.muls,
        }
    }
    fn resource_mut(&mut self, resource: Resource) -> &mut Vec<Issued<'a>> {
        match resource {
            Resource::Arithmetic => &mut self.alus,
            Resource::Load => &mut self.loads,
            Resource::Store => &mut self.stores,
            Resource::Multiplication => &mut self.muls,
        }
    }
    pub fn get_reg(&self, r: Register) -> Result<u32, DecodeError> {
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
    // pub fn get_reg_mut(&mut self, r: Register) -> Result<&mut u32, DecodeError> {
    //     match r.bank {
    //         RegisterType::Branch => self.bregs.get_mut(r.num),
    //         RegisterType::General => self.gregs.get_mut(r.num),
    //         RegisterType::Link => todo!(),
    //     }
    //     .ok_or(DecodeError::InvalidRegister(r))
    // }
    pub fn read_memory(&self, addr: usize, align: Alignment) -> Result<MemoryValue, DecodeError> {
        if addr.rem_euclid(align.offset()) != 0 {
            Err(DecodeError::MisalignedAccess(addr, align))
        } else {
            self.mem
                .get(addr..addr + align.offset())
                .map(MemoryValue::from)
                .ok_or(DecodeError::AddressOutOfBounds(addr, align))
        }
    }
    pub fn write_memory(&mut self, addr: usize, value: MemoryValue) -> Result<(), DecodeError> {
        let align = value.alignment();
        if addr.rem_euclid(align.offset()) != 0 {
            Err(DecodeError::MisalignedAccess(addr, align))
        } else {
            let bytes = self
                .mem
                .get_mut(addr..addr + align.offset())
                .ok_or(DecodeError::AddressOutOfBounds(addr, align))?;
            match value {
                MemoryValue::Byte(b) => bytes[0] = b,
                MemoryValue::Half(h) => bytes.copy_from_slice(&h.to_be_bytes()),
                MemoryValue::Word(w) => bytes.copy_from_slice(&w.to_be_bytes()),
            };
            Ok(())
        }
    }
    pub fn issue<I>(&mut self, ops: I, cycle: usize) -> Result<(), Box<Violation>>
    where
        I: IntoIterator<Item = &'a Operation>,
    {
        for (count, op) in ops.into_iter().enumerate() {
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
            let results = op.action.decode(self).map_err(|de| {
                let op = op.clone();
                Box::new(match de {
                    DecodeError::AddressOutOfBounds(addr, align) => {
                        Violation::MemoryOutOfBounds(op, addr, align)
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
            let units = self.resource_mut(r);
            if units.len() == cap {
                return Err(Box::new(Violation::ResourceOverflow(op.clone(), r)));
            }
            let pending = Pending {
                operation: op,
                issued: cycle,
                finished: cycle + latency,
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
        Ok(())
    }
    pub fn commit(&mut self, cycle: usize) -> Vec<Issued<'a>> {
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

    use super::{Cluster, Machine};
    pub fn test_machine<'a>() -> Machine<'a> {
        Machine {
            clusters: vec![Cluster {
                general: vec![0u32; 128],
                branch: vec![0u32; 128],
            }],
            mem: vec![0u8; 4096],
            alus: vec![],
            muls: vec![],
            loads: vec![],
            stores: vec![],
            num_slots: 4,
            num_alus: 4,
            num_muls: 2,
            num_loads: 1,
            num_stores: 1,
            alu_latency: 1,
            mul_latency: 2,
            store_latency: 3,
            load_latency: 3,
            pending_reads: HashMap::new(),
            pending_writes: HashMap::new(),
            symbols: HashMap::new(),
        }
    }
}
