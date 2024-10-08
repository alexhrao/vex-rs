//! Vex Simulator, written in Rust

use clap::Parser;
use machine::{Machine, MemoryValue, Violation, OUTPUT_REG};
use miette::{Diagnostic, IntoDiagnostic, NamedSource, SourceSpan};
use operation::WithContext;
use std::fs;
use std::{borrow::Cow, fmt::Display};
use thiserror::Error;

mod machine;
mod operation;

use operation::{Instruction, Kind, Location, Operation, ParseError};

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
            // Alignment has already been checked
            Location::Memory(m, a) => {
                machine
                    .write_memory(m, MemoryValue::new(self.value, a))
                    .unwrap();
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

#[derive(clap::Parser, Debug, Clone, PartialEq, Eq, Hash)]
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
    /// Number of general-purpose registers. This is in addition to
    /// the zero register, $r0.0
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
    element: Cow<'static, str>,
    source: ParseError,
    #[label = "{element}"]
    problem: SourceSpan,
    #[source_code]
    src: NamedSource<String>,
    #[help]
    help: Option<Cow<'static, str>>,
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

    let mut insts: Vec<Instruction> = vec![];
    let mut inst = Instruction::default();
    let inst_lines = lines
        .iter()
        .skip_while(|&&(_, _, l)| l != "#### BEGIN BASIC BLOCK ####")
        .skip(1)
        .take_while(|&&(_, _, l)| l != "#### END BASIC BLOCK ####")
        .filter(|&&(_, _, l)| !l.trim_start().starts_with('#'));
    for &(lineno, span, line) in inst_lines {
        if line.trim_start().starts_with(";;") {
            // eject
            insts.push(inst);
            inst = Instruction::default();
        } else {
            let op: Operation = line.parse().map_err(|p: WithContext<ParseError>| {
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
            inst.0.push(op.with_context((lineno, span)));
        }
    }
    // Push one more to ensure we have a cycle to clear the last of the pending
    insts.push(Instruction::default());
    let insts = insts;

    let mut machine: Machine<'_> = (&args).try_into().into_diagnostic()?;

    for (cycle, i) in insts.iter().enumerate().map(|(c, i)| (c + 1, i)) {
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
            println!("{} slots filled:", i.0.len());
            for (s, inst) in i.0.iter().enumerate() {
                println!("\t{s}: {inst}");
            }
        }
        // Issue instructions to their respective resources
        if let Err(e) = machine.issue(&i.0, cycle) {
            let span = |s: (usize, SourceSpan)| s.1;
            let (prev, curr) = match &*e {
                Violation::ResourceOverflow(i, _)
                | Violation::TooManyOperations(i)
                | Violation::RegisterOutOfBounds(i, _)
                | Violation::MemoryOutOfBounds(i, _, _)
                | Violation::UnalignedAddress(i, _, _)
                | Violation::InvalidWrite(i, _) => (None, i.ctx.map(span)),
                Violation::RegisterContention(_, c) | Violation::MemoryContention(c) => {
                    let (i1, i2) = c.get_insts();
                    (i1.ctx.map(span), i2.ctx.map(span))
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
    println!("{} in {} cycles", machine[OUTPUT_REG], insts.len());
    Ok(())
}
