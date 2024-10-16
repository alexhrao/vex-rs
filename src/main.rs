//! Vex Simulator, written in Rust
use clap::Parser;
use miette::{Diagnostic, IntoDiagnostic, NamedSource, SourceSpan};
use std::fmt::Display;
use std::fs;
use std::path::PathBuf;
use thiserror::Error;
use vex::program::Program;

use vex::machine::{self, Machine, MemoryValue, Violation, OUTPUT_REG};
use vex::operation::{Register, RegisterClass};

mod config;

const INPUT_REG: Register = Register {
    cluster: 0,
    class: RegisterClass::General,
    num: 3,
};

#[derive(clap::Parser, Debug, Clone, PartialEq, Eq, Hash)]
#[command(version)]
struct Args {
    /// Path to TOML configuration file; used for machine configuration, among
    /// other things. If not given, the default machine parameters will be
    /// used instead.
    #[arg(long, short)]
    config: Option<PathBuf>,
    /// Assert to print debugging information; useful if your code is failing
    /// to compile or producing... interesting results
    #[arg(long, short, default_value_t = false)]
    verbose: bool,
    /// Basic Block file
    file: String,
    /// Numbers (inputs for your VEX code)
    nums: Vec<u32>,
}

#[derive(Debug, Error)]
enum ParameterError {
    #[error("Configuration file error")]
    ConfigFile(#[from] config::Error),
    #[error("Machine Configuration error: {0:?}")]
    MachineConfig(#[from] machine::ConstructionError),
    #[error("Exactly 10 numbers must be provided; {0} given")]
    InvalidArguments(usize),
    #[error("Input file `{0}` not found")]
    FileNotFound(String),
}

#[derive(Error, Debug, Clone, PartialEq, Eq, Hash, Diagnostic)]
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

impl Display for ExecutionDiagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self.violation {
            Violation::MemoryContention(_) => "Memory contention",
            Violation::InvalidWrite(_, _) => "Wrote to unwriteable location",
            Violation::UninitializedMemory(_, _, _) | Violation::UnalignedAddress(_, _, _) => {
                "Invalid memory access"
            }
            Violation::PathContention(_, _, _) => "Cluster path contention",
            Violation::RegisterContention(_, _) => "Register contention",
            Violation::RegisterOutOfBounds(_, _) => "Out-of-bounds register access",
            Violation::ResourceOverflow(_, _) => "Resource overflow",
            Violation::TooManyOperations(_) => "Instruction width overflow",
            Violation::UnpairedIntercluster(_, _) => "Cluster path mismatch",
        })
    }
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
        // Sanitize tabs into four spaces
        .map(|s| s.trim_end().replace('\t', "    "))
        .collect::<Vec<_>>()
        .join("\n");


    let program: Program = backing.parse().map_err(|b: vex::program::ParseError| {
        b.as_diagnostic(NamedSource::new(&args.file, backing.clone()))
    })?;
    let mut machine: Machine<'_> = {
        if args.nums.len() != 10 {
            return Err(ParameterError::InvalidArguments(args.nums.len())).into_diagnostic();
        }
        let cfg = match &args.config {
            Some(p) => config::get_config(p).into_diagnostic()?,
            None => config::Config::default(),
        };
        let mut machine: Machine = cfg
            .as_machine_args(&program)
            .try_into()
            .map_err(ParameterError::MachineConfig)
            .into_diagnostic()?;
        for (m, n) in (0x18..=0x2c).step_by(4).zip(args.nums.iter().skip(1)) {
            machine.write_memory(m, MemoryValue::Word(*n)).unwrap();
        }
        machine
            .write_memory(0x30, MemoryValue::Word(args.nums[8]))
            .unwrap();
        machine[INPUT_REG] = args.nums[9];
        machine
    };
    loop {
        let cycle = machine.cycle();
        if args.verbose {
            println!("=== Starting cycle {cycle} ===");
        }
        // What is about to be issued?
        if args.verbose {
            if let Some(i) = machine.on_deck() {
                println!("slots ({}/{}):", i.0.len(), machine.slots());
                for (s, inst) in i.0.iter().enumerate() {
                    println!("\t{s}: {inst}");
                }
            }
        }
        match machine.step() {
            Err(e) => {
                let span = |s: (usize, SourceSpan)| s.1;
                let (prev, curr) = match &*e {
                    Violation::ResourceOverflow(i, _)
                    | Violation::TooManyOperations(i)
                    | Violation::RegisterOutOfBounds(i, _)
                    | Violation::UninitializedMemory(i, _, _)
                    | Violation::UnalignedAddress(i, _, _)
                    | Violation::InvalidWrite(i, _)
                    | Violation::UnpairedIntercluster(i, _) => (None, i.ctx.map(span)),
                    Violation::PathContention(i1, i2, _) => (i1.ctx.map(span), i2.ctx.map(span)),
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
            Ok(resolved) => {
                if args.verbose {
                    println!("{} resolved in cycle {cycle}:", resolved.len());
                    for r in resolved {
                        println!("\t* {r}");
                    }
                }
            }
        }
        if args.verbose {
            println!("Machine state at the end of cycle {cycle}:\n{machine}");
        }
        // If nobody's on deck, I'm finished
        if machine.on_deck().is_none() {
            if args.verbose {
                println!("=== No more instructions ===");
            }
            break;
        }
    }
    // At this point, the machine should not have anything in flight
    if machine.pending().inspect(|p| println!("{p:?}")).count() > 0 {
        miette::bail!("Machine was stopped with operations in flight");
    }
    println!("{} in {} cycles", machine[OUTPUT_REG], machine.cycle());
    Ok(())
}
