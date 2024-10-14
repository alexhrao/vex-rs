//! Vex Simulator, written in Rust
use clap::Parser;
use miette::{Diagnostic, IntoDiagnostic, NamedSource, SourceSpan};
use std::borrow::Cow;
use std::fs;
use std::path::PathBuf;
use thiserror::Error;

use vex::operation::{Instruction, Operation, ParseError, Register, RegisterClass, WithContext};
use vex::machine::{self, Machine, MemoryValue, Violation, OUTPUT_REG};

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

#[derive(Debug, thiserror::Error)]
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

impl<'a> TryFrom<&Args> for Machine<'a> {
    type Error = ParameterError;
    fn try_from(args: &Args) -> Result<Self, Self::Error> {
        if args.nums.len() != 10 {
            return Err(ParameterError::InvalidArguments(args.nums.len()));
        }
        let cfg: machine::Args = match &args.config {
            Some(p) => config::get_config(p)?.into(),
            None => config::Config::default().into()
        };
        let mut machine: Machine = cfg.try_into().map_err(ParameterError::MachineConfig)?;
        for (m, n) in (0x18..=0x2c).step_by(4).zip(args.nums.iter().skip(1)) {
            machine.write_memory(m, MemoryValue::Word(*n)).unwrap();
        }
        machine.write_memory(0x30, MemoryValue::Word(args.nums[8])).unwrap();
        machine[INPUT_REG] = args.nums[9];
        Ok(machine)
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
    element: Cow<'static, str>,
    source: ParseError,
    #[label = "{element}"]
    problem: SourceSpan,
    #[source_code]
    src: NamedSource<String>,
    #[help]
    help: Option<Cow<'static, str>>,
}

fn parse_insts(backing: &str, args: &Args) -> Result<Vec<Instruction>, Box<ParseDiagnostic>> {
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
                    src: NamedSource::new(&args.file, backing.to_owned()),
                    help: p.help,
                }
            })?;
            inst.0.push(op.with_context((lineno, span)));
        }
    }
    // Push one more to ensure we have a cycle to clear the last of the pending
    insts.push(Instruction::default());
    Ok(insts)
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

    let insts = parse_insts(&backing, &args).map_err(|b| *b)?;

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
