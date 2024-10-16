use std::{borrow::Cow, collections::HashMap, str::FromStr, sync::LazyLock};

use miette::{Diagnostic, NamedSource, Report, SourceSpan};
use regex::Regex;
use thiserror::Error;

use crate::operation::{self, Instruction, Operation, WithContext};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub(crate) insts: Vec<Instruction>,
    pub(crate) labels: HashMap<String, (usize, SourceSpan)>,
}

#[derive(Debug, Error, Clone)]
#[error("")]
pub struct LabelContext {
    current: SourceSpan,
    previous: Option<SourceSpan>,
    help: Option<Cow<'static, str>>,
}

#[derive(Debug, Error, Clone)]
pub enum ParseError {
    #[error("{0}")]
    Operation(#[source] WithContext<operation::ParseError>, usize),
    #[error("Label `{0}` seen multiple times")]
    DuplicateLabel(String, LabelContext),
    #[error("Label `{0}` was seen within a single instruction")]
    InvalidLabel(String, LabelContext),
}

#[derive(Debug, Diagnostic, Error)]
#[error("Label Parse Failure: {problem}")]
pub struct LabelDiagnostic {
    problem: String,
    prev_label: &'static str,
    #[label = "Label"]
    current: SourceSpan,
    #[label = "{prev_label}"]
    previous: Option<SourceSpan>,
    #[help]
    help: Option<Cow<'static, str>>,
    #[source_code]
    src: NamedSource<String>,
}

impl ParseError {
    pub fn as_diagnostic(self, src: NamedSource<String>) -> Report {
        let problem = self.to_string();
        let a: Box<dyn Diagnostic + Send + Sync> = match self {
            Self::Operation(p, offset) => {
                Box::new(operation::ParseDiagnostic::from_err(p, src, offset))
            }
            Self::DuplicateLabel(_, ctx) => Box::new(LabelDiagnostic {
                current: ctx.current,
                help: ctx.help,
                previous: ctx.previous,
                problem,
                src,
                prev_label: "Duplicate",
            }),
            Self::InvalidLabel(_, ctx) => Box::new(LabelDiagnostic {
                current: ctx.current,
                help: ctx.help,
                previous: ctx.previous,
                problem,
                src,
                prev_label: "Instruction Start",
            }),
        };
        Report::new_boxed(a)
    }
}

impl FromStr for Program {
    type Err = ParseError;
    fn from_str(backing: &str) -> Result<Self, Self::Err> {
        static LABEL_RE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^(\w+)::?\s*$").unwrap());
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
        let lines = lines
            .into_iter()
            .skip_while(|&(_, _, l)| !l.starts_with("#### BEGIN BASIC BLOCK ####"))
            .skip(1)
            .take_while(|&(_, _, l)| !l.starts_with("#### END BASIC BLOCK ####"))
            .collect::<Vec<_>>();
        let mut insts = vec![];
        let mut labels = HashMap::new();
        let mut inside_inst = false;
        let mut inst = Instruction::default();
        for &(lineno, span, line) in &lines {
            if line.trim_start().starts_with('#') {
                continue;
            }
            if line.trim_start().starts_with(";;") {
                // eject
                insts.push(inst);
                inst = Instruction::default();
                inside_inst = false;
                continue;
            }
            if let Some(label) = LABEL_RE.captures(line.trim_start()).and_then(|c| c.get(1)) {
                if inside_inst {
                    return Err(ParseError::InvalidLabel(
                        label.as_str().to_owned(),
                        LabelContext {
                            current: span,
                            previous: inst.0.first().and_then(|op| op.ctx.map(|c| c.1)),
                            help: Some(Cow::Borrowed(
                                "Labels must appear after a ;; but before any new operations",
                            )),
                        },
                    ));
                }
                if let Some((_, prev_ctx)) =
                    labels.insert(label.as_str().to_owned(), (insts.len(), span))
                {
                    return Err(ParseError::DuplicateLabel(
                        label.as_str().to_owned(),
                        LabelContext {
                            current: span,
                            previous: Some(prev_ctx),
                            help: None,
                        },
                    ));
                }
                continue;
            }
            let op: Operation = line
                .parse()
                .map_err(|p| ParseError::Operation(p, span.offset()))?;
            inst.0.push(op.with_context((lineno, span)));
            inside_inst = true;
        }
        Ok(Self { insts, labels })
    }
}
