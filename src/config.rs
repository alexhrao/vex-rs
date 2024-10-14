use std::{fs, io, path::Path};

use serde::Deserialize;
use thiserror::Error;
use vex::machine;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Deserialize)]
struct Resource {
    slots: usize,
    latency: usize,
}
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Deserialize)]
struct Cluster {
    regs: usize,
    branch: usize,
}

impl From<&Cluster> for machine::ClusterConfig {
    fn from(value: &Cluster) -> Self {
        Self {
            num_regs: value.regs,
            num_branch: value.branch,
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Deserialize)]
struct Machine {
    slots: usize,
    mem: usize,
    alu: Resource,
    load: Resource,
    store: Resource,
    mul: Resource,
    clusters: Vec<Cluster>,
}

impl Default for Machine {
    fn default() -> Self {
        Self {
            slots: 4,
            mem: 4096,
            alu: Resource {
                latency: 1,
                slots: 4,
            },
            load: Resource {
                slots: 1,
                latency: 3,
            },
            store: Resource {
                slots: 1,
                latency: 3,
            },
            mul: Resource {
                slots: 2,
                latency: 2,
            },
            clusters: vec![Cluster {
                branch: 8,
                regs: 64,
            }]
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Deserialize, Default)]
pub struct Config {
    machine: Machine,
}

impl From<&Config> for machine::Args {
    fn from(value: &Config) -> Self {
        let m = &value.machine;
        let clusters = m
            .clusters
            .iter()
            .map(machine::ClusterConfig::from)
            .collect();
        machine::Args {
            clusters,
            num_slots: m.slots,
            num_alus: m.alu.slots,
            num_muls: m.mul.slots,
            num_loads: m.load.slots,
            num_stores: m.store.slots,
            mem_size: m.mem,
            alu_latency: m.alu.latency,
            mul_latency: m.mul.latency,
            store_latency: m.store.latency,
            load_latency: m.load.latency,
        }
    }
}

impl From<Config> for machine::Args {
    fn from(value: Config) -> Self {
        (&value).into()
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("I/O Error")]
    FileNotFound(#[from] io::Error),
    #[error("Invalid TOML file")]
    InvalidToml(#[from] toml::de::Error),

}

pub fn get_config(cfg: &Path) -> Result<Config, Error> {
    let backing = fs::read_to_string(cfg)?;
    let config: Config = toml::from_str(&backing)?;
    Ok(config)
}