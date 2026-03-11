use vstd::prelude::*;
use crate::*;

verus! {

pub type CpuArray = LockedArray<Cpu, CPU_HAS_KILL_STATE, NUM_CPUS>;

}