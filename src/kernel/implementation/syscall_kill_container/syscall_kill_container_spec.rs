use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::kill_process_middle_step;

verus! {
/// Entering a container kill of the child at `child_index`. Placeholder until the container kill's steps are frozen: no
/// step enters it yet.
pub open spec fn kill_container_enter_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, child_index: usize) -> bool { false }

/// A container kill's own step between entering and finishing. Placeholder until the container kill's steps are frozen:
/// no such step exists yet.
pub open spec fn kill_container_middle_step(step: KernelStep, cpu_id: CpuId) -> bool { false }

/// The partial trace of a container kill before finishing: one enter step from `pre` followed by middle steps, each a
/// step of a process kill it runs inside the victim container or a step of its own.
#[verifier::opaque]
pub open spec fn kill_container_partial_trace(trace: Seq<KernelStep>, pre: KernelU, cpu_id: CpuId, child_index: usize) -> bool {
    &&& 1 <= trace.len()
    &&& trace[0].old_u == pre
    &&& kill_container_enter_step(pre, trace[0].new_u, cpu_id, child_index)
    &&& forall|j: int| #![trigger trace[j]] 0 < j < trace.len() ==> kill_process_middle_step(trace[j], cpu_id) || kill_container_middle_step(trace[j], cpu_id)
}
} // verus!
