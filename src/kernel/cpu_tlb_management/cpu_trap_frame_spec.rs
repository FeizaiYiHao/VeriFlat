use vstd::prelude::*;
use crate::*;

verus! {
/// Slot `c` of the per-cpu trap-frame table is filled exactly while cpu `c` runs a thread, and then holds the permission to
/// that thread's frame.
#[verifier::opaque]
pub open spec fn cpu_trap_frame_wf(frames: Map<CpuId, TrapFramePerm>, cpu_arr: CpuLockedArray) -> bool {
    forall|c: CpuId| #![trigger frames.dom().contains(c)] #![trigger cpu_arr.spec_index(c).view().view().view()] {
        &&& frames.dom().contains(c) == (index_valid(NUM_CPUS, c) && cpu_arr.spec_index(c).view().view().view().current_thread is Some)
        &&& frames.dom().contains(c) ==> frames[c].addr() == thread_trap_frame_addr(cpu_arr.spec_index(c).view().view().view().current_thread->Some_0)
    }
}

/// The trap-frame slot facts of cpu `cpu_id`.
pub proof fn cpu_trap_frame_wf_at(frames: Map<CpuId, TrapFramePerm>, cpu_arr: CpuLockedArray, cpu_id: CpuId)
    requires
        cpu_trap_frame_wf(frames, cpu_arr),
    ensures
        frames.dom().contains(cpu_id) == (index_valid(NUM_CPUS, cpu_id) && cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some),
        frames.dom().contains(cpu_id) ==> frames[cpu_id].addr() == thread_trap_frame_addr(cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0),
{ reveal(cpu_trap_frame_wf); }
}
