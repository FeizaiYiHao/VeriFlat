use vstd::prelude::*;
use crate::*;

verus! {
/// A running cpu and its RUNNING current thread name each other, and a marked cpu is write-held by its current thread's killer.
#[verifier::opaque]
pub open spec fn thread_cpu_wf(thrd_mp: ThreadLockedMap, cpu_arr: CpuLockedArray) -> bool {
    // A running cpu runs a RUNNING thread of its current process.
    &&& forall|cpu_id: CpuId|
        #![trigger cpu_arr.spec_index(cpu_id).view().view().view().current_thread]
        index_valid(NUM_CPUS, cpu_id) && cpu_arr.spec_index(cpu_id).view().view().view().state is Running ==> {
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            let thrd_ptr = cpu.current_thread.unwrap();
            &&& cpu.current_thread is Some
            &&& thrd_mp.dom().contains(thrd_ptr)
            &&& thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& cpu.current_process is Some
            &&& thrd_mp.spec_index(thrd_ptr).view().owning_proc == cpu.current_process.unwrap()
        }
    // A RUNNING thread is its cpu's current thread.
    &&& forall|t: RwLockThreadPtr|
        #![trigger thrd_mp.spec_index(t).view().state]
        thrd_mp.dom().contains(t) && thrd_mp.spec_index(t).view().state is RUNNING ==> {
            let cpu_id = thrd_mp.spec_index(t).view().state->RUNNING_cpu_id;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu_arr.spec_index(cpu_id).view().view().view().state is Running
            &&& cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(t)
        }
    // A marked cpu is running and write-held; its current thread carries the same mark, and that thread's holder, its
    // killer, holds the cpu.
    &&& forall|cpu_id: CpuId|
        #![trigger cpu_arr.spec_index(cpu_id).view().being_killed()]
        index_valid(NUM_CPUS, cpu_id) && cpu_arr.spec_index(cpu_id).view().being_killed() ==> {
            let cpu = cpu_arr.spec_index(cpu_id).view();
            let thread = thrd_mp.spec_index(cpu.view().view().current_thread->Some_0);
            &&& cpu.view().view().state is Running
            &&& cpu.view().view().current_thread is Some
            &&& thread.killer_info() == cpu.killer_info()
            &&& thread.locking_thread() is Write
            &&& cpu.wlocked_by_thread(thread.locking_thread()->Write_thread_id)
        }
}

pub proof fn thread_cpu_wf_cpu_at(thrd_mp: ThreadLockedMap, cpu_arr: CpuLockedArray, cpu_id: CpuId)
    requires
        thread_cpu_wf(thrd_mp, cpu_arr),
    ensures
        index_valid(NUM_CPUS, cpu_id) && cpu_arr.spec_index(cpu_id).view().view().view().state is Running ==> ({
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            let thrd_ptr = cpu.current_thread.unwrap();
            &&& cpu.current_thread is Some
            &&& thrd_mp.dom().contains(thrd_ptr)
            &&& thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& cpu.current_process is Some
            &&& thrd_mp.spec_index(thrd_ptr).view().owning_proc == cpu.current_process.unwrap()
        }),
{ reveal(thread_cpu_wf); }

/// A marked cpu `cpu_id` is running and write-held by the holder of its current thread, which carries the same mark.
pub proof fn thread_cpu_wf_killed_cpu_at(thrd_mp: ThreadLockedMap, cpu_arr: CpuLockedArray, cpu_id: CpuId)
    requires
        thread_cpu_wf(thrd_mp, cpu_arr),
    ensures
        index_valid(NUM_CPUS, cpu_id) && cpu_arr.spec_index(cpu_id).view().being_killed() ==> ({
            let cpu = cpu_arr.spec_index(cpu_id).view();
            let thread = thrd_mp.spec_index(cpu.view().view().current_thread->Some_0);
            &&& cpu.view().view().state is Running
            &&& cpu.view().view().current_thread is Some
            &&& thread.killer_info() == cpu.killer_info()
            &&& thread.locking_thread() is Write
            &&& cpu.wlocked_by_thread(thread.locking_thread()->Write_thread_id)
        }),
{ reveal(thread_cpu_wf); }

/// A running thread `thrd_ptr` is the current thread of its running cpu.
pub proof fn thread_cpu_wf_thread_at(thrd_mp: ThreadLockedMap, cpu_arr: CpuLockedArray, thrd_ptr: RwLockThreadPtr)
    requires
        thread_cpu_wf(thrd_mp, cpu_arr),
    ensures
        thrd_mp.dom().contains(thrd_ptr) && thrd_mp.spec_index(thrd_ptr).view().state is RUNNING ==> {
            let cpu_id = thrd_mp.spec_index(thrd_ptr).view().state->RUNNING_cpu_id;
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu_arr.spec_index(cpu_id).view().view().view().state is Running
            &&& cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr)
        },
{ reveal(thread_cpu_wf); }
}
