use vstd::prelude::*;
use crate::*;

verus! {
/// A marked cpu set stays write-held by the thread that holds its killer's process; its container carries the same
/// mark and owns no process and no thread.
#[verifier::opaque]
pub open spec fn cpu_set_kill_mark_wf(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, prc_mp: ProcessLockedMap) -> bool {
    forall|cpu_set_ptr: RwLockCpuSetPtr|
        #![trigger cpu_set_mp.spec_index(cpu_set_ptr).killer_info()]
        cpu_set_mp.dom().contains(cpu_set_ptr) && cpu_set_mp.spec_index(cpu_set_ptr).killer_info() is Some ==> {
            let killer_process = cpu_set_mp.spec_index(cpu_set_ptr).killer_info()->Some_0.process;
            let killer_tid = prc_mp.spec_index(killer_process).locking_thread()->Write_thread_id;
            let ctn_ptr = cpu_set_mp.spec_index(cpu_set_ptr).view().owning_container.view();
            &&& prc_mp.dom().contains(killer_process)
            &&& prc_mp.spec_index(killer_process).locking_thread() is Write
            &&& cpu_set_mp.spec_index(cpu_set_ptr).wlocked_by_thread(killer_tid)
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).being_killed()
            &&& ctn_mp.spec_index(ctn_ptr).killer_info() == cpu_set_mp.spec_index(cpu_set_ptr).killer_info()
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().is_empty()
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().is_empty()
        }
}

pub proof fn cpu_set_kill_mark_wf_at(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, prc_mp: ProcessLockedMap, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        cpu_set_kill_mark_wf(ctn_mp, cpu_set_mp, prc_mp),
    ensures
        cpu_set_mp.dom().contains(cpu_set_ptr) && cpu_set_mp.spec_index(cpu_set_ptr).killer_info() is Some ==> ({
            let killer_process = cpu_set_mp.spec_index(cpu_set_ptr).killer_info()->Some_0.process;
            let killer_tid = prc_mp.spec_index(killer_process).locking_thread()->Write_thread_id;
            let ctn_ptr = cpu_set_mp.spec_index(cpu_set_ptr).view().owning_container.view();
            &&& prc_mp.dom().contains(killer_process)
            &&& prc_mp.spec_index(killer_process).locking_thread() is Write
            &&& cpu_set_mp.spec_index(cpu_set_ptr).wlocked_by_thread(killer_tid)
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).being_killed()
            &&& ctn_mp.spec_index(ctn_ptr).killer_info() == cpu_set_mp.spec_index(cpu_set_ptr).killer_info()
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().is_empty()
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().is_empty()
        }),
{ reveal(cpu_set_kill_mark_wf); }
}
