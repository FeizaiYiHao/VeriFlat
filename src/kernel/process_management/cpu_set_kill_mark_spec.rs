use vstd::prelude::*;
use crate::*;

verus! {
/// A marked cpu set stays write-held by the thread that holds its killer's process; its container carries the same
/// mark and owns no process and no thread.
#[verifier::opaque]
pub open spec fn cpu_set_kill_mark_wf(container_map: ContainerLockedMap, cpu_set_map: CpuSetLockedMap, process_map: ProcessLockedMap) -> bool {
    forall|s: RwLockCpuSetPtr|
        #![trigger cpu_set_map.spec_index(s).killer_info()]
        cpu_set_map.dom().contains(s) && cpu_set_map.spec_index(s).killer_info() is Some ==> {
            let killer_process = cpu_set_map.spec_index(s).killer_info()->Some_0.process;
            let killer_tid = process_map.spec_index(killer_process).locking_thread()->Write_thread_id;
            let c = cpu_set_map.spec_index(s).view().owning_container.view();
            &&& process_map.dom().contains(killer_process)
            &&& process_map.spec_index(killer_process).locking_thread() is Write
            &&& cpu_set_map.spec_index(s).wlocked_by_thread(killer_tid)
            &&& container_map.dom().contains(c)
            &&& container_map.spec_index(c).being_killed()
            &&& container_map.spec_index(c).killer_info() == cpu_set_map.spec_index(s).killer_info()
            &&& container_map.spec_index(c).view_ghost().owned_processes.view().is_empty()
            &&& container_map.spec_index(c).view_ghost().owned_threads.view().is_empty()
        }
}

pub proof fn cpu_set_kill_mark_wf_at(container_map: ContainerLockedMap, cpu_set_map: CpuSetLockedMap, process_map: ProcessLockedMap, s: RwLockCpuSetPtr)
    requires
        cpu_set_kill_mark_wf(container_map, cpu_set_map, process_map),
    ensures
        cpu_set_map.dom().contains(s) && cpu_set_map.spec_index(s).killer_info() is Some ==> ({
            let killer_process = cpu_set_map.spec_index(s).killer_info()->Some_0.process;
            let killer_tid = process_map.spec_index(killer_process).locking_thread()->Write_thread_id;
            let c = cpu_set_map.spec_index(s).view().owning_container.view();
            &&& process_map.dom().contains(killer_process)
            &&& process_map.spec_index(killer_process).locking_thread() is Write
            &&& cpu_set_map.spec_index(s).wlocked_by_thread(killer_tid)
            &&& container_map.dom().contains(c)
            &&& container_map.spec_index(c).being_killed()
            &&& container_map.spec_index(c).killer_info() == cpu_set_map.spec_index(s).killer_info()
            &&& container_map.spec_index(c).view_ghost().owned_processes.view().is_empty()
            &&& container_map.spec_index(c).view_ghost().owned_threads.view().is_empty()
        }),
{ reveal(cpu_set_kill_mark_wf); }
}
