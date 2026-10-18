use vstd::prelude::*;
use crate::*;

verus! {
/// Marking the write-held exiting process `process_ptr`, whose tables map nothing and whose only thread `thread_ptr`
/// is parked as an exited zombie, as having emptied its tables while it and its tables are still write-held. Lock
/// owners, lock ids, and every other object stay.
#[verifier::opaque]
pub open spec fn thread_exit_tables_emptied_transition(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr) -> bool {
    let process = pre.prc_mp.spec_index(process_ptr);
    &&& post == (KernelK { prc_mp: post.prc_mp, ..pre })
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& !process.view().zombie
    &&& process.view().owned_threads.view().len() == 1
    &&& process.view().owned_threads.view().contains(thread_ptr)
    &&& pre.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExitZombie)
    &&& pre.pt_mp.spec_index(process.view().pagetable).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
    &&& process.view().iommu_table is Some ==> pre.it_mp.spec_index(process.view().iommu_table->Some_0).view().mapping_4k().dom() =~= Set::<VAddr>::empty()
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& post.prc_mp.perms_wf()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& post.prc_mp.spec_index(process_ptr).is_init()
    &&& post.prc_mp.spec_index(process_ptr).wlocked()
    &&& post.prc_mp.spec_index(process_ptr).view() == (Process { state: Ghost(ProcessState::TablesEmptied), ..process.view() })
    &&& post.prc_mp.spec_index(process_ptr).view_rodata() == process.view_rodata()
    &&& post.prc_mp.spec_index(process_ptr).view_ghost() == process.view_ghost()
    &&& post.prc_mp.spec_index(process_ptr).locking_thread() == process.locking_thread()
    &&& post.prc_mp.spec_index(process_ptr).being_killed() == process.being_killed()
    &&& post.prc_mp.spec_index(process_ptr).killer_info() == process.killer_info()
}
} // verus!
