use vstd::prelude::*;
use crate::*;

verus! {
/// A container whose root process is removed owns no process: every owned process names it as its owning container, and a process in the map keeps that container's root process.
pub proof fn container_root_removed_implies_no_owned_processes(k: KernelK, c: RwLockContainerPtr)
    requires
        container_process_wf(k.ctn_mp, k.prc_mp),
        k.ctn_mp.dom().contains(c),
        k.ctn_mp.spec_index(c).view().root_process_removed.view(),
    ensures k.ctn_mp.spec_index(c).view_ghost().owned_processes.view().is_empty(),
{
    assert(k.ctn_mp.spec_index(c).view_ghost().owned_processes.view() =~= Set::<RwLockProcessPtr>::empty()) by { reveal(container_process_wf); };
}
} // verus!
