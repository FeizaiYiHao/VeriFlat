use vstd::prelude::*;
use crate::*;

verus! {
/// Container owned_processes and process owning_container agree; a non-empty container owns its root process.
#[verifier::opaque]
pub open spec fn container_process_wf(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap) -> bool {
    // Container -> processes.
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view().root_process]
        #![trigger ctn_mp.spec_index(c).view_ghost().owned_processes]
        ctn_mp.dom().contains(c) ==> {
            let owned = ctn_mp.spec_index(c).view_ghost().owned_processes.view();
            let root = ctn_mp.spec_index(c).view().root_process;
            // a container that owns no process is write-held
            &&& owned.is_empty() ==> ctn_mp.spec_index(c).wlocked()
            &&& !owned.is_empty() ==> prc_mp.dom().contains(root) && owned.contains(root)
            &&& owned.subset_of(prc_mp.dom())
            // a zombie container still owns its root, which is a zombie
            &&& ctn_mp.spec_index(c).view().zombie ==> owned.contains(root) && prc_mp.spec_index(root).view().zombie
        }
    &&& forall|c: RwLockContainerPtr, p: RwLockProcessPtr|
        #![trigger ctn_mp.spec_index(c).view_ghost().owned_processes.view().contains(p)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view_ghost().owned_processes.view().contains(p)
            ==> prc_mp.spec_index(p).view_rodata().view().owning_container == c
    // Process -> container.
    &&& forall|p: RwLockProcessPtr|
        #![trigger prc_mp.dom().contains(p), prc_mp.spec_index(p).view_rodata().view().owning_container]
        prc_mp.dom().contains(p) ==> {
            let ctn_ptr = prc_mp.spec_index(p).view_rodata().view().owning_container;
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(p)
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth == prc_mp.spec_index(p).view_rodata().view().container_depth
        }
}

pub proof fn container_process_wf_process_at(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        container_process_wf(ctn_mp, prc_mp),
    ensures
        prc_mp.dom().contains(prc_ptr) ==> ({
            let ctn_ptr = prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container;
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(prc_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth == prc_mp.spec_index(prc_ptr).view_rodata().view().container_depth
        }),
{ reveal(container_process_wf); }

pub proof fn container_process_wf_container_at(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, ctn_ptr: RwLockContainerPtr, prc_ptr: RwLockProcessPtr)
    requires
        container_process_wf(ctn_mp, prc_mp),
    ensures
        ctn_mp.dom().contains(ctn_ptr) ==> ({
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().subset_of(prc_mp.dom())
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(prc_ptr) ==> prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr
        }),
{ reveal(container_process_wf); }

/// Container `ctn_ptr` owning a process owns its root process, which is in the process map.
pub proof fn container_process_wf_root_at(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_process_wf(ctn_mp, prc_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        !ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().is_empty() ==> {
            &&& prc_mp.dom().contains(ctn_mp.spec_index(ctn_ptr).view().root_process)
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().contains(ctn_mp.spec_index(ctn_ptr).view().root_process)
        },
{ reveal(container_process_wf); }

/// Each container's processes are empty or a well-formed tree at its root process.
#[verifier::opaque]
pub open spec fn per_container_process_tree_wf(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap) -> bool
    recommends
        container_process_wf(ctn_mp, prc_mp),
{
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view().root_process]
        #![trigger ctn_mp.spec_index(c).view_ghost().owned_processes]
        ctn_mp.dom().contains(c)
            ==> ctn_mp.spec_index(c).view_ghost().owned_processes.view().is_empty()
            || process_tree_wf(ctn_mp.spec_index(c).view().root_process, ctn_mp.spec_index(c).view_ghost().owned_processes.view(), prc_mp)
}

/// Container `ctn_ptr`'s process tree is empty or well formed.
pub proof fn per_container_process_tree_wf_at(ctn_mp: ContainerLockedMap, prc_mp: ProcessLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        per_container_process_tree_wf(ctn_mp, prc_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().is_empty()
            || process_tree_wf(ctn_mp.spec_index(ctn_ptr).view().root_process, ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view(), prc_mp),
{ reveal(per_container_process_tree_wf); }
} // verus!
