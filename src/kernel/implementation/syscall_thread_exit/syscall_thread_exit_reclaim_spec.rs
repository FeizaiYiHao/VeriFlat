use vstd::prelude::*;
use crate::*;

verus! {
/// Marking the write-held exiting process `process_ptr`, whose tables map nothing and whose only thread `thread_ptr`
/// is parked as an exited zombie, as having emptied its tables while it and its tables are still write-held. Lock
/// owners, lock ids, and every other object stay.
#[verifier::opaque]
pub open spec fn thread_exit_tables_emptied_eof_transition_framing(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr) -> bool {
    let process = pre.prc_mp.spec_index(process_ptr);
    &&& post == (KernelK { prc_mp: post.prc_mp, ..pre })
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

/// Detaching function `(bus, device, function)` of the exiting process: its root-table slot drops its IOMMU root and
/// its IOTLB domain is invalidated and its cached context entry dropped. Owners, the table base, the root-table lock, and every other object stay.
#[verifier::opaque]
pub open spec fn thread_exit_detach_process_functions_eof_transition_framing(pre: KernelK, post: KernelK, bus: usize, device: usize, function: usize) -> bool {
    &&& post == (KernelK { irt: post.irt, iommu_tlb: post.iommu_tlb, ..pre })
    &&& post.irt.locking_thread() == pre.irt.locking_thread()
    &&& post.irt.view().table_base() == pre.irt.view().table_base()
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] post.irt.view().spec_index_owner(b, d, f) == pre.irt.view().spec_index_owner(b, d, f)
    &&& post.irt.view().iommu_roots() == seq3_update(pre.irt.view().iommu_roots(), bus as int, device as int, function as int, None)
    &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] pci_bdf_valid(b, d, f)
        ==> post.irt.view().spec_index_iommu_root(b, d, f) == if (b, d, f) == (bus, device, function) { None } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
    &&& post.iommu_tlb.view() == pre.iommu_tlb.view().insert(pci_bdf_did(bus, device, function), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
    &&& post.iommu_tlb.context_cache() == pre.iommu_tlb.context_cache().remove(pci_bdf_did(bus, device, function))
}
} // verus!
