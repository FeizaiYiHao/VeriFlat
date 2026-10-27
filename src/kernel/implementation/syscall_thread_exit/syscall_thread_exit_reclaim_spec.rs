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

/// Detaching the write-held IOMMU table `iommu_table` of the exiting process under the held root-table lock: every root-table
/// slot its owner owns drops its IOMMU root and DID, the table drops its DID, and the IOTLB domain and cached context entries
/// of that DID, if any, are invalidated. Owners, the table base, the root-table lock, the table's lock, and every other object
/// stay.
#[verifier::opaque]
pub open spec fn thread_exit_detach_process_functions_eof_transition_framing(pre: KernelK, post: KernelK, iommu_table: RwLockPageTableRoot) -> bool {
    let table = pre.it_mp.spec_index(iommu_table);
    let empty_tlb = SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() };
    &&& post == (KernelK { irt: post.irt, iommu_tlb: post.iommu_tlb, it_mp: post.it_mp, ..pre })
    &&& post.irt.locking_thread() == pre.irt.locking_thread()
    &&& post.irt.view().table_base() == pre.irt.view().table_base()
    &&& post.irt.view().owners() == pre.irt.view().owners()
    &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_owner(b, d, f)] post.irt.view().spec_index_owner(b, d, f) == pre.irt.view().spec_index_owner(b, d, f)
    &&& forall|b: usize, d: usize, f: usize| #![trigger post.irt.view().spec_index_iommu_root(b, d, f)] #![trigger post.irt.view().spec_index_iommu_did(b, d, f)] pci_bdf_valid(b, d, f) ==> {
        let owned = pre.irt.view().spec_index_owner(b, d, f) == table.view().proc_ptr;
        &&& post.irt.view().spec_index_iommu_root(b, d, f) == if owned { None } else { pre.irt.view().spec_index_iommu_root(b, d, f) }
        &&& post.irt.view().spec_index_iommu_did(b, d, f) == if owned { None } else { pre.irt.view().spec_index_iommu_did(b, d, f) }
    }
    &&& post.it_mp.unchanged_except(&pre.it_mp, iommu_table)
    &&& post.it_mp.lock_id_by_key(iommu_table) == pre.it_mp.lock_id_by_key(iommu_table)
    &&& post.it_mp.spec_index(iommu_table).locking_thread() == table.locking_thread()
    &&& post.it_mp.spec_index(iommu_table).being_killed() == table.being_killed()
    &&& post.it_mp.spec_index(iommu_table).view() == (PageTable { did: None, ..table.view() })
    &&& post.it_mp.spec_index(iommu_table).view().mapping_4k() == table.view().mapping_4k()
    &&& post.it_mp.spec_index(iommu_table).view().mapping_2m() == table.view().mapping_2m()
    &&& post.it_mp.spec_index(iommu_table).view().mapping_1g() == table.view().mapping_1g()
    &&& post.it_mp.spec_index(iommu_table).view().page_closure() == table.view().page_closure()
    &&& post.it_mp.spec_index(iommu_table).view().proc_ptr == table.view().proc_ptr
    &&& table.view().did matches Some(did) ==> {
        &&& post.iommu_tlb.view() == pre.iommu_tlb.view().insert(did, empty_tlb)
        &&& post.iommu_tlb.context_cache() == Map::new(pre.iommu_tlb.context_cache().dom().filter(|bdf: PciBdf| pre.iommu_tlb.context_cache()[bdf].1 != did), |bdf: PciBdf| pre.iommu_tlb.context_cache()[bdf])
    }
    &&& table.view().did is None ==> post.iommu_tlb == pre.iommu_tlb
    &&& forall|did: VtdDomainId| #![trigger post.iommu_tlb.spec_index(did)]
        post.iommu_tlb.spec_index(did) == if table.view().did == Some(did) { empty_tlb } else { pre.iommu_tlb.spec_index(did) }
}
} // verus!
