use vstd::prelude::*;
use crate::*;

verus! {
/// Every page mapped at a source-range address of `source_pagetable` is owned by `target_container` or one of its ancestors.
pub(super) proof fn ipc_share_pages_source_owners_in_target_uppertree(
    krnl: &KernelK, cpu_id: CpuId, caller_thread: RwLockThreadPtr, peer_thread: RwLockThreadPtr, source_thread: RwLockThreadPtr,
    source_pagetable: RwLockPageTableRoot, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr, source_range: &VaRange4K,
)
    requires
        krnl.inv(),
        source_thread == caller_thread || source_thread == peer_thread,
        index_valid(NUM_CPUS, cpu_id),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_thread),
        krnl.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        krnl.thr_mp.dom().contains(peer_thread),
        krnl.thr_mp.spec_index(peer_thread).view().blocking_endpoint_ptr is Some,
        krnl.thr_mp.spec_index(source_thread).view().owning_container == source_container,
        krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc,
        krnl.ctn_mp.dom().contains(target_container),
        source_container == target_container || krnl.ctn_mp.spec_index(target_container).view_ghost().uppertree_seq.view().contains(source_container),
        share_mapping_4k_source_range_present(krnl, source_pagetable, source_range),
    ensures
        share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range),
{
    thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread);
    process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread);
    container_uppertree_seq_wf_at(krnl.rt_ctn, krnl.ctn_mp, target_container, source_container);
    reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(container_subtree_set_wf);
}
}
