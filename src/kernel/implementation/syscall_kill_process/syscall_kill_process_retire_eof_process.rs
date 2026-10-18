use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_spec::*;

verus! {
/// Retiring the empty zombie `target` keeps the container tree and the container, endpoint, scheduler, cpu-set,
/// offline-flag, PCID-allocator, and thread relations.
pub(super) proof fn kill_retire_eof_container_relations(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.dom().contains(parent_ptr),
        parent_ptr != target,
        pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()),
        pre.prc_mp.spec_index(parent_ptr).view().children.map().spec_index(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()) == target,
        pre.ctn_mp.dom().contains(container_ptr),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        thread_caller_callee_wf(post.thr_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp),
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
        container_thread_wf(post.ctn_mp, post.thr_mp),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(kill_retire_eof_transition_framing);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, pre.ep_mp, post.ep_mp); };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp, post.sched_mp); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thr_mp, post.thr_mp); };
}

/// Retiring the empty zombie `target` keeps the container-cpu relation and the process PCID, cpu, thread, kill-mark,
/// lock-state, and emptied-thread invariants.
pub(super) proof fn kill_retire_eof_process_relations(
    pre: KernelK, post: KernelK, lctx: LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr,
    container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.dom().contains(parent_ptr),
        parent_ptr != target,
        pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()),
        pre.prc_mp.spec_index(parent_ptr).view().children.map().spec_index(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()) == target,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        forall|d: RwLockProcessPtr| #![trigger lctx.process_lock_map().dom().contains(d)] lctx.process_lock_map().dom().contains(d) && pre.prc_mp.spec_index(d).killer_info() is Some
            ==> pre.prc_mp.spec_index(d).killer_info()->Some_0.process != target && pre.prc_mp.spec_index(d).view_rodata().view().owning_container == container_ptr,
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        process_thread_wf(post.prc_mp, post.thr_mp),
        process_kill_mark_wf(post.prc_mp),
        process_state_lock_wf(post.prc_mp),
        process_emptied_threads_wf(post.prc_mp, post.thr_mp),
{
    reveal(kill_retire_eof_transition_framing);
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(process_cpu_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); reveal(container_pcid_allocator_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { reveal(process_thread_wf); };
    assert(process_kill_mark_wf(post.prc_mp)) by { reveal(process_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); reveal(container_process_wf); reveal(per_container_process_tree_wf); reveal(process_children_parent_wf); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
}

/// Retiring the empty zombie `target` keeps the IOMMU root-table, PCI-function ownership, IOTLB, and IOMMU-table lock
/// invariants.
pub(super) proof fn kill_retire_eof_iommu(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
    ensures
        iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp),
        process_pci_function_ownership_wf(post.irt.view(), post.prc_mp),
        iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp),
        iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp),
{
    reveal(kill_retire_eof_transition_framing);
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); reveal(process_pci_function_ownership_wf); process_iommu_table_match_process_at(pre.prc_mp, pre.it_mp, target); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); reveal(process_iommu_table_match); };
}

/// A CPU/PCID association that the TLB and dirty-map invariants constrain belongs to neither the retired target nor its
/// page table: a current PCID belongs to a running process, which is no zombie, and a live TLB entry for the target's
/// page table would have to be a subset of its empty mappings.
broadcast proof fn kill_retire_eof_tlb_entry(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, c: CpuId, p: Pcid,
)
    requires
        cpu_array_wf(pre.cpu_arr, pre.dflt_pt.view()),
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        cpu_dirty_map_proc_pcid_match(pre.prc_mp, pre.cpu_arr, pre.pcid_needflush, pre.cpu_tlb),
        tlb_wf_spec(pre.cpu_tlb, pre.pt_mp, pre.cpu_arr, pre.pcid_needflush),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        index_valid(NUM_CPUS, c),
        pcid_valid(p),
        p != KERNEL_DEFAULT_PCID,
    ensures
        #![trigger kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr), post.cpu_tlb.spec_index((c, p))]
        #![trigger kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr), post.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(p)]
        ({
            let tlb = post.cpu_tlb.spec_index((c, p));
            let cpu = post.cpu_arr.spec_index(c).view().view();
            let dirty = cpu.tlb_dirty_bitmap().spec_index(p);
            let pagetable = pre.prc_mp.spec_index(target).view().pagetable;
            let needflush = post.pcid_needflush.spec_index(c, p).view().needflush;
            &&& !tlb.is_empty() && (!needflush || cpu.view().current_pcid == p) ==> dirty is Some && dirty.unwrap().pagetable_ptr != pagetable
            &&& dirty is Some && ((!needflush && !tlb.is_empty()) || cpu.view().current_pcid == p) ==> dirty.unwrap().process_ptr != target && dirty.unwrap().pagetable_ptr != pagetable
        }),
{
    reveal(kill_retire_eof_transition_framing);
    let tlb = pre.cpu_tlb.spec_index((c, p));
    let cpu = pre.cpu_arr.spec_index(c).view().view();
    let dirty = cpu.tlb_dirty_bitmap().spec_index(p);
    let pagetable = pre.prc_mp.spec_index(target).view().pagetable;
    if cpu.view().current_pcid == p {
        cpu_array_wf_at(pre.cpu_arr, pre.dflt_pt.view(), c); process_cpu_wf_at(pre.prc_mp, pre.cpu_arr, c);
        process_pagetable_match_process_at(pre.prc_mp, pre.pt_mp, target); process_pagetable_match_process_at(pre.prc_mp, pre.pt_mp, cpu.view().current_process.unwrap());
    } else if !tlb.is_empty() && !pre.pcid_needflush.spec_index(c, p).view().needflush {
        assert(dirty is Some && (dirty.unwrap().pagetable_ptr == pagetable
            ==> tlb.tlb_4k().dom() =~= Set::<VAddr>::empty() && tlb.tlb_2m().dom() =~= Set::<VAddr>::empty() && tlb.tlb_1g().dom() =~= Set::<VAddr>::empty())) by { reveal(tlb_wf_spec); };
        assert(dirty.unwrap().process_ptr != target) by { reveal(cpu_dirty_map_proc_pcid_match); };
    }
}

/// Retiring the empty zombie `target` keeps the cpu dirty-map and TLB invariants.
pub(super) proof fn kill_retire_eof_tlb(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
    ensures
        cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush),
        tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush),
{
    reveal(kill_retire_eof_transition_framing);
    assert(cpu_dirty_map_contains_container_processes(post.ctn_mp, post.cpu_set_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf); broadcast use kill_retire_eof_tlb_entry; };
    assert(cpu_dirty_map_proc_pcid_match(post.prc_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by { reveal(cpu_dirty_map_proc_pcid_match); broadcast use kill_retire_eof_tlb_entry; };
    assert(cpu_dirty_map_contains_pagetable_pcid_match(post.pt_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); broadcast use kill_retire_eof_tlb_entry; };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); broadcast use kill_retire_eof_tlb_entry; };
}
} // verus!
