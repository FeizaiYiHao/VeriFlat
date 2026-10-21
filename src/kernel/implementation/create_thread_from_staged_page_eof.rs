use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;

verus! {
/// Complete kernel-state summary of `create_thread_from_staged_page_merged`.
#[verifier::opaque]
pub open spec fn create_thread_from_staged_page_eof_transition_framing(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, process_node_addr: usize, sched_node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(page_ptr);
    let uppers = pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    let pre_page = pre.pg_arr.spec_index(page_index).view();
    let post_page = post.pg_arr.spec_index(page_index).view();
    let pre_process = pre.prc_mp.spec_index(process_ptr);
    let post_process = post.prc_mp.spec_index(process_ptr);
    let pre_staging = pre.thr_mp.spec_index(staging_thread_ptr);
    let post_staging = post.thr_mp.spec_index(staging_thread_ptr);
    let pre_scheduler = pre.sched_mp.spec_index(scheduler_ptr);
    let post_scheduler = post.sched_mp.spec_index(scheduler_ptr);
    let pre_shard = pre_scheduler.shards.spec_index(cpu_id).view();
    let post_shard = post_scheduler.shards.spec_index(cpu_id).view();
    let thread = post.thr_mp.spec_index(page_ptr).view();
    &&& post == (KernelK { pg_arr: post.pg_arr, ctn_mp: post.ctn_mp, sched_mp: post.sched_mp, prc_mp: post.prc_mp, thr_mp: post.thr_mp, ..pre })
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& post_page.view() == (Page { state: PageState::Allocated4k { state: Allocated4KPageState::AsThread }, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    &&& post_page.view().perm_4k.view().is_none()
    &&& post_page.view_rodata() == pre_page.view_rodata()
    &&& post_page.view_ghost() == pre_page.view_ghost()
    &&& post_page.locking_thread() == pre_page.locking_thread()
    &&& post_page.being_killed() == pre_page.being_killed()
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let pre_ghost = pre.ctn_mp.spec_index(c).view_ghost();
            &&& post.ctn_mp.spec_index(c).view() == pre.ctn_mp.spec_index(c).view()
            &&& post.ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
            &&& post.ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
            &&& post.ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
            &&& post.ctn_mp.spec_index(c).killer_info() == pre.ctn_mp.spec_index(c).killer_info()
            &&& post.ctn_mp.spec_index(c).view_ghost() == (ContainerGhost {
                uppertree_seq: pre_ghost.uppertree_seq, subtree_set: pre_ghost.subtree_set, owned_processes: pre_ghost.owned_processes,
                owned_threads: if c == container_ptr { Ghost(pre_ghost.owned_threads.view().insert(page_ptr)) } else { pre_ghost.owned_threads },
                owned_indirect_threads: if uppers.to_set().contains(c) { Ghost(pre_ghost.owned_indirect_threads.view().insert(page_ptr)) } else { pre_ghost.owned_indirect_threads },
                owned_endpoints: pre_ghost.owned_endpoints, retire_ready: pre_ghost.retire_ready,
            })
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& forall|p: RwLockProcessPtr, f: PciBdf| #![trigger post.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view().contains(f)]
        pre.prc_mp.dom().contains(p) ==> post.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view().contains(f) == pre.prc_mp.spec_index(p).view_ghost().owned_pci_functions.view().contains(f)
    &&& post_process.view() == (Process { owned_threads: post_process.view().owned_threads, state: Ghost(ProcessState::Running), ..pre_process.view() })
    &&& post_process.view().owned_threads.view() == pre_process.view().owned_threads.view().push(page_ptr)
    &&& post_process.view().owned_threads.dom() == pre_process.view().owned_threads.dom().insert(process_node_addr)
    &&& post_process.view().owned_threads.map() == pre_process.view().owned_threads.map().insert(process_node_addr, page_ptr)
    &&& !pre_process.view().owned_threads.dom().contains(process_node_addr)
    &&& !pre_process.view().owned_threads.map().dom().contains(process_node_addr)
    &&& post_process.view_rodata() == pre_process.view_rodata()
    &&& post_process.view_ghost() == pre_process.view_ghost()
    &&& post_process.locking_thread() == pre_process.locking_thread()
    &&& post_process.being_killed() == pre_process.being_killed()
    &&& post_process.killer_info() == pre_process.killer_info()
    &&& post.thr_mp.dom() =~= pre.thr_mp.dom().insert(page_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) && t != staging_thread_ptr ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)]
        pre.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t).view().endpoint_descriptors == pre.thr_mp.spec_index(t).view().endpoint_descriptors
    &&& forall|t: RwLockThreadPtr, p: PagePtr| #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(p)]
        pre.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(p) == pre.thr_mp.spec_index(t).view().temp_alloc_cache_2m.view().contains(p)
    &&& forall|t: RwLockThreadPtr, p: PagePtr| #![trigger post.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p)]
        pre.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p) == pre.thr_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p)
    &&& post_staging.view() == (Thread { quota_4k: post_staging.view().quota_4k, temp_alloc_cache_4k: post_staging.view().temp_alloc_cache_4k, ..pre_staging.view() })
    &&& post_staging.view().temp_alloc_cache_4k.view() == pre_staging.view().temp_alloc_cache_4k.view().remove(page_ptr)
    &&& post_staging.view().quota_4k == pre_staging.view().quota_4k - 1
    &&& post_staging.locking_thread() == pre_staging.locking_thread()
    &&& post_staging.being_killed() == pre_staging.being_killed()
    &&& post_staging.killer_info() == pre_staging.killer_info()
    &&& post_staging.view_ghost() == pre_staging.view_ghost()
    &&& post.thr_mp.spec_index(page_ptr).is_init()
    &&& !post.thr_mp.spec_index(page_ptr).being_killed()
    &&& thread.inv()
    &&& thread.state == (ThreadState::SCHEDULED { cpu_id })
    &&& thread.last_cpu == cpu_id
    &&& thread.owning_container == container_ptr
    &&& thread.container_depth == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
    &&& thread.owning_proc == process_ptr
    &&& thread.process_depth == pre_process.view_rodata().view().depth
    &&& thread.proc_pagetable_ptr == pre_process.view().pagetable
    &&& thread.upper_container_seq.view() == uppers
    &&& thread.caller is None
    &&& thread.callee is None
    &&& thread.scheduler_linkedlist_node.addr() == sched_node_addr
    &&& thread.proc_linkedlist_node.addr() == process_node_addr
    &&& thread.blocking_endpoint_ptr is None
    &&& thread.blocking_endpoint_index is None
    &&& thread.endpoint_descriptors.view() == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| None::<RwLockEndpointPtr>)
    &&& thread.ipc_payload is Empty
    &&& thread.error_code is None
    &&& thread.free_quota_pending_clean()
    &&& thread.syscall_progress.view() is None
    &&& thread.temp_alloc_clean()
    &&& thread.quota_4k == 0
    &&& thread.quota_2m == 0
    &&& thread.quota_1g == 0
    &&& post.sched_mp.dom() == pre.sched_mp.dom()
    &&& post.sched_mp.unchanged_except(&pre.sched_mp, scheduler_ptr)
    &&& post_scheduler.owning_container == pre_scheduler.owning_container
    &&& post_scheduler.shards.entries_unchanged_except(&pre_scheduler.shards, cpu_id)
    &&& post_shard.view().queue.view() == pre_shard.view().queue.view().push(page_ptr)
    &&& post_shard.view().queue.dom() == pre_shard.view().queue.dom().insert(sched_node_addr)
    &&& post_shard.view().queue.map() == pre_shard.view().queue.map().insert(sched_node_addr, page_ptr)
    &&& !pre_shard.view().queue.dom().contains(sched_node_addr)
    &&& !pre_shard.view().queue.map().dom().contains(sched_node_addr)
    &&& post_shard.locking_thread() == pre_shard.locking_thread()
    &&& post_shard.being_killed() == pre_shard.being_killed()
    &&& scheduler_shards_of(post_scheduler) == scheduler_shards_of(pre_scheduler).update(cpu_id as int, scheduler_shards_of(pre_scheduler)[cpu_id as int].push(page_ptr))
}

/// Only the owning process's thread list changes and it runs, so no process becomes emptied and every table link keeps its value.
proof fn eof_create_thread_process_emptied_tables_wf(pre: KernelK, post: KernelK, process_ptr: RwLockProcessPtr)
    requires
        process_emptied_tables_wf(pre.prc_mp, pre.pt_mp, pre.pt_lower.view(), pre.it_mp),
        post.pt_mp == pre.pt_mp,
        post.pt_lower == pre.pt_lower,
        post.it_mp == pre.it_mp,
        post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr),
        post.prc_mp.spec_index(process_ptr).view() == (Process { owned_threads: post.prc_mp.spec_index(process_ptr).view().owned_threads, state: Ghost(ProcessState::Running), ..pre.prc_mp.spec_index(process_ptr).view() }),
    ensures
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp),
{ reveal(process_emptied_tables_wf); }

#[verifier::spinoff_prover]
proof fn eof_create_thread_memory_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(staging_thread_ptr),
        !pre.thr_mp.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set().subset_of(pre.ctn_mp.dom()),
        pre.sched_mp.dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        create_thread_from_staged_page_eof_transition_framing(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, process_node_addr, sched_node_addr),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        thread_perms_wf(post.thr_mp),
        scheduler_perms_wf(post.sched_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
    ensures
        post.memory_management_inv(),
{
    reveal(create_thread_from_staged_page_eof_transition_framing);
    let page_index = page_ptr2page_index(page_ptr);
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by { process_kernel_pages_owner_wf_preserved_for_page_state_eq(pre, post); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr, page_index); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by {
        page_iommu_table_wf_preserved_for_nonmapped_page_change(pre.ctn_mp, pre.prc_mp, pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr, page_index);
        reveal(page_iommu_table_wf);
    };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.prc_mp, post.prc_mp); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { pagetable_pages_wf_preserved_for_page_state_eq(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view(), pre.pg_arr, post.pg_arr); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_staged_pages_4k_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
    assert(thread_staged_pages_2m_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
    assert(thread_staged_pages_1g_wf(post.thr_mp, post.pg_arr)) by { reveal(thread_staged_pages_1g_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { eof_create_thread_process_emptied_tables_wf(pre, post, process_ptr); };
    assert(container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures(); thread_perms_wf_at(post.thr_mp, page_ptr);
        lemma_container_process_thread_quota_folds_insert_zero_forall(pre.rt_ctn, pre.ctn_mp, post.ctn_mp, pre.prc_mp, post.prc_mp, pre.thr_mp, post.thr_mp, container_ptr, page_ptr);
        assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); };
        assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by { reveal(container_process_allocator_quota_2m_wf); };
        assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_1g_wf); };
    };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, process_ptr); pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
        reveal(container_kill_retire_wf); reveal(container_uppertree_seq_wf);
    };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(post.allc_4k_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(post.allc_2m_mp, pre.pg_arr, post.pg_arr, page_index); };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(post.allc_1g_mp, pre.pg_arr, post.pg_arr, page_index); };
}

proof fn eof_create_thread_endpoint_ref_counter_wf(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        thread_endpoint_ref_counter_wf(pre.thr_mp, pre.ep_mp),
        create_thread_from_staged_page_eof_transition_framing(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, process_node_addr, sched_node_addr),
    ensures
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
{
    reveal(create_thread_from_staged_page_eof_transition_framing); reveal(thread_endpoint_ref_counter_wf);
}

proof fn eof_create_thread_process_management_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(staging_thread_ptr),
        !pre.thr_mp.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set().subset_of(pre.ctn_mp.dom()),
        pre.sched_mp.dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        create_thread_from_staged_page_eof_transition_framing(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, process_node_addr, sched_node_addr),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        thread_perms_wf(post.thr_mp),
        scheduler_perms_wf(post.sched_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
    ensures
        post.process_management_inv(),
{
    reveal(create_thread_from_staged_page_eof_transition_framing);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, pre.prc_mp)) by { reveal(container_process_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        assert(per_container_process_tree_wf(post.ctn_mp, pre.prc_mp)) by { reveal(per_container_process_tree_wf); };
        per_container_process_tree_wf_preserved_for_tree_fields_eq(post.ctn_mp, pre.prc_mp, post.prc_mp);
    };
    assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { reveal(container_endpoint_wf); };
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); };
    eof_create_thread_endpoint_ref_counter_wf(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, process_node_addr, sched_node_addr);
    assert(thread_endpoint_queue_wf(post.thr_mp, post.ep_mp)) by { reveal(thread_endpoint_queue_wf); };
    assert(thread_caller_callee_wf(post.thr_mp)) by { reveal(thread_caller_callee_wf); };
    assert(container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp)) by { reveal(container_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); reveal(container_thread_endpoint_wf); };
    assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { reveal(container_scheduler_wf); };
    assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
    assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { reveal(container_cpu_offline_flags_wf); };
    assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); };
    assert(container_thread_wf(post.ctn_mp, post.thr_mp)) by { reveal(container_thread_wf); pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set_ensures(); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, process_ptr); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
    assert(thread_cpu_wf(post.thr_mp, post.cpu_arr)) by { reveal(thread_cpu_wf); };
    assert(thread_dangling_chain_end_wf(post.thr_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thr_mp, post.thr_mp); };
}

pub(super) proof fn eof_create_thread_inv(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, process_node_addr: usize, sched_node_addr: usize,
)
    requires
        pre.inv(),
        page_ptr_valid(page_ptr),
        pre.prc_mp.dom().contains(process_ptr),
        !pre.prc_mp.spec_index(process_ptr).view().zombie,
        pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        pre.thr_mp.dom().contains(staging_thread_ptr),
        !pre.thr_mp.dom().contains(page_ptr),
        page_ptr != staging_thread_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().to_set().subset_of(pre.ctn_mp.dom()),
        pre.sched_mp.dom().contains(scheduler_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= Set::<PagePtr>::empty().insert(page_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
        pre.thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
        create_thread_from_staged_page_eof_transition_framing(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, process_node_addr, sched_node_addr),
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        thread_perms_wf(post.thr_mp),
        scheduler_perms_wf(post.sched_mp),
        process_thread_wf(post.prc_mp, post.thr_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
    ensures
        post.inv(),
{
    eof_create_thread_memory_management_inv(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, process_node_addr, sched_node_addr);
    eof_create_thread_process_management_inv(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, process_node_addr, sched_node_addr);
    reveal(create_thread_from_staged_page_eof_transition_framing);
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(container_cpu_wf);
    };
}

/// The create-thread summary yields the new-thread step fields; container scheduler injectivity comes from `pre`.
pub(super) proof fn eof_create_thread_new_thread_fields(
    pre: KernelK, post: KernelK, page_ptr: PagePtr, process_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    scheduler_ptr: RwLockSchedulerPtr, cpu_id: CpuId, process_node_addr: usize, sched_node_addr: usize, initial_regs: Registers,
)
    requires
        pre.inv(),
        pre.prc_mp.dom().contains(process_ptr),
        pre.thr_mp.dom().contains(staging_thread_ptr),
        !pre.thr_mp.dom().contains(page_ptr),
        pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 1,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr,
        create_thread_from_staged_page_eof_transition_framing(pre, post, page_ptr, process_ptr, staging_thread_ptr, container_ptr, scheduler_ptr, cpu_id, process_node_addr, sched_node_addr),
        post.thr_mp.spec_index(page_ptr).view().trap_frame.is_some(),
        *post.thr_mp.spec_index(page_ptr).view().trap_frame.get_some_0() == initial_regs,
    ensures
        kernel_new_thread_fields(&pre, &post, process_ptr, staging_thread_ptr, container_ptr, cpu_id, page_ptr, initial_regs, None, pre.thr_mp.spec_index(staging_thread_ptr).view().syscall_progress.view()),
{
    reveal(create_thread_from_staged_page_eof_transition_framing); reveal(kernel_new_thread_fields);
    assert_seqs_equal!(Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| None::<RwLockEndpointPtr>) == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { None } else { None }), i => {});
}
}
