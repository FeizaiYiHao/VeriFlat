use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_spec::*;

verus! {
/// Removing the process `removed`, which holds no quota, from the folded set keeps the process quota folds when every
/// other member keeps its quotas.
pub(crate) proof fn lemma_process_effective_quota_folds_remove_zero(s: Set<RwLockProcessPtr>, pre_map: ProcessLockedMap, post_map: ProcessLockedMap, removed: RwLockProcessPtr)
    requires
        s.contains(removed),
        process_effective_quota_4k(pre_map.spec_index(removed)) == 0,
        process_effective_quota_2m(pre_map.spec_index(removed)) == 0,
        process_effective_quota_1g(pre_map.spec_index(removed)) == 0,
        forall|p: RwLockProcessPtr| #![trigger s.contains(p)] s.contains(p) && p != removed ==> {
            &&& process_effective_quota_4k(post_map.spec_index(p)) == process_effective_quota_4k(pre_map.spec_index(p))
            &&& process_effective_quota_2m(post_map.spec_index(p)) == process_effective_quota_2m(pre_map.spec_index(p))
            &&& process_effective_quota_1g(post_map.spec_index(p)) == process_effective_quota_1g(pre_map.spec_index(p))
        },
    ensures
        process_effective_quota_4k_fold_sum(s.remove(removed), post_map) == process_effective_quota_4k_fold_sum(s, pre_map),
        process_effective_quota_2m_fold_sum(s.remove(removed), post_map) == process_effective_quota_2m_fold_sum(s, pre_map),
        process_effective_quota_1g_fold_sum(s.remove(removed), post_map) == process_effective_quota_1g_fold_sum(s, pre_map),
{
    let pre_4k = |p: RwLockProcessPtr| process_effective_quota_4k(pre_map.spec_index(p));
    let post_4k = |p: RwLockProcessPtr| process_effective_quota_4k(post_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + pre_4k(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_4k(pre_map.spec_index(p)))
        && (|sum: int, p: RwLockProcessPtr| sum + post_4k(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_4k(post_map.spec_index(p)))
        && s.remove(removed).fold(0int, |sum: int, p: RwLockProcessPtr| sum + post_4k(p)) == s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + pre_4k(p)) - pre_4k(removed))
        by { lemma_set_fold_int_sum_remove(s, pre_4k, post_4k, removed); };
    let pre_2m = |p: RwLockProcessPtr| process_effective_quota_2m(pre_map.spec_index(p));
    let post_2m = |p: RwLockProcessPtr| process_effective_quota_2m(post_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + pre_2m(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(pre_map.spec_index(p)))
        && (|sum: int, p: RwLockProcessPtr| sum + post_2m(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_2m(post_map.spec_index(p)))
        && s.remove(removed).fold(0int, |sum: int, p: RwLockProcessPtr| sum + post_2m(p)) == s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + pre_2m(p)) - pre_2m(removed))
        by { lemma_set_fold_int_sum_remove(s, pre_2m, post_2m, removed); };
    let pre_1g = |p: RwLockProcessPtr| process_effective_quota_1g(pre_map.spec_index(p));
    let post_1g = |p: RwLockProcessPtr| process_effective_quota_1g(post_map.spec_index(p));
    assert((|sum: int, p: RwLockProcessPtr| sum + pre_1g(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_1g(pre_map.spec_index(p)))
        && (|sum: int, p: RwLockProcessPtr| sum + post_1g(p)) =~= (|sum: int, p: RwLockProcessPtr| sum + process_effective_quota_1g(post_map.spec_index(p)))
        && s.remove(removed).fold(0int, |sum: int, p: RwLockProcessPtr| sum + post_1g(p)) == s.fold(0int, |sum: int, p: RwLockProcessPtr| sum + pre_1g(p)) - pre_1g(removed))
        by { lemma_set_fold_int_sum_remove(s, pre_1g, post_1g, removed); };
}

proof fn kill_retire_eof_subsystems(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_perms_wf(post.it_mp),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allc_ptr).wf(),
    ensures post.subsystems_inv(),
{
    reveal(kill_retire_eof_transition_framing);
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    assert(pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn kill_retire_eof_page_states(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().parent == parent,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
    ensures
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        container_pages_wf(post.ctn_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    let process = pre.prc_mp.spec_index(target).view();
    let pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), process.pagetable);
    process_pages_wf_process_at(pre.prc_mp, pre.pg_arr, target);
    pagetable_pages_wf_root_page_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pt.cr3())).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: process.pagetable, table_type: PT_TYPE } }))
        by { pagetable_pages_wf_closure_page_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable, pt.cr3()); };
    assert(process.iommu_table is Some ==> {
        let it = process.iommu_table->Some_0;
        &&& pre.pg_arr.spec_index(page_ptr2page_index(it)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
        &&& pre.pg_arr.spec_index(page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: it, table_type: IOMMU_TYPE } })
    }) by { if process.iommu_table is Some { iommu_table_pages_wf_root_page_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0); iommu_table_pages_wf_closure_page_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0, pre.it_mp.spec_index(process.iommu_table->Some_0).view().cr3); } };
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by {
        thread_staged_4k_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
        thread_staged_1g_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
}

proof fn kill_retire_eof_process_object_pages(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().parent == parent,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        parent is Some ==> {
            let parent_ptr = parent->Some_0;
            &&& pre.prc_mp.dom().contains(parent_ptr)
            &&& parent_ptr != target
        },
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(ctn_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
        ({
            let process = pre.prc_mp.spec_index(target).view();
            let pages = kill_retire_pages(pre, target);
            &&& 3 <= pages.len()
            &&& pages[0] == page_ptr2page_index(target)
            &&& pages[1] == page_ptr2page_index(process.pagetable)
            &&& pages[2] == page_ptr2page_index(pre.pt_mp.spec_index(process.pagetable).view().cr3)
            &&& process.iommu_table is Some ==> {
                let it = process.iommu_table->Some_0;
                &&& pages.len() == 5
                &&& pages[3] == page_ptr2page_index(it)
                &&& pages[4] == page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)
            }
        }),
    ensures process_pages_wf(post.prc_mp, post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    let process = pre.prc_mp.spec_index(target).view();
    let pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), process.pagetable);
    process_pages_wf_process_at(pre.prc_mp, pre.pg_arr, target);
    pagetable_pages_wf_root_page_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pt.cr3())).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: process.pagetable, table_type: PT_TYPE } }))
        by { pagetable_pages_wf_closure_page_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable, pt.cr3()); };
    assert(process.iommu_table is Some ==> {
        let it = process.iommu_table->Some_0;
        &&& pre.pg_arr.spec_index(page_ptr2page_index(it)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
        &&& pre.pg_arr.spec_index(page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: it, table_type: IOMMU_TYPE } })
    }) by { if process.iommu_table is Some { iommu_table_pages_wf_root_page_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0); iommu_table_pages_wf_closure_page_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0, pre.it_mp.spec_index(process.iommu_table->Some_0).view().cr3); } };
    page_ptr_roundtrip(); page_index_roundtrip();
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); };
}

proof fn kill_retire_eof_pagetable_pages(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().parent == parent,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        parent is Some ==> {
            let parent_ptr = parent->Some_0;
            &&& pre.prc_mp.dom().contains(parent_ptr)
            &&& parent_ptr != target
        },
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(ctn_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
        ({
            let process = pre.prc_mp.spec_index(target).view();
            let pages = kill_retire_pages(pre, target);
            &&& 3 <= pages.len()
            &&& pages[0] == page_ptr2page_index(target)
            &&& pages[1] == page_ptr2page_index(process.pagetable)
            &&& pages[2] == page_ptr2page_index(pre.pt_mp.spec_index(process.pagetable).view().cr3)
            &&& process.iommu_table is Some ==> {
                let it = process.iommu_table->Some_0;
                &&& pages.len() == 5
                &&& pages[3] == page_ptr2page_index(it)
                &&& pages[4] == page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)
            }
        }),
    ensures pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    let process = pre.prc_mp.spec_index(target).view();
    let pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), process.pagetable);
    process_pages_wf_process_at(pre.prc_mp, pre.pg_arr, target);
    pagetable_pages_wf_root_page_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pt.cr3())).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: process.pagetable, table_type: PT_TYPE } }))
        by { pagetable_pages_wf_closure_page_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable, pt.cr3()); };
    assert(process.iommu_table is Some ==> {
        let it = process.iommu_table->Some_0;
        &&& pre.pg_arr.spec_index(page_ptr2page_index(it)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
        &&& pre.pg_arr.spec_index(page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: it, table_type: IOMMU_TYPE } })
    }) by { if process.iommu_table is Some { iommu_table_pages_wf_root_page_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0); iommu_table_pages_wf_closure_page_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0, pre.it_mp.spec_index(process.iommu_table->Some_0).view().cr3); } };
    page_ptr_roundtrip(); page_index_roundtrip();
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(process_pages_wf); reveal(pagetable_pages_wf); };
}

proof fn kill_retire_eof_iommu_table_pages(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().parent == parent,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        parent is Some ==> {
            let parent_ptr = parent->Some_0;
            &&& pre.prc_mp.dom().contains(parent_ptr)
            &&& parent_ptr != target
        },
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(ctn_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
        ({
            let process = pre.prc_mp.spec_index(target).view();
            let pages = kill_retire_pages(pre, target);
            &&& 3 <= pages.len()
            &&& pages[0] == page_ptr2page_index(target)
            &&& pages[1] == page_ptr2page_index(process.pagetable)
            &&& pages[2] == page_ptr2page_index(pre.pt_mp.spec_index(process.pagetable).view().cr3)
            &&& process.iommu_table is Some ==> {
                let it = process.iommu_table->Some_0;
                &&& pages.len() == 5
                &&& pages[3] == page_ptr2page_index(it)
                &&& pages[4] == page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)
            }
        }),
    ensures iommu_table_pages_wf(post.it_mp, post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    let process = pre.prc_mp.spec_index(target).view();
    let pt = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), process.pagetable);
    process_pages_wf_process_at(pre.prc_mp, pre.pg_arr, target);
    pagetable_pages_wf_root_page_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pt.cr3())).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: process.pagetable, table_type: PT_TYPE } }))
        by { pagetable_pages_wf_closure_page_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable, pt.cr3()); };
    assert(process.iommu_table is Some ==> {
        let it = process.iommu_table->Some_0;
        &&& pre.pg_arr.spec_index(page_ptr2page_index(it)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
        &&& pre.pg_arr.spec_index(page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: it, table_type: IOMMU_TYPE } })
    }) by { if process.iommu_table is Some { iommu_table_pages_wf_root_page_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0); iommu_table_pages_wf_closure_page_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0, pre.it_mp.spec_index(process.iommu_table->Some_0).view().cr3); } };
    page_ptr_roundtrip(); page_index_roundtrip();
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(process_pages_wf); reveal(iommu_table_pages_wf); };
}

proof fn kill_retire_eof_process_kernel_pages_owner(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
        ({
            let process = pre.prc_mp.spec_index(target).view();
            let pages = kill_retire_pages(pre, target);
            &&& 3 <= pages.len()
            &&& pages[0] == page_ptr2page_index(target)
            &&& pages[1] == page_ptr2page_index(process.pagetable)
            &&& pages[2] == page_ptr2page_index(pre.pt_mp.spec_index(process.pagetable).view().cr3)
            &&& process.iommu_table is Some ==> {
                let it = process.iommu_table->Some_0;
                &&& pages.len() == 5
                &&& pages[3] == page_ptr2page_index(it)
                &&& pages[4] == page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)
            }
        }),
    ensures process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    page_ptr_roundtrip(); page_index_roundtrip();
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { reveal(process_object_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf); };
}

proof fn kill_retire_eof_page_object_owner(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
        ({
            let process = pre.prc_mp.spec_index(target).view();
            let pages = kill_retire_pages(pre, target);
            &&& 3 <= pages.len()
            &&& pages[0] == page_ptr2page_index(target)
            &&& pages[1] == page_ptr2page_index(process.pagetable)
            &&& pages[2] == page_ptr2page_index(pre.pt_mp.spec_index(process.pagetable).view().cr3)
            &&& process.iommu_table is Some ==> {
                let it = process.iommu_table->Some_0;
                &&& pages.len() == 5
                &&& pages[3] == page_ptr2page_index(it)
                &&& pages[4] == page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)
            }
        }),
    ensures page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    page_ptr_roundtrip(); page_index_roundtrip();
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by { reveal(page_object_owner_wf); reveal(container_owned_pages_wf); };
}

proof fn kill_retire_eof_page_pagetable(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
    ensures page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, target); process_emptied_tables_wf_at(pre.prc_mp, pre.pt_mp, pre.pt_lower.view(), pre.it_mp, pre.pg_arr, target);
    assert(page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); reveal(pagetable_lower_wf); };
}

proof fn kill_retire_eof_container_process_mappings(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
    ensures container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    process_perms_wf_at(pre.prc_mp, target); process_emptied_tables_wf_at(pre.prc_mp, pre.pt_mp, pre.pt_lower.view(), pre.it_mp, pre.pg_arr, target);
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
        reveal(container_process_page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(process_pagetable_wf);
    };
}

proof fn kill_retire_eof_iommu_mappings(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
    ensures page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(process_iommu_table_wf); };
}

proof fn kill_retire_eof_table_matches(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
    ensures
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp),
{
    reveal(kill_retire_eof_transition_framing);
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf); };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
}

proof fn kill_retire_eof_allocator(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
    ensures
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_page_ptrs_wf(post.allc_1g_mp),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_retire_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_index_valid_imply_page_ptr_valid(); page_ptr_roundtrip(); page_index_roundtrip();
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ctn_ptr);
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, target); reveal(container_kill_retire_wf); reveal(container_allocator_wf); };
    assert(allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf); reveal(allocator_free_page_ptrs_wf); };
}

proof fn kill_retire_eof_quota(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().parent == parent,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        parent is Some ==> {
            let parent_ptr = parent->Some_0;
            &&& pre.prc_mp.dom().contains(parent_ptr)
            &&& parent_ptr != target
            &&& pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr)
        },
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_retire_eof_transition_framing);
    let owned = pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view();
    assert({
        &&& process_effective_quota_4k_fold_sum(owned.remove(target), post.prc_mp) == process_effective_quota_4k_fold_sum(owned, pre.prc_mp)
        &&& process_effective_quota_2m_fold_sum(owned.remove(target), post.prc_mp) == process_effective_quota_2m_fold_sum(owned, pre.prc_mp)
        &&& process_effective_quota_1g_fold_sum(owned.remove(target), post.prc_mp) == process_effective_quota_1g_fold_sum(owned, pre.prc_mp)
    }) by { reveal(container_process_wf); process_perms_wf_at(pre.prc_mp, target); lemma_process_effective_quota_folds_remove_zero(owned, pre.prc_mp, post.prc_mp, target); };
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); reveal(container_allocator_wf); lemma_process_effective_quota_4k_fold_sum_eq_forall(); };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by { reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); lemma_process_effective_quota_2m_fold_sum_eq_forall(); };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_1g_wf); reveal(container_process_wf); lemma_process_effective_quota_1g_fold_sum_eq_forall(); };
}

/// Retiring the empty zombie `target` and returning its pages to shard `cpu_id` of its container's 4K allocator keeps the
/// subsystem and memory-management invariants.
pub(crate) proof fn kill_retire_eof_memory(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent: Option<RwLockProcessPtr>, ctn_ptr: RwLockContainerPtr,
    allc_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().parent == parent,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == ctn_ptr,
        parent is Some ==> {
            let parent_ptr = parent->Some_0;
            &&& pre.prc_mp.dom().contains(parent_ptr)
            &&& parent_ptr != target
            &&& pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr)
            &&& pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr())
            &&& pre.prc_mp.spec_index(parent_ptr).view().children.map().spec_index(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()) == target
        },
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == allc_ptr,
        pre.allc_4k_mp.dom().contains(allc_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == ctn_ptr
        },
        page_array_wf(post.pg_arr),
        container_perms_wf(post.ctn_mp),
        process_perms_wf(post.prc_mp),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_perms_wf(post.it_mp),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allc_ptr).wf(),
    ensures
        post.subsystems_inv(),
        post.memory_management_inv(),
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    kill_retire_eof_subsystems(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_page_states(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_process_object_pages(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_pagetable_pages(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_iommu_table_pages(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_process_kernel_pages_owner(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_page_object_owner(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_page_pagetable(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_container_process_mappings(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_iommu_mappings(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_table_matches(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_allocator(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
    kill_retire_eof_quota(pre, post, cpu_id, target, parent, ctn_ptr, allc_ptr);
}
} // verus!
