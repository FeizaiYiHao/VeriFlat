use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_spec::{kill_retire_pages, kill_retire_tables_emptied};
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_pages::kill_retire_pages_held_and_owned;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_retire_eof_memory::lemma_process_effective_quota_folds_remove_zero;

verus! {
/// Retiring the empty zombie root process `target` of the marked container `container_ptr`: the process leaves the
/// process map while every other process keeps its state, and the container drops it from its processes and clears its
/// zombie flag; its page table and IOMMU table, which only hold their root tables, leave their maps; every page in
/// `kill_retire_pages(pre, target)` returns through its free-list node to shard `cpu_id` of the container's 4K
/// allocator `allocator_ptr`, whose quota grows by the number of those pages.
#[verifier::opaque]
pub open spec fn kill_container_retire_root_eof_transition_framing(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
) -> bool {
    let process = pre.prc_mp.spec_index(target);
    let pagetable = process.view().pagetable;
    let iommu_table = process.view().iommu_table;
    let pages = kill_retire_pages(pre, target);
    let n = pages.len();
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    let pre_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let post_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    let pre_cache = pre_allocator.cpu_caches.spec_index(cpu_id).view();
    let post_cache = post_allocator.cpu_caches.spec_index(cpu_id).view();
    &&& post == (KernelK { prc_mp: post.prc_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, it_mp: post.it_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.prc_mp.dom() == pre.prc_mp.dom().remove(target)
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] post.prc_mp.dom().contains(p) ==> {
        &&& post.prc_mp.spec_index(p) == pre.prc_mp.spec_index(p)
        &&& post.prc_mp.view().spec_index(p).is_init() == pre.prc_mp.view().spec_index(p).is_init()
        &&& post.prc_mp.view().spec_index(p).addr() == pre.prc_mp.view().spec_index(p).addr()
    }
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) && c != container_ptr ==> post.ctn_mp.spec_index(c) == pre.ctn_mp.spec_index(c)
    &&& post.ctn_mp.spec_index(container_ptr).view() == (Container { zombie: false, ..pre.ctn_mp.spec_index(container_ptr).view() })
    &&& post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata()
    &&& post.ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
        owned_processes: Ghost(pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target)), ..pre.ctn_mp.spec_index(container_ptr).view_ghost() })
    &&& post.ctn_mp.spec_index(container_ptr).is_init() == pre.ctn_mp.spec_index(container_ptr).is_init()
    &&& post.ctn_mp.spec_index(container_ptr).locking_thread() == pre.ctn_mp.spec_index(container_ptr).locking_thread()
    &&& post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed()
    &&& post.ctn_mp.spec_index(container_ptr).killer_info() == pre.ctn_mp.spec_index(container_ptr).killer_info()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr)
    &&& post.pt_mp.dom() =~= pre.pt_mp.dom().remove(pagetable)
    &&& post.pt_lower.view() == pre.pt_lower.view().remove(pagetable)
    &&& forall|r: RwLockPageTableRoot| #![trigger pagetable_c(post.pt_mp, post.pt_lower.view(), r)]
        post.pt_mp.dom().contains(r) ==> pagetable_c(post.pt_mp, post.pt_lower.view(), r) == pagetable_c(pre.pt_mp, pre.pt_lower.view(), r)
    &&& forall|t: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(t)] post.pt_mp.dom().contains(t) ==> post.pt_mp.spec_index(t) == pre.pt_mp.spec_index(t)
    &&& forall|t: RwLockPageTableRoot| #![trigger post.pt_mp.lock_id_by_key(t)] post.pt_mp.dom().contains(t) ==> post.pt_mp.lock_id_by_key(t) == pre.pt_mp.lock_id_by_key(t)
    &&& post.it_mp.dom() =~= match iommu_table { Some(it) => pre.it_mp.dom().remove(it), None => pre.it_mp.dom() }
    &&& forall|t: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(t)] post.it_mp.dom().contains(t) ==> post.it_mp.spec_index(t) == pre.it_mp.spec_index(t)
    &&& forall|t: RwLockPageTableRoot| #![trigger post.it_mp.lock_id_by_key(t)] post.it_mp.dom().contains(t) ==> post.it_mp.lock_id_by_key(t) == pre.it_mp.lock_id_by_key(t)
    &&& forall|i: PageIndex| #![trigger post.pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !pages.contains(i) ==> post.pg_arr.spec_index(i) == pre.pg_arr.spec_index(i)
    &&& forall|k: int| #![trigger pages[k]] 0 <= k < n ==> {
        let pre_page = pre.pg_arr.spec_index(pages[k]).view();
        let post_page = post.pg_arr.spec_index(pages[k]).view();
        &&& post_page.is_init() == pre_page.is_init()
        &&& post_page.view_rodata() == pre_page.view_rodata()
        &&& post_page.view_ghost() == pre_page.view_ghost()
        &&& post_page.locking_thread() == pre_page.locking_thread()
        &&& post_page.being_killed() == pre_page.being_killed()
        &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
        &&& post_page.view() == (Page { state: free_state, free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    }
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + n
    &&& post_cache.view().view().len() == pre_cache.view().view().len() + n
    &&& forall|p: PagePtr| #![trigger post_cache.view().view().contains(p)]
        post_cache.view().view().contains(p) == (pre_cache.view().view().contains(p) || pages.contains(page_ptr2page_index(p)) && page_ptr_valid(p))
    &&& forall|a: usize| #![trigger pre_cache.view().map().dom().contains(a)]
        pre_cache.view().map().dom().contains(a) ==> post_cache.view().map().dom().contains(a) && post_cache.view().map().spec_index(a) == pre_cache.view().map().spec_index(a)
    &&& forall|k: int| #![trigger pages[k]] 0 <= k < n ==> {
        let node = pre.pg_arr.spec_index(pages[k]).view().view().free_list_node_storage.addr();
        &&& !pre_cache.view().map().dom().contains(node)
        &&& post_cache.view().map().dom().contains(node)
        &&& post_cache.view().map().spec_index(node) == page_index2page_ptr(pages[k])
    }
    &&& post_allocator.cpu_caches.entries_unchanged_except(&pre_allocator.cpu_caches, cpu_id)
    &&& post_cache.locking_thread() == pre_cache.locking_thread()
    &&& post_allocator.global_pool == pre_allocator.global_pool
    &&& post_allocator.owning_container == pre_allocator.owning_container
    &&& post_allocator.quota.view().value == pre_allocator.quota.view().value + n
    &&& post_allocator.quota.view() == (AllocatorQuota { value: post_allocator.quota.view().value, ..pre_allocator.quota.view() })
    &&& post_allocator.quota.is_init() == pre_allocator.quota.is_init()
    &&& post_allocator.quota.view_rodata() == pre_allocator.quota.view_rodata()
    &&& post_allocator.quota.view_ghost() == pre_allocator.quota.view_ghost()
    &&& post_allocator.quota.locking_thread() == pre_allocator.quota.locking_thread()
    &&& post_allocator.quota.being_killed() == pre_allocator.quota.being_killed()
}

proof fn kill_container_retire_root_eof_subsystems(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == container_ptr
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
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures post.subsystems_inv(),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    reveal(KernelK::default_pagetable_wf);
}

proof fn kill_container_retire_root_eof_page_states(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == container_ptr
        },
    ensures
        allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_page_owner_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        container_pages_wf(post.pg_arr, post.ctn_mp),
        thread_pages_wf(post.thr_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp),
        thread_staged_pages_wf(post.thr_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    let process = pre.prc_mp.spec_index(target).view();
    let pt = pagetable_c(pre.pt_mp, pre.pt_lower.view(), process.pagetable);
    process_pages_wf_process_entry_at(pre.pg_arr, pre.prc_mp, target);
    pagetable_pages_wf_root_entry_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pt.cr3())).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: process.pagetable, table_type: PT_TYPE } }))
        by { pagetable_pages_wf_closure_entry_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable, pt.cr3()); };
    assert(process.iommu_table is Some ==> {
        let it = process.iommu_table->Some_0;
        &&& pre.pg_arr.spec_index(page_ptr2page_index(it)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
        &&& pre.pg_arr.spec_index(page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: it, table_type: IOMMU_TYPE } })
    }) by {
        if process.iommu_table is Some { iommu_table_pages_wf_root_entry_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0); iommu_table_pages_wf_closure_entry_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0, pre.it_mp.spec_index(process.iommu_table->Some_0).view().cr3); }
    };
    assert(allocator_pages_wf(post.pg_arr, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_4k_mp, post.allc_4k_mp);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_2m_mp, post.allc_2m_mp);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.allc_1g_mp, post.allc_1g_mp);
    };
    assert(container_page_owner_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.pg_arr, post.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.ctn_mp, post.ctn_mp); };
    assert(thread_pages_wf(post.thr_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { cpu_set_pages_wf_preserved_for_page_state_eq(pre.cpu_set_mp, post.cpu_set_mp, pre.pg_arr, post.pg_arr); };
    assert(pcid_allocator_pages_wf(post.pg_arr, post.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr, pre.pcid_allc_mp, post.pcid_allc_mp); };
    assert(thread_staged_pages_wf(post.thr_mp, post.pg_arr)) by {
        thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
        thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thr_mp, post.thr_mp, pre.pg_arr, post.pg_arr);
    };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
}

proof fn kill_container_retire_root_eof_process_pages(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == container_ptr
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
    ensures
        process_pages_wf(post.pg_arr, post.prc_mp),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    let process = pre.prc_mp.spec_index(target).view();
    let pt = pagetable_c(pre.pt_mp, pre.pt_lower.view(), process.pagetable);
    process_pages_wf_process_entry_at(pre.pg_arr, pre.prc_mp, target);
    pagetable_pages_wf_root_entry_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable);
    assert(pre.pg_arr.spec_index(page_ptr2page_index(pt.cr3())).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: process.pagetable, table_type: PT_TYPE } }))
        by { pagetable_pages_wf_closure_entry_at(pre.pt_mp, pre.pt_lower.view(), pre.pg_arr, process.pagetable, pt.cr3()); };
    assert(process.iommu_table is Some ==> {
        let it = process.iommu_table->Some_0;
        &&& pre.pg_arr.spec_index(page_ptr2page_index(it)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } })
        &&& pre.pg_arr.spec_index(page_ptr2page_index(pre.it_mp.spec_index(it).view().cr3)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: it, table_type: IOMMU_TYPE } })
    }) by {
        if process.iommu_table is Some { iommu_table_pages_wf_root_entry_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0); iommu_table_pages_wf_closure_entry_at(pre.it_mp, pre.pg_arr, process.iommu_table->Some_0, pre.it_mp.spec_index(process.iommu_table->Some_0).view().cr3); }
    };
    page_ptr_roundtrip(); page_index_roundtrip();
    assert(process_pages_wf(post.pg_arr, post.prc_mp)) by { reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(process_pages_wf); reveal(pagetable_pages_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(process_pages_wf); reveal(iommu_table_pages_wf); };
}

proof fn kill_container_retire_root_eof_process_kernel_pages_owner(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
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
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == container_ptr
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
    ensures
        process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp),
        page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    page_ptr_roundtrip(); page_index_roundtrip();
    assert(process_kernel_pages_owner_wf(post.pg_arr, post.prc_mp, post.pt_mp, post.it_mp)) by {
        reveal(process_kernel_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match);
    };
    assert(page_object_owner_wf(post.pg_arr, post.ctn_mp, post.thr_mp)) by { reveal(page_object_owner_wf); reveal(container_page_owner_wf); };
}

proof fn kill_container_retire_root_eof_mappings(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
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
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == container_ptr
        },
    ensures
        page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    assert(page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); reveal(pagetable_lower_wf); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by {
        reveal(container_process_page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); reveal(process_pagetable_match);
    };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); reveal(process_iommu_table_match); };
    assert(process_pagetable_match(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_match); };
    assert(process_iommu_table_match(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_match); };
    assert(pagetable_no_huge_leaf_wf(post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(pagetable_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp)) by { reveal(process_emptied_tables_wf); reveal(process_pagetable_match); reveal(process_iommu_table_match); };
}

proof fn kill_container_retire_root_eof_allocator(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == container_ptr
        },
    ensures
        post.allocator_free_pages_wf(),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr),
        container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr),
        container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_index_valid_imply_page_ptr_valid(); page_ptr_roundtrip(); page_index_roundtrip();
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp);
    };
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, container_ptr);
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by {
        container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, target); reveal(container_kill_retire_wf); reveal(container_allocator_wf);
    };
    assert(container_allocator_global_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_cpu_cache_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_free_4k_page_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); };
    assert(container_allocator_free_2m_page_wf(post.allc_2m_mp, post.pg_arr)) by {
        reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf);
    };
    assert(container_allocator_free_1g_page_wf(post.allc_1g_mp, post.pg_arr)) by {
        reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf);
    };
}

proof fn kill_container_retire_root_eof_quota(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        kill_retire_tables_emptied(pre, target),
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    let owned = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    assert({
        &&& process_effective_quota_4k_fold_sum(owned.remove(target), post.prc_mp) == process_effective_quota_4k_fold_sum(owned, pre.prc_mp)
        &&& process_effective_quota_2m_fold_sum(owned.remove(target), post.prc_mp) == process_effective_quota_2m_fold_sum(owned, pre.prc_mp)
        &&& process_effective_quota_1g_fold_sum(owned.remove(target), post.prc_mp) == process_effective_quota_1g_fold_sum(owned, pre.prc_mp)
    }) by { reveal(container_process_wf); process_perms_wf_at(pre.prc_mp, target); lemma_process_effective_quota_folds_remove_zero(owned, pre.prc_mp, post.prc_mp, target); };
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp)) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); reveal(container_allocator_wf); lemma_process_effective_quota_4k_fold_sum_eq_forall();
    };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_2m_mp)) by {
        reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); lemma_process_effective_quota_2m_fold_sum_eq_forall();
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_1g_mp)) by {
        reveal(container_process_allocator_quota_1g_wf); reveal(container_process_wf); lemma_process_effective_quota_1g_fold_sum_eq_forall();
    };
}

/// Retiring the empty zombie root `target` and returning its pages to shard `cpu_id` of its container's 4K allocator
/// keeps the subsystem and memory-management invariants.
pub(crate) proof fn kill_container_retire_root_eof_memory(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        index_valid(NUM_CPUS, cpu_id),
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
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        forall|k: int| #![trigger kill_retire_pages(pre, target)[k]] 0 <= k < kill_retire_pages(pre, target).len() ==> {
            &&& index_valid(NUM_PAGES, kill_retire_pages(pre, target)[k])
            &&& kill_retire_pages(pre, target)[k] == page_ptr2page_index(target) || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().pagetable)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).view().cr3)
                || pre.prc_mp.spec_index(target).view().iommu_table is Some && (kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0)
                || kill_retire_pages(pre, target)[k] == page_ptr2page_index(pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).view().cr3))
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().state is Allocated4k
            &&& pre.pg_arr.spec_index(kill_retire_pages(pre, target)[k]).view().view().owning_container == container_ptr
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
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
    ensures
        post.subsystems_inv(),
        post.memory_management_inv(),
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thr_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    kill_container_retire_root_eof_subsystems(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_page_states(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_process_pages(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_process_kernel_pages_owner(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_mappings(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_allocator(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_quota(pre, post, cpu_id, target, container_ptr, allocator_ptr);
}

/// Retiring the empty zombie root `target` keeps the container tree and the container, endpoint, scheduler, cpu-set,
/// offline-flag, PCID-allocator, and thread relations.
pub(crate) proof fn kill_container_retire_root_eof_container_relations(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.dom().contains(container_ptr),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
        container_endpoint_wf(post.ctn_mp, post.ep_mp),
        thread_endpoint_ref_counter_wf(post.thr_mp, post.ep_mp),
        thread_endpoint_queue_wf(post.thr_mp, post.ep_mp),
        thread_caller_callee_wf(post.thr_mp),
        thread_dangling_chain_end_wf(post.thr_mp),
        container_thread_endpoint_wf(post.ctn_mp, post.thr_mp, post.ep_mp),
        container_scheduler_wf(post.ctn_mp, post.sched_mp),
        container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp),
        container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp),
        container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp),
        container_thread_scheduler_wf(post.ctn_mp, post.thr_mp, post.sched_mp),
        container_thread_wf(post.ctn_mp, post.thr_mp),
        thread_cpu_wf(post.thr_mp, post.cpu_arr),
{
    reveal(kill_container_retire_root_eof_transition_framing);
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

/// Retiring the empty zombie root `target` keeps the container-cpu relation and the process PCID, cpu, thread,
/// kill-mark, lock-state, and emptied-thread invariants.
pub(crate) proof fn kill_container_retire_root_eof_process_relations(
    pre: KernelK, post: KernelK, lctx: LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
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
        pre.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        forall|d: RwLockProcessPtr| #![trigger lctx.process_lock_map().dom().contains(d)] lctx.process_lock_map().dom().contains(d) && pre.prc_mp.spec_index(d).killer_info() is Some
            ==> pre.prc_mp.spec_index(d).killer_info()->Some_0.process != target && pre.prc_mp.spec_index(d).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        forall|c: RwLockContainerPtr| #![trigger lctx.container_lock_map().dom().contains(c)] lctx.container_lock_map().dom().contains(c) && pre.ctn_mp.spec_index(c).killer_info() is Some
            ==> pre.ctn_mp.spec_index(c).killer_info()->Some_0.process != target,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(lctx.thread_id()) ==> !pre.thr_mp.spec_index(u).being_killed(),
    ensures
        container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
        process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp),
        process_cpu_wf(post.prc_mp, post.cpu_arr),
        process_thread_wf(post.prc_mp, post.thr_mp),
        process_kill_mark_wf(post.ctn_mp, post.prc_mp),
        container_kill_mark_wf(post.ctn_mp, post.prc_mp),
        cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp),
        process_state_lock_wf(post.prc_mp),
        process_emptied_threads_wf(post.prc_mp, post.thr_mp),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by { reveal(container_cpu_wf); reveal(process_cpu_wf); };
    assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); reveal(container_pcid_allocator_wf); };
    assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
    assert(process_thread_wf(post.prc_mp, post.thr_mp)) by { pre.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), target); reveal(process_thread_wf); };
    assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); reveal(container_process_wf); reveal(per_container_process_tree_wf); reveal(process_children_parent_wf); };
    assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); };
    assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); reveal(container_kill_mark_wf); reveal(LockedMap::typed_lock_map_aligned); };
    assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
    assert(process_emptied_threads_wf(post.prc_mp, post.thr_mp)) by { reveal(process_emptied_threads_wf); };
}

/// Retiring the empty zombie root `target` keeps the IOMMU root-table, PCI-function ownership, IOTLB, and IOMMU-table
/// lock invariants.
pub(crate) proof fn kill_container_retire_root_eof_iommu(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
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
    reveal(kill_container_retire_root_eof_transition_framing);
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); reveal(process_pci_function_ownership_wf); process_iommu_table_match_process_at(pre.prc_mp, pre.it_mp, target); };
    assert(iommu_tlb_wf_spec(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf_spec); reveal(iommu_root_table_process_wf); };
    assert(iommu_table_lock_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_table_lock_wf); reveal(process_iommu_table_match); };
}

/// A CPU/PCID association that the TLB and dirty-map invariants constrain belongs to neither the retired target nor its
/// page table: a current PCID belongs to a running process, which is no zombie, and a live TLB entry for the target's
/// page table would have to be a subset of its empty mappings.
broadcast proof fn kill_container_retire_root_eof_tlb_entry(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, c: CpuId, p: Pcid,
)
    requires
        cpu_array_wf(pre.cpu_arr, pre.dflt_pt.view()),
        process_cpu_wf(pre.prc_mp, pre.cpu_arr),
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        cpu_dirty_map_proc_pcid_match(pre.prc_mp, pre.cpu_arr, pre.pcid_needflush, pre.cpu_tlb),
        tlb_wf_spec(pre.cpu_tlb, pre.pt_mp, pre.pt_lower.view(), pre.cpu_arr, pre.pcid_needflush),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
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
        #![trigger kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr), post.cpu_tlb.spec_index((c, p))]
        #![trigger kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr), post.cpu_arr.spec_index(c).view().view().tlb_dirty_bitmap().spec_index(p)]
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
    reveal(kill_container_retire_root_eof_transition_framing);
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

/// Retiring the empty zombie root `target` keeps the cpu dirty-map and TLB invariants.
pub(crate) proof fn kill_container_retire_root_eof_tlb(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
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
        tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    assert(cpu_dirty_map_contains_container_processes(post.ctn_mp, post.cpu_set_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(container_cpu_wf); broadcast use kill_container_retire_root_eof_tlb_entry; };
    assert(cpu_dirty_map_proc_pcid_match(post.prc_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by { reveal(cpu_dirty_map_proc_pcid_match); broadcast use kill_container_retire_root_eof_tlb_entry; };
    assert(cpu_dirty_map_contains_pagetable_pcid_match(post.pt_mp, post.cpu_arr, post.pcid_needflush, post.cpu_tlb)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); broadcast use kill_container_retire_root_eof_tlb_entry; };
    assert(tlb_wf_spec(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(tlb_wf_spec); broadcast use kill_container_retire_root_eof_tlb_entry; };
}

/// Every member of the tree whose root `root_process` has no child is that root.
broadcast proof fn kill_container_retire_root_eof_only_root(process_perms: ProcessLockedMap, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, p_ptr: RwLockProcessPtr)
    requires
        process_tree_wf(root_process, process_tree_dom, process_perms),
        process_perms.spec_index(root_process).view().children.view().len() == 0,
    ensures #![trigger process_tree_wf(root_process, process_tree_dom, process_perms), process_tree_dom.contains(p_ptr)] process_tree_dom.contains(p_ptr) ==> p_ptr == root_process,
    decreases process_perms.spec_index(p_ptr).view_rodata().view().depth,
{
    if process_tree_dom.contains(p_ptr) && p_ptr != root_process {
        process_root_wf_at(root_process, process_tree_dom, process_perms, p_ptr); process_children_parent_wf_parent_at(root_process, process_tree_dom, process_perms, p_ptr);
        let parent_ptr = process_perms.spec_index(p_ptr).view_rodata().view().parent->Some_0;
        process_children_parent_wf_at(root_process, process_tree_dom, process_perms, parent_ptr, p_ptr);
        kill_container_retire_root_eof_only_root(process_perms, root_process, process_tree_dom, parent_ptr);
    }
}

/// Retiring the childless root `target`, the only process of its container `container_ptr`, which is write-held and not
/// the root container, leaves that container without processes and keeps every container's process set consistent with
/// the process map, every process tree well formed, and the root container's root process.
pub(crate) proof fn kill_container_retire_root_eof_tree(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        0 < pre.prc_mp.spec_index(target).view_rodata().view().container_depth,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view().root_process == target,
        pre.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
    ensures
        post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
        post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process),
{
    reveal(kill_container_retire_root_eof_transition_framing);
    let tree = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, target); per_container_process_tree_wf_at(pre.ctn_mp, pre.prc_mp, container_ptr);
    assert(process_tree_wf(target, tree, pre.prc_mp));
    assert(tree.remove(target) =~= Set::<RwLockProcessPtr>::empty()) by { broadcast use kill_container_retire_root_eof_only_root; };
    assert(container_ptr != pre.rt_ctn && pre.ctn_mp.dom().contains(pre.rt_ctn)) by { reveal(container_root_wf); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); broadcast use kill_container_retire_root_eof_only_root; };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        reveal(per_container_process_tree_wf); reveal(container_process_wf); process_no_change_to_tree_fields_imply_wf_forall();
    };
}

/// Retiring the empty zombie root process `target` of the marked, write-held container `container_ptr`, and returning
/// its pages to that container's 4K allocator, keeps the kernel invariant.
pub(crate) proof fn kill_container_retire_root_eof(
    pre: KernelK, post: KernelK, lctx: LocalContext, cpu_id: CpuId, target: RwLockProcessPtr, container_ptr: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_container_retire_root_eof_transition_framing(pre, post, cpu_id, target, container_ptr, allocator_ptr),
        index_valid(NUM_CPUS, cpu_id),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        0 < pre.prc_mp.spec_index(target).view_rodata().view().container_depth,
        pre.pt_mp.dom().contains(pre.prc_mp.spec_index(target).view().pagetable),
        pre.pt_mp.spec_index(pre.prc_mp.spec_index(target).view().pagetable).locking_thread() is Write,
        kill_retire_tables_emptied(pre, target),
        pre.prc_mp.spec_index(target).view().iommu_table is Some ==> pre.it_mp.dom().contains(pre.prc_mp.spec_index(target).view().iommu_table->Some_0) && pre.it_mp.spec_index(pre.prc_mp.spec_index(target).view().iommu_table->Some_0).locking_thread() is Write,
        pre.ctn_mp.dom().contains(container_ptr),
        pre.ctn_mp.spec_index(container_ptr).view().root_process == target,
        pre.ctn_mp.spec_index(container_ptr).locking_thread() is Write,
        pre.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        pre.allc_4k_mp.dom().contains(allocator_ptr),
        kill_retire_pages(pre, target).no_duplicates(),
        page_array_wf(post.pg_arr),
        post.ctn_mp.perms_wf(),
        post.prc_mp.perms_wf(),
        pagetable_perms_wf(post.pt_mp),
        pagetable_lower_wf(post.pt_mp, post.pt_lower.view()),
        pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view()),
        pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view()),
        pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_perms_wf(post.it_mp),
        post.allc_4k_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_ptr).wf(),
        pre.prc_mp.typed_lock_map_aligned(lctx.process_lock_map(), lctx.thread_id()),
        typed_lock_map_contains_mode(lctx.process_lock_map(), target, TypedLockMode::Write),
        forall|d: RwLockProcessPtr| #![trigger lctx.process_lock_map().dom().contains(d)] lctx.process_lock_map().dom().contains(d) && pre.prc_mp.spec_index(d).killer_info() is Some
            ==> pre.prc_mp.spec_index(d).killer_info()->Some_0.process != target && pre.prc_mp.spec_index(d).view_rodata().view().owning_container == container_ptr,
        pre.ctn_mp.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id()),
        forall|c: RwLockContainerPtr| #![trigger lctx.container_lock_map().dom().contains(c)] lctx.container_lock_map().dom().contains(c) && pre.ctn_mp.spec_index(c).killer_info() is Some
            ==> pre.ctn_mp.spec_index(c).killer_info()->Some_0.process != target,
        forall|u: RwLockThreadPtr| #![trigger pre.thr_mp.spec_index(u).locking_thread()]
            pre.thr_mp.dom().contains(u) && pre.thr_mp.spec_index(u).wlocked_by_thread(lctx.thread_id()) ==> !pre.thr_mp.spec_index(u).being_killed(),
    ensures
        post.inv(),
        post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
{
    assert(container_perms_wf(post.ctn_mp)) by { reveal(kill_container_retire_root_eof_transition_framing); reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(process_perms_wf(post.prc_mp)) by { reveal(kill_container_retire_root_eof_transition_framing); reveal(process_perms_wf); };
    kill_retire_pages_held_and_owned(pre, target, kill_retire_pages(pre, target).to_set(), allocator_ptr, cpu_id);
    kill_container_retire_root_eof_memory(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_container_relations(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_process_relations(pre, post, lctx, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_iommu(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_tlb(pre, post, cpu_id, target, container_ptr, allocator_ptr);
    kill_container_retire_root_eof_tree(pre, post, cpu_id, target, container_ptr, allocator_ptr);
}
} // verus!
