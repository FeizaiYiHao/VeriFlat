use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof::kill_container_retire_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof_entry::*;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_alloc_page::free_4k_page::kill_container_quota_fold::lemma_container_allocator_2m_quota_bounded;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::free_4k_page::kill_container_quota_fold::lemma_container_allocator_2m_quota_bounded;

verus! {
/// After the retire a merged tail or a page the retired container did not own is unchanged; any other page it owned is an object page now free on a global list of `owner_ptr`, which owns it.
pub(crate) proof fn kill_container_retire_eof_page_moves(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        post == (KernelK { ctn_mp: post.ctn_mp, sched_mp: post.sched_mp, cpu_set_mp: post.cpu_set_mp, pcid_allc_mp: post.pcid_allc_mp, cpu_offline_mp: post.cpu_offline_mp,
            allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, pg_arr: post.pg_arr, ..pre }),
        forall|i: PageIndex| #![trigger post.pg_arr.spec_index(i)]
            index_valid(NUM_PAGES, i) && (pre.pg_arr.spec_index(i).view().view().owning_container != ctn_ptr || pre.pg_arr.spec_index(i).view().view().is_merged()) ==> post.pg_arr.spec_index(i) == pre.pg_arr.spec_index(i),
        forall|i: PageIndex| #![trigger post.pg_arr.spec_index(i)]
            index_valid(NUM_PAGES, i) && pre.pg_arr.spec_index(i).view().view().owning_container == ctn_ptr && !pre.pg_arr.spec_index(i).view().view().is_merged() ==> {
            let ro = pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view();
            let owner_ro = pre.ctn_mp.spec_index(owner_ptr).view_rodata().view();
            let pre_page = pre.pg_arr.spec_index(i).view().view();
            let post_page = post.pg_arr.spec_index(i).view().view();
            &&& i == page_ptr2page_index(ro.scheduler) || i == page_ptr2page_index(ro.cpu_set) || i == page_ptr2page_index(ro.allocator_ptr_4k) || i == page_ptr2page_index(ro.allocator_ptr_2m)
                || i == page_ptr2page_index(ro.allocator_ptr_1g) || i == page_ptr2page_index(ctn_ptr) || i == page_ptr2page_index(ro.pcid_allocator)
            &&& post_page.owning_container == owner_ptr
            &&& !pre_page.is_io_page && !post_page.is_io_page
            &&& post_page.free_list_node_storage.addr() == pre_page.free_list_node_storage.addr()
            &&& pre_page.state is Allocated4k ==> post_page.state == (PageState::Free4k { allocator_ptr: Ghost(owner_ro.allocator_ptr_4k), state: FreePageAllocatorState::GlobalList })
            &&& pre_page.state is Allocated2m ==> post_page.state == (PageState::Free2m { allocator_ptr: Ghost(owner_ro.allocator_ptr_2m), state: FreePageAllocatorState::GlobalList })
            &&& pre_page.state is Allocated4k || pre_page.state is Allocated2m
        },
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    broadcast use kill_container_retire_eof_owned_page;
}

/// The global pools of `owner_ptr`'s 4K and 2M allocators after the retire hold their old pages and exactly the
/// retired container's 4K object pages and 2M heads; every other allocator is unchanged or retired.
pub(crate) proof fn kill_container_retire_eof_pool_moves(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        ({
            let ro = pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view();
            let owner_ro = pre.ctn_mp.spec_index(owner_ptr).view_rodata().view();
            let (o4, o2) = (owner_ro.allocator_ptr_4k, owner_ro.allocator_ptr_2m);
            &&& pre.ctn_mp.dom().contains(owner_ptr)
            &&& pre.allc_4k_mp.dom().contains(o4) && post.allc_4k_mp.dom().contains(o4) && o4 != ro.allocator_ptr_4k
            &&& pre.allc_2m_mp.dom().contains(o2) && post.allc_2m_mp.dom().contains(o2) && o2 != ro.allocator_ptr_2m
            &&& pre.allc_4k_mp.spec_index(o4).owning_container == owner_ptr && pre.allc_2m_mp.spec_index(o2).owning_container == owner_ptr
            &&& forall|p: PagePtr| #![trigger post.allc_4k_mp.spec_index(o4).global_pool.view().view().contains(p)]
                post.allc_4k_mp.spec_index(o4).global_pool.view().view().contains(p) == (pre.allc_4k_mp.spec_index(o4).global_pool.view().view().contains(p)
                    || page_ptr_valid(p) && pre.pg_arr.spec_index(page_ptr2page_index(p)).view().view().owning_container == ctn_ptr && pre.pg_arr.spec_index(page_ptr2page_index(p)).view().view().state is Allocated4k)
            &&& forall|p: PagePtr| #![trigger post.allc_2m_mp.spec_index(o2).global_pool.view().view().contains(p)]
                post.allc_2m_mp.spec_index(o2).global_pool.view().view().contains(p) == (pre.allc_2m_mp.spec_index(o2).global_pool.view().view().contains(p)
                    || page_ptr_valid(p) && pre.pg_arr.spec_index(page_ptr2page_index(p)).view().view().owning_container == ctn_ptr && pre.pg_arr.spec_index(page_ptr2page_index(p)).view().view().state is Allocated2m)
        }),
{
    reveal(kill_container_retire_eof_transition_framing);
    let ro = pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view();
    let owner_ro = pre.ctn_mp.spec_index(owner_ptr).view_rodata().view();
    let heads = kill_container_retire_heads(ctn_ptr, ro);
    let pool_2m = pre.allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m).global_pool.view().view();
    kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ctn_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, owner_ptr);
    assert(pool_2m.insert(0, page_index2page_ptr(heads[0])).insert(0, page_index2page_ptr(heads[1])) =~= seq![page_index2page_ptr(heads[1]), page_index2page_ptr(heads[0])] + pool_2m);
    broadcast use kill_container_retire_eof_owned_page, vstd::seq_lib::lemma_seq_concat_contains_all_elements, vstd::seq_lib::lemma_seq_contains_after_push;
}

/// Retiring the container keeps every page that an allocator names in the state that names it.
pub(crate) proof fn kill_container_retire_eof_page_objects_allocators(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(allocator_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_4k_pages_wf); };
    assert(allocator_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_2m_pages_wf); };
    assert(allocator_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(allocator_1g_pages_wf); };
}

/// Retiring the container keeps every page that a container names in the state that names it.
pub(crate) proof fn kill_container_retire_eof_page_objects_containers(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures container_pages_wf(post.ctn_mp, post.pg_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_pages_wf); };
}

/// Retiring the container keeps every page that a scheduler, a cpu set, or a PCID allocator names in the state that
/// names it.
pub(crate) proof fn kill_container_retire_eof_page_objects_retired(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { reveal(scheduler_pages_wf); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { reveal(pcid_allocator_pages_wf); };
}

/// Retiring the container keeps every page that a process or a page table names in the state that names it.
pub(crate) proof fn kill_container_retire_eof_page_objects_processes(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        process_pages_wf(post.prc_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
{
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { reveal(process_pages_wf); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { reveal(iommu_table_pages_wf); };
    assert(process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr)) by { reveal(process_object_pages_owner_wf); };
}

/// Retiring the container keeps every page that a thread or an endpoint names, or that a thread stages, in the state
/// that names it.
pub(crate) proof fn kill_container_retire_eof_page_objects_threads(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
{
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_pages_wf); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { reveal(endpoint_pages_wf); };
    assert(thread_staged_pages_wf(post.thrd_mp, post.pg_arr)) by { reveal(thread_staged_4k_pages_wf); reveal(thread_staged_2m_pages_wf); reveal(thread_staged_1g_pages_wf); };
}

/// Retiring the container keeps every 2M and 1G page group whole: its 2M heads turn free with their tails still merged under them.
pub(crate) proof fn kill_container_retire_eof_hugepages(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
{
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(hugepage_2m_wf(post.pg_arr)) by { reveal(hugepage_2m_wf); };
    assert(hugepage_1g_wf(post.pg_arr)) by { reveal(hugepage_1g_wf); };
}

/// Retiring the container, which owns no mapped page, keeps every page-table mapping.
pub(crate) proof fn kill_container_retire_eof_mappings_pagetable(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
{
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_perms_wf); reveal(pagetable_lower_wf); };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_perms_wf); reveal(pagetable_lower_wf); };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); };
}

/// Retiring the container, which owns no mapped page, keeps every page-table and IOMMU mapping's owner relation.
pub(crate) proof fn kill_container_retire_eof_mappings(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(container_process_wf); reveal(iommu_table_perms_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by { reveal(process_emptied_tables_wf); };
}

/// Retiring the container hands every page it owned to `owner_ptr`, keeping the container page sets and each page's
/// object owner consistent.
pub(crate) proof fn kill_container_retire_eof_page_owners(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { reveal(container_owned_pages_wf); };
    assert(page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr)) by {
        reveal(page_array_wf); reveal(page_object_owner_wf); reveal(container_owned_pages_wf); broadcast use kill_container_retire_eof_no_endpoint;
    };
}

/// Retiring the container keeps every retire-ready container empty and its allocators drained: `owner_ptr`, whose
/// allocators gain the target's pages and quota, and every ancestor whose subtree or child list loses the target held it
/// and so is not retire-ready.
proof fn kill_container_retire_eof_kill_retire_wf(pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_container_retire_eof_transition_framing);
    assert(pre.ctn_mp.spec_index(parent_ptr).view().children.view().contains(ctn_ptr)) by { reveal(container_children_parent_wf); };
    reveal(container_uppertree_seq_wf); reveal(container_kill_retire_wf); reveal(container_allocator_wf);
}

/// Retiring the container keeps every allocator well formed, gives `owner_ptr`'s 4K and 2M allocators the freed pages
/// with matching quota, and drops the retired allocators, whose free lists are empty.
pub(crate) proof fn kill_container_retire_eof_allocators(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures
        allocator_perms_wf(post.allc_4k_mp),
        allocator_perms_wf(post.allc_2m_mp),
        allocator_perms_wf(post.allc_1g_mp),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_page_ptrs_wf(post.allc_1g_mp),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_container_retire_eof_transition_framing);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    kill_container_retire_eof_pool_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ctn_ptr);
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_perms_wf(post.allc_2m_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_perms_wf(post.allc_1g_mp)) by { reveal(allocator_perms_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_page_ptrs_wf(post.allc_1g_mp)) by { reveal(allocator_free_page_ptrs_wf); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(container_allocator_wf); };
    kill_container_retire_eof_kill_retire_wf(pre, post, ctn_ptr, parent_ptr, owner_ptr);
}

/// Retiring the container keeps every free 4K page on the free list of its allocator in that allocator's pools:
/// `owner_ptr`'s 4K global pool gains the retired container's 4K object pages, which now name it.
pub(crate) proof fn kill_container_retire_eof_allocator_free_4k_pages(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    kill_container_retire_eof_pool_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ctn_ptr);
    broadcast use kill_container_retire_eof_owned_page;
    assert(allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); };
}

/// Retiring the container keeps every free 2M page on the free list of its allocator in that allocator's pools:
/// `owner_ptr`'s 2M global pool gains the retired container's 2M heads, which now name it.
pub(crate) proof fn kill_container_retire_eof_allocator_free_2m_pages(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    kill_container_retire_eof_pool_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ctn_ptr);
    broadcast use kill_container_retire_eof_owned_page;
    assert(allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_free_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf); reveal(allocator_free_page_ptrs_wf); };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_free_2m_pages_wf); };
}

/// Retiring the container keeps every free 1G page on the free list of its allocator in that allocator's pools.
pub(crate) proof fn kill_container_retire_eof_allocator_free_1g_pages(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(kill_container_retire_eof_transition_framing);
    kill_container_retire_eof_page_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr); kill_container_retire_eof_object_pages(pre, ctn_ptr, parent_ptr, owner_ptr);
    page_ptr_roundtrip(); page_index_roundtrip(); page_index_valid_imply_page_ptr_valid(); page_ptr_valid_imply_page_index_valid();
    kill_container_retire_eof_pool_moves(pre, post, ctn_ptr, parent_ptr, owner_ptr);
    container_allocator_wf_at(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp, ctn_ptr);
    broadcast use kill_container_retire_eof_owned_page;
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by {
        reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf);
        reveal(container_allocator_wf); reveal(allocator_free_page_ptrs_wf);
    };
}

/// Retiring the container keeps every container's allocator quota equal to its free pages minus what its processes
/// and threads hold: `owner_ptr`'s 4K and 2M quota and free pages both grow by the pages returned.
pub(crate) proof fn kill_container_retire_eof_allocator_quotas(
    pre: KernelK, post: KernelK, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, ctn_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, ctn_ptr, parent_ptr, owner_ptr),
    ensures container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    reveal(kill_container_retire_eof_transition_framing);
    lemma_container_allocator_4k_quota_bounded(&pre, owner_ptr); lemma_container_allocator_2m_quota_bounded(&pre, owner_ptr);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by { reveal(container_process_allocator_quota_2m_wf); reveal(container_allocator_wf); };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by { reveal(container_process_allocator_quota_1g_wf); reveal(container_allocator_wf); };
}
} // verus!
