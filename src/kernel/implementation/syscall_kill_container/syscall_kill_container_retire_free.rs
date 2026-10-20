use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;

verus! {
/// In a released view, returns the write-held `Allocated4k` pages `pages`, whose kernel objects were removed with their
/// permissions in `page_perms`, through their free-list nodes to the global pool of the 4K allocator `allocator_ptr` of
/// `owner_ptr`, which takes them over. The quota is left to the caller.
pub(crate) fn kill_container_retire_pages_4k_to_pool(
    krnl: &mut KernelK, pages: &ArrayVec<PageIndex, 5>, Tracked(page_perms): Tracked<Map<PageIndex, PagePerm4k>>, allocator_ptr: RwLockPageAllocatorPtr,
    owner_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pool_lock_perm): Tracked<&LockPerm>,
)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_array_wf(old(krnl).pg_arr),
        old(krnl).allc_4k_mp.perms_wf(),
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).wf(),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        pool_lock_perm.state() is WriteLock,
        pool_lock_perm.thread_id() == old(lctx).thread_id(),
        pool_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool.locking_thread()->Write_lock_id,
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() + pages.view().len() < usize::MAX,
        pages.wf(),
        pages.view().no_duplicates(),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
            let page_index = pages.view()[k];
            &&& index_valid(NUM_PAGES, page_index)
            &&& old(krnl).pg_arr.spec_index(page_index).view().view().state is Allocated4k
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write)
            &&& page_lock_perms.dom().contains(page_index)
            &&& page_lock_perms.spec_index(page_index).state() is WriteLock
            &&& page_lock_perms.spec_index(page_index).thread_id() == old(lctx).thread_id()
            &&& page_lock_perms.spec_index(page_index).lock_id() == old(krnl).pg_arr.spec_index(page_index).view().locking_thread()->Write_lock_id
            &&& page_perms.dom().contains(page_index)
            &&& page_perms.spec_index(page_index).is_init()
            &&& page_perms.spec_index(page_index).addr() == page_index2page_ptr(page_index)
            &&& !old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool.view().view().contains(page_index2page_ptr(page_index))
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).wf(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom(),
        forall|i: PageIndex| #![trigger final(lctx).page_lock_map().index(i)] old(lctx).page_lock_map().dom().contains(i) ==> final(lctx).page_lock_map().index(i)
            == if pages.view().contains(i) { TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(i), mode: TypedLockMode::Write } } else { old(lctx).page_lock_map().index(i) },
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !pages.view().contains(i) ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
            let pre_page = old(krnl).pg_arr.spec_index(pages.view()[k]).view();
            let post_page = final(krnl).pg_arr.spec_index(pages.view()[k]).view();
            &&& post_page.is_init() == pre_page.is_init()
            &&& post_page.view_rodata() == pre_page.view_rodata()
            &&& post_page.view_ghost() == pre_page.view_ghost()
            &&& post_page.locking_thread() == pre_page.locking_thread()
            &&& post_page.being_killed() == pre_page.being_killed()
            &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
            &&& post_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList }, owning_container: owner_ptr,
                free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
        },
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
        ({
            let pre_allocator = old(krnl).allc_4k_mp.spec_index(allocator_ptr);
            let post_allocator = final(krnl).allc_4k_mp.spec_index(allocator_ptr);
            let pre_pool = pre_allocator.global_pool.view();
            let post_pool = post_allocator.global_pool.view();
            &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + pages.view().len()
            &&& post_pool.view().len() == pre_pool.view().len() + pages.view().len()
            &&& forall|p: PagePtr| #![trigger post_pool.view().contains(p)] post_pool.view().contains(p) == (pre_pool.view().contains(p) || pages.view().contains(page_ptr2page_index(p)) && page_ptr_valid(p))
            &&& forall|a: usize| #![trigger pre_pool.map().dom().contains(a)] pre_pool.map().dom().contains(a) ==> post_pool.map().dom().contains(a) && post_pool.map().spec_index(a) == pre_pool.map().spec_index(a)
            &&& forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
                let node = old(krnl).pg_arr.spec_index(pages.view()[k]).view().view().free_list_node_storage.addr();
                &&& !pre_pool.map().dom().contains(node)
                &&& post_pool.map().dom().contains(node)
                &&& post_pool.map().spec_index(node) == page_index2page_ptr(pages.view()[k])
            }
            &&& post_allocator.global_pool.locking_thread() == pre_allocator.global_pool.locking_thread()
            &&& post_allocator.global_pool.being_killed() == pre_allocator.global_pool.being_killed()
            &&& post_allocator.cpu_caches == pre_allocator.cpu_caches
            &&& post_allocator.owning_container == pre_allocator.owning_container
            &&& post_allocator.quota == pre_allocator.quota
        }),
{
    let tracked mut page_perms = page_perms;
    let mut k: usize = 0;
    while k < pages.len()
        invariant
            pages.wf(),
            pages.view().no_duplicates(),
            0 <= k <= pages.view().len(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(krnl, &*lctx),
            page_array_wf(krnl.pg_arr),
            krnl.allc_4k_mp.perms_wf(),
            typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
            pool_lock_perm.state() is WriteLock,
            pool_lock_perm.thread_id() == lctx.thread_id(),
            pool_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool.locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view() + pages.view().len() < usize::MAX,
            forall|j: int| #![trigger pages.view()[j]] 0 <= j < pages.view().len() ==> {
                let page_index = pages.view()[j];
                &&& index_valid(NUM_PAGES, page_index)
                &&& old(krnl).pg_arr.spec_index(page_index).view().view().state is Allocated4k
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_index, TypedLockMode::Write)
                &&& page_lock_perms.dom().contains(page_index)
                &&& page_lock_perms.spec_index(page_index).state() is WriteLock
                &&& page_lock_perms.spec_index(page_index).thread_id() == old(lctx).thread_id()
                &&& page_lock_perms.spec_index(page_index).lock_id() == old(krnl).pg_arr.spec_index(page_index).view().locking_thread()->Write_lock_id
                &&& !old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool.view().view().contains(page_index2page_ptr(page_index))
            },
            forall|j: int| #![trigger pages.view()[j]] k <= j < pages.view().len() ==> {
                let page_index = pages.view()[j];
                &&& page_perms.dom().contains(page_index)
                &&& page_perms.spec_index(page_index).is_init()
                &&& page_perms.spec_index(page_index).addr() == page_index2page_ptr(page_index)
            },
            lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom(),
            forall|i: PageIndex| #![trigger lctx.page_lock_map().index(i)] old(lctx).page_lock_map().dom().contains(i) ==> lctx.page_lock_map().index(i)
                == if pages.view().subrange(0, k as int).contains(i) { TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(i), mode: TypedLockMode::Write } } else { old(lctx).page_lock_map().index(i) },
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            *krnl == (KernelK { pg_arr: krnl.pg_arr, allc_4k_mp: krnl.allc_4k_mp, ..*old(krnl) }),
            forall|i: PageIndex| #![trigger krnl.pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !pages.view().subrange(0, k as int).contains(i) ==> krnl.pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
            forall|j: int| #![trigger pages.view()[j]] 0 <= j < k ==> {
                let pre_page = old(krnl).pg_arr.spec_index(pages.view()[j]).view();
                let cur_page = krnl.pg_arr.spec_index(pages.view()[j]).view();
                &&& cur_page.is_init() == pre_page.is_init()
                &&& cur_page.view_rodata() == pre_page.view_rodata()
                &&& cur_page.view_ghost() == pre_page.view_ghost()
                &&& cur_page.locking_thread() == pre_page.locking_thread()
                &&& cur_page.being_killed() == pre_page.being_killed()
                &&& cur_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
                &&& cur_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList }, owning_container: owner_ptr,
                    free_list_node_storage: cur_page.view().free_list_node_storage, perm_4k: cur_page.view().perm_4k, ..pre_page.view() })
            },
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            krnl.allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
            ({
                let pre_allocator = old(krnl).allc_4k_mp.spec_index(allocator_ptr);
                let cur_allocator = krnl.allc_4k_mp.spec_index(allocator_ptr);
                let pre_pool = pre_allocator.global_pool.view();
                let cur_pool = cur_allocator.global_pool.view();
                &&& cur_allocator.wf()
                &&& cur_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + k
                &&& cur_pool.view().len() == pre_pool.view().len() + k
                &&& forall|p: PagePtr| #![trigger cur_pool.view().contains(p)] cur_pool.view().contains(p) == (pre_pool.view().contains(p) || pages.view().subrange(0, k as int).contains(page_ptr2page_index(p)) && page_ptr_valid(p))
                &&& forall|a: usize| #![trigger pre_pool.map().dom().contains(a)] pre_pool.map().dom().contains(a) ==> cur_pool.map().dom().contains(a) && cur_pool.map().spec_index(a) == pre_pool.map().spec_index(a)
                &&& forall|j: int| #![trigger pages.view()[j]] 0 <= j < k ==> {
                    let node = old(krnl).pg_arr.spec_index(pages.view()[j]).view().view().free_list_node_storage.addr();
                    &&& !pre_pool.map().dom().contains(node)
                    &&& cur_pool.map().dom().contains(node)
                    &&& cur_pool.map().spec_index(node) == page_index2page_ptr(pages.view()[j])
                }
                &&& cur_allocator.global_pool.locking_thread() == pre_allocator.global_pool.locking_thread()
                &&& cur_allocator.global_pool.being_killed() == pre_allocator.global_pool.being_killed()
                &&& cur_allocator.cpu_caches == pre_allocator.cpu_caches
                &&& cur_allocator.owning_container == pre_allocator.owning_container
                &&& cur_allocator.quota == pre_allocator.quota
            }),
        decreases pages.view().len() - k,
    {
        broadcast use vstd::seq_lib::lemma_seq_concat_contains_all_elements, vstd::seq_lib::lemma_seq_contains_after_push;
        let page_index = *pages.get(k);
        let ghost cur_pool = krnl.allc_4k_mp.spec_index(allocator_ptr).global_pool.view();
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        proof {
            page_array_wf_at(krnl.pg_arr, page_index);
            assert(!cur_pool.view().contains(page_index2page_ptr(page_index))) by {
                page_ptr_roundtrip();
                assert(!pages.view().subrange(0, k as int).contains(page_index)) by { reveal(Seq::contains); };
            };
        }
        let tracked page_perm = page_perms.tracked_remove(page_index);
        let tracked page_lock_perm = page_lock_perms.tracked_borrow(page_index);
        let (node_addr, node_perm) = page_array_retire_kernel_object_4k_to_global(&mut krnl.pg_arr, page_index, Tracked(page_perm), allocator_ptr, owner_ptr, Tracked(&*lctx),
            Tracked(page_lock_perm));
        proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }
        krnl.allc_4k_mp.push_global_pool_page_typed(allocator_ptr, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(pool_lock_perm));
        proof {
            assert(cur_pool.view().insert(0, page_index2page_ptr(page_index)) =~= seq![page_index2page_ptr(page_index)] + cur_pool.view());
            assert(seq![page_index2page_ptr(page_index)][0] == page_index2page_ptr(page_index));
            page_index_valid_imply_page_ptr_valid();
            assert(pages.view().subrange(0, k + 1) =~= pages.view().subrange(0, k as int).push(page_index));
        }
        k = k + 1;
    }
    proof { assert(pages.view().subrange(0, pages.view().len() as int) =~= pages.view()); }
}

/// In a released view, returns the write-held `Allocated2m` head page `head`, whose kernel object was removed with its
/// permission `page_perm`, through its free-list node to the global pool of the 2M allocator `allocator_ptr` of
/// `owner_ptr`, which takes it over with its merged tails, write-held through `tail_perms`. The quota is left to the
/// caller.
pub(crate) fn kill_container_retire_head_2m_to_pool(
    krnl: &mut KernelK, head: PageIndex, Tracked(page_perm): Tracked<PagePerm2m>, allocator_ptr: RwLockPageAllocatorPtr, owner_ptr: RwLockContainerPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(tail_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(pool_lock_perm): Tracked<&LockPerm>,
)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_array_wf(old(krnl).pg_arr),
        old(krnl).allc_2m_mp.perms_wf(),
        old(krnl).allc_2m_mp.dom().contains(allocator_ptr),
        old(krnl).allc_2m_mp.spec_index(allocator_ptr).wf(),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), allocator_ptr, TypedLockMode::Write),
        pool_lock_perm.state() is WriteLock,
        pool_lock_perm.thread_id() == old(lctx).thread_id(),
        pool_lock_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(allocator_ptr).global_pool.locking_thread()->Write_lock_id,
        old(krnl).allc_2m_mp.spec_index(allocator_ptr).total_free_pages.view() < usize::MAX,
        page_index_2m_valid(head),
        old(krnl).pg_arr.spec_index(head).view().view().state is Allocated2m,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), head, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(head).view().locking_thread()->Write_lock_id,
        page_perm.is_init(),
        page_perm.addr() == page_index2page_ptr(head),
        !old(krnl).allc_2m_mp.spec_index(allocator_ptr).global_pool.view().view().contains(page_index2page_ptr(head)),
        owned_2m_tail_lock_perms_wf(*tail_perms, old(krnl).pg_arr, old(lctx), head),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).allc_2m_mp.perms_wf(),
        final(krnl).allc_2m_mp.spec_index(allocator_ptr).wf(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(head), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(head), mode: TypedLockMode::Write }),
        owned_2m_tail_lock_perms_wf(*tail_perms, final(krnl).pg_arr, final(lctx), head),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)]
            index_valid(NUM_PAGES, i) && i != head && !page_2m_tail_indices(head).contains(i) ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
        ({
            let pre_page = old(krnl).pg_arr.spec_index(head).view();
            let post_page = final(krnl).pg_arr.spec_index(head).view();
            &&& post_page.is_init() == pre_page.is_init()
            &&& post_page.view_rodata() == pre_page.view_rodata()
            &&& post_page.view_ghost() == pre_page.view_ghost()
            &&& post_page.locking_thread() == pre_page.locking_thread()
            &&& post_page.being_killed() == pre_page.being_killed()
            &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
            &&& post_page.view() == (Page { state: PageState::Free2m { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::GlobalList }, owning_container: owner_ptr,
                free_list_node_storage: post_page.view().free_list_node_storage, perm_2m: post_page.view().perm_2m, ..pre_page.view() })
        }),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)] page_2m_tail_indices(head).contains(i) ==> {
            &&& final(krnl).pg_arr.spec_index(i).view().view() == (Page { owning_container: owner_ptr, ..old(krnl).pg_arr.spec_index(i).view().view() })
            &&& final(krnl).pg_arr.spec_index(i).view().is_init() == old(krnl).pg_arr.spec_index(i).view().is_init()
            &&& final(krnl).pg_arr.spec_index(i).view().view_rodata() == old(krnl).pg_arr.spec_index(i).view().view_rodata()
            &&& final(krnl).pg_arr.spec_index(i).view().view_ghost() == old(krnl).pg_arr.spec_index(i).view().view_ghost()
            &&& final(krnl).pg_arr.spec_index(i).view().locking_thread() == old(krnl).pg_arr.spec_index(i).view().locking_thread()
            &&& final(krnl).pg_arr.spec_index(i).view().being_killed() == old(krnl).pg_arr.spec_index(i).view().being_killed()
        },
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, allocator_ptr),
        ({
            let pre_allocator = old(krnl).allc_2m_mp.spec_index(allocator_ptr);
            let post_allocator = final(krnl).allc_2m_mp.spec_index(allocator_ptr);
            let node = old(krnl).pg_arr.spec_index(head).view().view().free_list_node_storage.addr();
            &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + 1
            &&& post_allocator.global_pool.view().view() == pre_allocator.global_pool.view().view().insert(0, page_index2page_ptr(head))
            &&& post_allocator.global_pool.view().map() == pre_allocator.global_pool.view().map().insert(node, page_index2page_ptr(head))
            &&& !pre_allocator.global_pool.view().map().dom().contains(node)
            &&& post_allocator.global_pool.locking_thread() == pre_allocator.global_pool.locking_thread()
            &&& post_allocator.global_pool.being_killed() == pre_allocator.global_pool.being_killed()
            &&& post_allocator.cpu_caches == pre_allocator.cpu_caches
            &&& post_allocator.owning_container == pre_allocator.owning_container
            &&& post_allocator.quota == pre_allocator.quota
        }),
{
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(head);
    proof { page_array_wf_at(krnl.pg_arr, head); page_ptr_roundtrip(); }
    let (node_addr, node_perm) = page_array_retire_kernel_object_2m_to_global(&mut krnl.pg_arr, head, Tracked(page_perm), allocator_ptr, owner_ptr, Tracked(&*lctx),
        Tracked(page_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(head), old_page_lock_id, krnl.pg_arr.lock_id_by_index(head)); }
    krnl.allc_2m_mp.push_global_pool_page_typed(allocator_ptr, node_addr, node_perm, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
        Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(pool_lock_perm));
    kill_container_retire_set_tails_owner(&mut krnl.pg_arr, head, owner_ptr, Tracked(&*lctx), Tracked(tail_perms));
}

/// Gives the 511 merged tails of the 2M page at `head`, write-held through `perms`, to `owner`; every other page stays.
fn kill_container_retire_set_tails_owner(
    pages: &mut PageLockedArray, head: PageIndex, owner: RwLockContainerPtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(perms): Tracked<&Map<PageIndex, LockPerm>>,
)
    requires
        page_array_wf(*old(pages)),
        page_index_2m_valid(head),
        old(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        owned_2m_tail_lock_perms_wf(*perms, *old(pages), lctx, head),
    ensures
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        owned_2m_tail_lock_perms_wf(*perms, *final(pages), lctx, head),
        forall|i: PageIndex| #![trigger final(pages).spec_index(i)]
            index_valid(NUM_PAGES, i) && !page_2m_tail_indices(head).contains(i) ==> final(pages).spec_index(i) == old(pages).spec_index(i),
        forall|i: PageIndex| #![trigger final(pages).spec_index(i)]
            page_2m_tail_indices(head).contains(i) ==> {
                &&& final(pages).spec_index(i).view().view() == (Page { owning_container: owner, ..old(pages).spec_index(i).view().view() })
                &&& final(pages).spec_index(i).view().is_init() == old(pages).spec_index(i).view().is_init()
                &&& final(pages).spec_index(i).view().view_rodata() == old(pages).spec_index(i).view().view_rodata()
                &&& final(pages).spec_index(i).view().view_ghost() == old(pages).spec_index(i).view().view_ghost()
                &&& final(pages).spec_index(i).view().locking_thread() == old(pages).spec_index(i).view().locking_thread()
                &&& final(pages).spec_index(i).view().being_killed() == old(pages).spec_index(i).view().being_killed()
            },
{
    proof {
        page_array_wf_map(*pages);
        assert(Set::range((head + 1) as usize, (head + 1) as usize).is_empty()) by { assert_sets_equal!(Set::range((head + 1) as usize, (head + 1) as usize) == Set::<PageIndex>::empty(), index => {}); };
    }
    let mut count: usize = 0;
    while count < 511
        invariant
            page_array_wf(*old(pages)),
            page_index_2m_valid(head),
            0 <= count <= 511,
            pages.inv(),
            pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
            owned_2m_tail_lock_perms_wf(*perms, *old(pages), lctx, head),
            forall|i: PageIndex| #![trigger pages.spec_index(i)]
                index_valid(NUM_PAGES, i) && !Set::range((head + 1) as usize, (head + 1 + count) as usize).contains(i) ==> pages.spec_index(i) == old(pages).spec_index(i),
            forall|i: PageIndex| #![trigger pages.spec_index(i)]
                Set::range((head + 1) as usize, (head + 1 + count) as usize).contains(i) ==> {
                    &&& pages.spec_index(i).view().view() == (Page { owning_container: owner, ..old(pages).spec_index(i).view().view() })
                    &&& pages.spec_index(i).view().is_init() == old(pages).spec_index(i).view().is_init()
                    &&& pages.spec_index(i).view().view_rodata() == old(pages).spec_index(i).view().view_rodata()
                    &&& pages.spec_index(i).view().view_ghost() == old(pages).spec_index(i).view().view_ghost()
                    &&& pages.spec_index(i).view().locking_thread() == old(pages).spec_index(i).view().locking_thread()
                    &&& pages.spec_index(i).view().being_killed() == old(pages).spec_index(i).view().being_killed()
                    &&& pages.spec_index(i).lock_id() == old(pages).spec_index(i).lock_id()
                    &&& pages.spec_index(i).view().inv()
                },
        decreases 511 - count,
    {
        let index = head + 1usize + count;
        proof {
            assert(page_2m_tail_indices(head).contains(index) && !Set::range((head + 1) as usize, (head + 1 + count) as usize).contains(index)) by {
                vstd::set_lib::range_set_properties((head + 1) as usize, (head + 512) as usize); vstd::set_lib::range_set_properties((head + 1) as usize, (head + 1 + count) as usize);
            };
        }
        let page = pages.borrow_mut_typed(index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(perms.tracked_borrow(index)));
        page.owning_container = owner;
        proof {
            assert(pages.spec_index(index).view().inv()) by { page_array_wf_at(*old(pages), index); reveal(Page::mappings_va_valid); };
            assert(Set::range((head + 1) as usize, (head + 2 + count) as usize) == Set::range((head + 1) as usize, (head + 1 + count) as usize).insert(index)) by {
                assert_sets_equal!(Set::range((head + 1) as usize, (head + 2 + count) as usize) == Set::range((head + 1) as usize, (head + 1 + count) as usize).insert(index), candidate => {});
            };
        }
        count = count + 1usize;
    }
    proof { assert(page_array_wf(*pages)) by { reveal(page_array_wf); }; }
}
} // verus!
