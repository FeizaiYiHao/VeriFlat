use vstd::prelude::*;
use crate::*;

verus! {
/// In a released view, returns the write-held `Allocated4k` pages `pages`, whose kernel objects were removed with their
/// permissions in `page_perms`, through their free-list nodes to the global pool of the 4K allocator `allc_ptr` of
/// `owner_ptr`, which takes them over. The quota is left to the caller.
pub(crate) fn kill_container_retire_pages_4k_to_pool(
    krnl: &mut KernelK, pages: &ArrayVec<PageIndex, 5>, Tracked(page_perms): Tracked<Map<PageIndex, PagePerm4k>>, allc_ptr: RwLockPageAllocatorPtr,
    owner_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perms): Tracked<&Map<PageIndex, LockPerm>>, Tracked(pool_lock_perm): Tracked<&LockPerm>,
)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_array_wf(old(krnl).pg_arr),
        old(krnl).allc_4k_mp.perms_wf(),
        old(krnl).allc_4k_mp.dom().contains(allc_ptr),
        old(krnl).allc_4k_mp.spec_index(allc_ptr).wf(),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), allc_ptr, TypedLockMode::Write),
        pool_lock_perm.state() is WriteLock,
        pool_lock_perm.thread_id() == old(lctx).thread_id(),
        pool_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).global_pool.locking_thread()->Write_lock_id,
        old(krnl).allc_4k_mp.spec_index(allc_ptr).total_free_pages.view() + pages.view().len() < usize::MAX,
        pages.wf(),
        pages.view().no_duplicates(),
        forall|k: int| #![trigger pages.view()[k]] 0 <= k < pages.view().len() ==> {
            let pg_idx = pages.view()[k];
            &&& index_valid(NUM_PAGES, pg_idx)
            &&& old(krnl).pg_arr.spec_index(pg_idx).view().view().state is Allocated4k
            &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), pg_idx, TypedLockMode::Write)
            &&& page_lock_perms.dom().contains(pg_idx)
            &&& page_lock_perms.spec_index(pg_idx).state() is WriteLock
            &&& page_lock_perms.spec_index(pg_idx).thread_id() == old(lctx).thread_id()
            &&& page_lock_perms.spec_index(pg_idx).lock_id() == old(krnl).pg_arr.spec_index(pg_idx).view().locking_thread()->Write_lock_id
            &&& page_perms.dom().contains(pg_idx)
            &&& page_perms.spec_index(pg_idx).is_init()
            &&& page_perms.spec_index(pg_idx).addr() == page_index2page_ptr(pg_idx)
            &&& !old(krnl).allc_4k_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(pg_idx))
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).allc_4k_mp.perms_wf(),
        final(krnl).allc_4k_mp.spec_index(allc_ptr).wf(),
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
            &&& post_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList }, owning_container: owner_ptr,
                free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
        },
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allc_ptr),
        ({
            let pre_allocator = old(krnl).allc_4k_mp.spec_index(allc_ptr);
            let post_allocator = final(krnl).allc_4k_mp.spec_index(allc_ptr);
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
            typed_lock_map_contains_mode(lctx.allocator_global_pool_4k_lock_map(), allc_ptr, TypedLockMode::Write),
            pool_lock_perm.state() is WriteLock,
            pool_lock_perm.thread_id() == lctx.thread_id(),
            pool_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allc_ptr).global_pool.locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.spec_index(allc_ptr).total_free_pages.view() + pages.view().len() < usize::MAX,
            forall|j: int| #![trigger pages.view()[j]] 0 <= j < pages.view().len() ==> {
                let pg_idx = pages.view()[j];
                &&& index_valid(NUM_PAGES, pg_idx)
                &&& old(krnl).pg_arr.spec_index(pg_idx).view().view().state is Allocated4k
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), pg_idx, TypedLockMode::Write)
                &&& page_lock_perms.dom().contains(pg_idx)
                &&& page_lock_perms.spec_index(pg_idx).state() is WriteLock
                &&& page_lock_perms.spec_index(pg_idx).thread_id() == old(lctx).thread_id()
                &&& page_lock_perms.spec_index(pg_idx).lock_id() == old(krnl).pg_arr.spec_index(pg_idx).view().locking_thread()->Write_lock_id
                &&& !old(krnl).allc_4k_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(pg_idx))
            },
            forall|j: int| #![trigger pages.view()[j]] k <= j < pages.view().len() ==> {
                let pg_idx = pages.view()[j];
                &&& page_perms.dom().contains(pg_idx)
                &&& page_perms.spec_index(pg_idx).is_init()
                &&& page_perms.spec_index(pg_idx).addr() == page_index2page_ptr(pg_idx)
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
                &&& cur_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList }, owning_container: owner_ptr,
                    free_list_node_storage: cur_page.view().free_list_node_storage, perm_4k: cur_page.view().perm_4k, ..pre_page.view() })
            },
            krnl.allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            krnl.allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allc_ptr),
            ({
                let pre_allocator = old(krnl).allc_4k_mp.spec_index(allc_ptr);
                let cur_allocator = krnl.allc_4k_mp.spec_index(allc_ptr);
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
        let pg_idx = *pages.get(k);
        let ghost cur_pool = krnl.allc_4k_mp.spec_index(allc_ptr).global_pool.view();
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
        proof {
            page_array_wf_at(krnl.pg_arr, pg_idx);
            assert(!cur_pool.view().contains(page_index2page_ptr(pg_idx))) by {
                page_ptr_roundtrip();
                assert(!pages.view().subrange(0, k as int).contains(pg_idx)) by { reveal(Seq::contains); };
            };
        }
        let tracked page_perm = page_perms.tracked_remove(pg_idx);
        let tracked page_lock_perm = page_lock_perms.tracked_borrow(pg_idx);
        let (node_addr, node_perm) = page_array_retire_kernel_object_4k_to_global(&mut krnl.pg_arr, pg_idx, Tracked(page_perm), allc_ptr, owner_ptr, Tracked(&*lctx),
            Tracked(page_lock_perm));
        proof { lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx)); }
        krnl.allc_4k_mp.push_global_pool_page_typed(allc_ptr, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(pool_lock_perm));
        proof {
            assert(cur_pool.view().insert(0, page_index2page_ptr(pg_idx)) =~= seq![page_index2page_ptr(pg_idx)] + cur_pool.view());
            assert(seq![page_index2page_ptr(pg_idx)][0] == page_index2page_ptr(pg_idx));
            page_index_valid_imply_page_ptr_valid();
            assert(pages.view().subrange(0, k + 1) =~= pages.view().subrange(0, k as int).push(pg_idx));
        }
        k = k + 1;
    }
    proof { assert(pages.view().subrange(0, pages.view().len() as int) =~= pages.view()); }
}

/// In a released view, returns the write-held `Allocated2m` head `head`, whose object was removed with `page_perm`, to the global pool of `owner_ptr`'s 2M allocator `allc_ptr`; the quota is left to the caller.
pub(crate) fn kill_container_retire_head_2m_to_pool(
    krnl: &mut KernelK, head: PageIndex, Tracked(page_perm): Tracked<PagePerm2m>, allc_ptr: RwLockPageAllocatorPtr, owner_ptr: RwLockContainerPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(pool_lock_perm): Tracked<&LockPerm>,
)
    requires
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Release,
        page_array_wf(old(krnl).pg_arr),
        old(krnl).allc_2m_mp.perms_wf(),
        old(krnl).allc_2m_mp.dom().contains(allc_ptr),
        old(krnl).allc_2m_mp.spec_index(allc_ptr).wf(),
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), allc_ptr, TypedLockMode::Write),
        pool_lock_perm.state() is WriteLock,
        pool_lock_perm.thread_id() == old(lctx).thread_id(),
        pool_lock_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(allc_ptr).global_pool.locking_thread()->Write_lock_id,
        old(krnl).allc_2m_mp.spec_index(allc_ptr).total_free_pages.view() < usize::MAX,
        page_index_2m_valid(head),
        old(krnl).pg_arr.spec_index(head).view().view().state is Allocated2m,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), head, TypedLockMode::Write),
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(head).view().locking_thread()->Write_lock_id,
        page_perm.is_init(),
        page_perm.addr() == page_index2page_ptr(head),
        !old(krnl).allc_2m_mp.spec_index(allc_ptr).global_pool.view().view().contains(page_index2page_ptr(head)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        page_array_wf(final(krnl).pg_arr),
        final(krnl).allc_2m_mp.perms_wf(),
        final(krnl).allc_2m_mp.spec_index(allc_ptr).wf(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(head), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(head), mode: TypedLockMode::Write }),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)]
            index_valid(NUM_PAGES, i) && i != head ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
        ({
            let pre_page = old(krnl).pg_arr.spec_index(head).view();
            let post_page = final(krnl).pg_arr.spec_index(head).view();
            &&& post_page.is_init() == pre_page.is_init()
            &&& post_page.view_rodata() == pre_page.view_rodata()
            &&& post_page.view_ghost() == pre_page.view_ghost()
            &&& post_page.locking_thread() == pre_page.locking_thread()
            &&& post_page.being_killed() == pre_page.being_killed()
            &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
            &&& post_page.view() == (Page { state: PageState::Free2m { allocator_ptr: Ghost(allc_ptr), state: FreePageAllocatorState::GlobalList }, owning_container: owner_ptr,
                free_list_node_storage: post_page.view().free_list_node_storage, perm_2m: post_page.view().perm_2m, ..pre_page.view() })
        }),
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, allc_ptr),
        ({
            let pre_allocator = old(krnl).allc_2m_mp.spec_index(allc_ptr);
            let post_allocator = final(krnl).allc_2m_mp.spec_index(allc_ptr);
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
    let (node_addr, node_perm) = page_array_retire_kernel_object_2m_to_global(&mut krnl.pg_arr, head, Tracked(page_perm), allc_ptr, owner_ptr, Tracked(&*lctx),
        Tracked(page_lock_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(head), old_page_lock_id, krnl.pg_arr.lock_id_by_index(head)); }
    krnl.allc_2m_mp.push_global_pool_page_typed(allc_ptr, node_addr, node_perm, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
        Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(pool_lock_perm));
}
} // verus!
