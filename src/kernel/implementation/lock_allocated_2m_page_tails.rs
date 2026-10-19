use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use crate::*;
use crate::kernel::implementation::lock_owned_2m_page_tails::*;

verus! {
/// Write-hold the 511 merged tails of the allocated 2M kernel-object page at `head`, in index order, for a killer that may
/// hold the offline request cells of marked containers it write-holds; `wunlock_owned_2m_page_tails` releases them.
pub fn wlock_allocated_2m_page_tails(krnl: &mut KernelK, head: PageIndex, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: Tracked<Map<PageIndex, LockPerm>>)
    requires
        old(krnl).inv(),
        page_index_2m_valid(head),
        old(krnl).pg_arr.spec_index(head).view().view().state is Allocated2m,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().disjoint(page_2m_tail_indices(head)),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_flag: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger old(lctx).cpu_offline_flag_lock_map().dom().contains(held_flag)]
            old(lctx).cpu_offline_flag_lock_map().dom().contains(held_flag) ==> {
                let flag_container = old(krnl).cpu_offline_mp.spec_index(held_flag.0).owning_container.view();
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), flag_container, TypedLockMode::Write)
                &&& old(krnl).ctn_mp.spec_index(flag_container).being_killed()
            },
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page)
            ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < MERGED_PAGE_LOCK_MAJOR || (old(krnl).pg_arr.lock_id_by_index(held_page).major == MERGED_PAGE_LOCK_MAJOR && held_page < head + 1),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        forall|held_page: PageIndex| #![trigger final(lctx).page_lock_map().dom().contains(held_page)] final(lctx).page_lock_map().dom().contains(held_page)
            ==> final(krnl).pg_arr.lock_id_by_index(held_page).major < MERGED_PAGE_LOCK_MAJOR || (final(krnl).pg_arr.lock_id_by_index(held_page).major == MERGED_PAGE_LOCK_MAJOR && held_page < head + 512),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !page_2m_tail_indices(head).contains(index) ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        final(lctx).page_lock_map().remove_keys(page_2m_tail_indices(head)) == old(lctx).page_lock_map(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_2m_tail_indices(head)),
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
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view() == old(krnl).pg_arr.spec_index(index).view().view(),
        owned_2m_tail_lock_perms_wf(ret.view(), final(krnl).pg_arr, final(lctx), head),
{
    let tracked mut perms: Map<PageIndex, LockPerm> = Map::tracked_empty();
    let mut count: usize = 0;
    proof {
        assert(page_2m_tail_prefix_indices(head, 0).is_empty()) by { assert_sets_equal!(page_2m_tail_prefix_indices(head, 0) == Set::<PageIndex>::empty(), index => {}); };
    }
    while count < 511
        invariant
            krnl.inv(),
            page_index_2m_valid(head),
            old(krnl).pg_arr.spec_index(head).view().view().state is Allocated2m,
            head + 512usize <= NUM_PAGES,
            0 <= count <= 511,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lctx.page_lock_map().remove_keys(page_2m_tail_prefix_indices(head, count)) == old(lctx).page_lock_map(),
            lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_2m_tail_prefix_indices(head, count)),
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
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            *krnl == (KernelK { pg_arr: krnl.pg_arr, ..*old(krnl) }),
            forall|index: PageIndex|
                #![trigger krnl.pg_arr.spec_index(index).view().view()]
                index_valid(NUM_PAGES, index) ==> krnl.pg_arr.spec_index(index).view().view() == old(krnl).pg_arr.spec_index(index).view().view(),
            forall|index: PageIndex|
                #![trigger krnl.pg_arr.spec_index(index)]
                #![trigger old(krnl).pg_arr.spec_index(index)]
                index_valid(NUM_PAGES, index) && !page_2m_tail_prefix_indices(head, count).contains(index) ==> krnl.pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
            perms.dom() == page_2m_tail_prefix_indices(head, count),
            forall|index: PageIndex|
                #![trigger perms.dom().contains(index)]
                perms.dom().contains(index) ==> {
                    &&& index_valid(NUM_PAGES, index)
                    &&& krnl.pg_arr.spec_index(index).view().is_init()
                    &&& krnl.pg_arr.spec_index(index).view().view().state is Merged2m
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
                    &&& perms.spec_index(index).state() is WriteLock
                    &&& perms.spec_index(index).thread_id() == lctx.thread_id()
                    &&& perms.spec_index(index).lock_id() == krnl.pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
                },
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            forall|held_flag: (RwLockCpuOfflineFlagsPtr, CpuId)| #![trigger lctx.cpu_offline_flag_lock_map().dom().contains(held_flag)]
                lctx.cpu_offline_flag_lock_map().dom().contains(held_flag) ==> {
                    let flag_container = krnl.cpu_offline_mp.spec_index(held_flag.0).owning_container.view();
                    &&& typed_lock_map_contains_mode(lctx.container_lock_map(), flag_container, TypedLockMode::Write)
                    &&& krnl.ctn_mp.spec_index(flag_container).being_killed()
                },
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger lctx.page_lock_map().dom().contains(held_page)] lctx.page_lock_map().dom().contains(held_page)
                ==> krnl.pg_arr.lock_id_by_index(held_page).major < MERGED_PAGE_LOCK_MAJOR || (krnl.pg_arr.lock_id_by_index(held_page).major == MERGED_PAGE_LOCK_MAJOR && held_page < head + 1 + count),
        decreases 511 - count,
    {
        let index = head + 1usize + count;
        proof { assert(krnl.pg_arr.spec_index(index).view().view().state is Merged2m) by { hugepage_2m_wf_tail_at(krnl.pg_arr, head, index); }; }
        let Tracked(perm) = krnl.wlock_page(index, Tracked(&mut *lctx));
        proof {
            perms.tracked_insert(index, perm);
            assert(page_2m_tail_prefix_indices(head, (count + 1) as usize) == page_2m_tail_prefix_indices(head, count).insert(index)) by {
                assert_sets_equal!(page_2m_tail_prefix_indices(head, (count + 1) as usize) == page_2m_tail_prefix_indices(head, count).insert(index), candidate => {});
            };
            assert(lctx.page_lock_map().remove_keys(page_2m_tail_prefix_indices(head, (count + 1) as usize)) == old(lctx).page_lock_map()) by {
                assert_maps_equal!(lctx.page_lock_map().remove_keys(page_2m_tail_prefix_indices(head, (count + 1) as usize)), old(lctx).page_lock_map(), key => {});
            };
        }
        count = count + 1usize;
    }
    proof {
        assert(page_2m_tail_prefix_indices(head, 511) == page_2m_tail_indices(head)) by { assert_sets_equal!(page_2m_tail_prefix_indices(head, 511) == page_2m_tail_indices(head), index => {}); };
        assert(held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx))) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by {
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
            broadcast use kernel_pagetable_nonlock_fields_unchanged_for_equal;
            kernel_no_change_to_nonlock_fields_imply_kernel_u_nonlock_eq(old(krnl), krnl);
        };
    }
    Tracked(perms)
}
}
