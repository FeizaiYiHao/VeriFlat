use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use vstd::set_lib::*;
use crate::*;

verus! {
pub open spec fn page_2m_tail_indices(head: PageIndex) -> Set<PageIndex> {
    Set::range((head + 1) as usize, (head + 512) as usize)
}

pub open spec fn page_2m_ptr_prefix(head: PageIndex, count: nat) -> Set<PagePtr>
    decreases count,
{
    if count == 0 {
        Set::empty()
    } else {
        page_2m_ptr_prefix(head, (count - 1) as nat)
            .insert(spec_page_index2page_ptr((head as int + count as int - 1) as usize))
    }
}

pub open spec fn page_2m_all_ptrs(head: PageIndex) -> Set<PagePtr> {
    page_2m_ptr_prefix(head, 512)
}

proof fn page_2m_ptr_prefix_contains_head(head: PageIndex, count: nat)
    requires
        page_index_2m_valid(head),
        0 < count <= 512,
    ensures
        page_2m_ptr_prefix(head, count).contains(page_index2page_ptr(head)),
    decreases count,
{
    if count > 1 {
        page_2m_ptr_prefix_contains_head(head, (count - 1) as nat);
    }
}

pub proof fn page_2m_all_ptrs_contains_head(head: PageIndex)
    requires
        page_index_2m_valid(head),
    ensures
        page_2m_all_ptrs(head).contains(page_index2page_ptr(head)),
{
    page_2m_ptr_prefix_contains_head(head, 512);
}

proof fn page_2m_ptr_prefix_contains_index(head: PageIndex, count: nat, index: PageIndex)
    requires
        page_index_2m_valid(head),
        0 < count <= 512,
        head <= index < head + count,
    ensures
        page_2m_ptr_prefix(head, count).contains(
            page_index2page_ptr(index),
        ),
    decreases count,
{
    let last = (head as int + count as int - 1) as usize;
    if index == last {
    } else {
        page_2m_ptr_prefix_contains_index(head, (count - 1) as nat, index);
    }
}

pub proof fn page_2m_all_ptrs_contains_index(head: PageIndex, index: PageIndex)
    requires
        page_index_2m_valid(head),
        head <= index < head + 512,
    ensures
        page_2m_all_ptrs(head).contains(page_index2page_ptr(index)),
{
    page_2m_ptr_prefix_contains_index(head, 512, index);
}

#[verifier::spinoff_prover]
pub(super) proof fn page_ptr_indices_disjoint_from_2m_tail(
    page_ptrs: Seq<PagePtr>,
    page_indices: Set<PageIndex>,
    head: PageIndex,
)
    requires
        page_index_2m_valid(head),
        page_indices == page_ptrs.map_values(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
        ).to_set(),
        forall|page_ptr: PagePtr|
            #![trigger page_ptrs.to_set().contains(page_ptr)]
            page_ptrs.to_set().contains(page_ptr)
                ==> page_ptr_valid(page_ptr),
        page_ptrs.to_set().disjoint(page_2m_all_ptrs(head)),
    ensures
        page_indices.disjoint(page_2m_tail_indices(head)),
{
    let page_ptr_set = page_ptrs.to_set();
    let mapped_by = page_ptr_set.map_by(
        |page_ptr: PagePtr| page_ptr2page_index(page_ptr), |index: PageIndex| spec_page_index2page_ptr(index),
    );
    assert(page_indices =~= mapped_by) by {
        broadcast use Seq::lemma_to_set_map_commutes;
        page_ptr_roundtrip();
        assert_sets_equal!(page_indices == mapped_by, index => {
            page_ptr_set.lemma_map_contains(|page_ptr: PagePtr| page_ptr2page_index(page_ptr), index);
            page_ptr_set.lemma_map_by_contains(
                |page_ptr: PagePtr| page_ptr2page_index(page_ptr), |index: PageIndex| spec_page_index2page_ptr(index), index,
            );
        });
    };
    assert(page_indices.intersect(page_2m_tail_indices(head))
        =~= Set::<PageIndex>::empty()) by {
        assert_sets_equal!(
            page_indices.intersect(page_2m_tail_indices(head))
                == Set::<PageIndex>::empty(),
            index => {
                if page_indices.contains(index)
                    && page_2m_tail_indices(head).contains(index)
                {
                    page_2m_all_ptrs_contains_index(head, index);
                    page_index_roundtrip();
                    page_ptr_set.lemma_map_by_contains(
                        |page_ptr: PagePtr| page_ptr2page_index(page_ptr), |index: PageIndex| spec_page_index2page_ptr(index), index,
                    );
                }
            }
        );
    };
    lemma_set_disjoint_iff_empty_intersection(page_indices, page_2m_tail_indices(head));
}

pub broadcast proof fn page_2m_ptr_prefix_member_bounds(head: PageIndex, count: nat, page_ptr: PagePtr)
    requires
        page_index_2m_valid(head),
        count <= 512,
        #[trigger] page_2m_ptr_prefix(head, count).contains(page_ptr),
    ensures
        page_ptr_valid(page_ptr),
        head <= page_ptr2page_index(page_ptr) < head + count,
        page_ptr2page_index(page_ptr) == head
            || spec_page_index_merge_2m_valid(head, page_ptr2page_index(page_ptr)),
        page_ptr2page_index(page_ptr) == head
            || page_2m_tail_indices(head).contains(page_ptr2page_index(page_ptr)),
    decreases count,
{
    assert(count > 0) by {
        if count == 0 {
        }
    };
    let last = (head as int + count as int - 1) as usize;
    if page_ptr == spec_page_index2page_ptr(last) {
        page_index_valid_imply_page_ptr_valid();
        page_index_roundtrip();
    } else {
        page_2m_ptr_prefix_member_bounds(head, (count - 1) as nat, page_ptr);
    }
}

pub broadcast proof fn page_ptr_sequence_index_in_mapped_set(
    page_ptrs: Seq<PagePtr>,
    i: int,
)
    requires
        0 <= i < page_ptrs.len(),
    ensures
        #[trigger] page_ptr_valid(page_ptrs.spec_index(i)) ==> {
            &&& index_valid(NUM_PAGES, page_ptr2page_index(page_ptrs.spec_index(i)))
            &&& page_ptrs.map_values(
                |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
            ).to_set().contains(
                page_ptr2page_index(page_ptrs.spec_index(i)),
            )
        },
{
    page_ptr_valid_imply_page_index_valid();
    let mapped = page_ptrs.map_values(
        |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
    );
    mapped.lemma_index_contains(i);
    mapped.to_set_ensures();
}

pub broadcast proof fn page_ptr_sequence_index_in_equal_set(
    page_ptrs: Seq<PagePtr>,
    i: int,
)
    requires
        0 <= i < page_ptrs.len(),
    ensures
        page_ptrs.to_set().contains(
            #[trigger] page_ptrs.spec_index(i),
        ),
{
    page_ptrs.lemma_index_contains(i);
    page_ptrs.to_set_ensures();
}

proof fn ordered_2m_heads_have_disjoint_all_ptrs(left: PageIndex, right: PageIndex)
    requires
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left + 512 <= right,
    ensures
        page_2m_all_ptrs(left).disjoint(page_2m_all_ptrs(right)),
{
    broadcast use page_2m_ptr_prefix_member_bounds;
}

pub proof fn distinct_2m_heads_have_disjoint_all_ptrs(left: PageIndex, right: PageIndex)
    requires
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left != right,
    ensures
        page_2m_all_ptrs(left).disjoint(page_2m_all_ptrs(right)),
{
    if left + 512usize <= right {
        ordered_2m_heads_have_disjoint_all_ptrs(left, right);
    } else {
        ordered_2m_heads_have_disjoint_all_ptrs(right, left);
    }
}

pub proof fn owned_2m_all_ptrs_belong_to_container(
    krnl: &KernelK, head: PageIndex, container_ptr: RwLockContainerPtr,
)
    requires
        krnl.inv(),
        page_index_2m_valid(head),
        krnl.pg_arr.spec_index(head).view().view().state is Owned2m,
        krnl.pg_arr.spec_index(head)
            .view().view().owning_container == container_ptr,
    ensures
        page_2m_all_ptrs(head).subset_of(
            krnl.ctn_mp.spec_index(container_ptr)
                .view().owned_pages.view(),
        ),
{
    assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_page_owner_wf); };
    assert(page_2m_all_ptrs(head).subset_of(krnl.ctn_mp.spec_index(container_ptr).view().owned_pages.view())) by {
        reveal(hugepage_2m_wf);
        reveal(container_page_owner_wf);
        broadcast use page_2m_ptr_prefix_member_bounds;
        page_ptr_roundtrip();
    };
}

pub proof fn owned_4k_page_not_in_2m_tail(
    krnl: &KernelK, page_ptr: PagePtr, head: PageIndex,
)
    requires
        krnl.inv(),
        page_ptr_valid(page_ptr),
        page_index_2m_valid(head),
        krnl.pg_arr.spec_index(head).view().view().state is Owned2m,
        krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().state is Owned4k,
    ensures
        !page_2m_tail_indices(head).contains(
            page_ptr2page_index(page_ptr),
        ),
{
    if page_2m_tail_indices(head).contains(
        page_ptr2page_index(page_ptr),
    ) {
        assert(
            krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().state is Merged2m
        ) by {
            reveal(hugepage_2m_wf);
        };
    }
}

pub proof fn owned_4k_page_not_in_2m_region(
    krnl: &KernelK, page_ptr: PagePtr, head: PageIndex,
)
    requires
        krnl.inv(),
        page_ptr_valid(page_ptr),
        page_index_2m_valid(head),
        krnl.pg_arr.spec_index(head).view().view().state is Owned2m,
        krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().state is Owned4k,
    ensures
        !page_2m_all_ptrs(head).contains(page_ptr),
{
    if page_2m_all_ptrs(head).contains(page_ptr) {
        page_2m_ptr_prefix_member_bounds(head, 512, page_ptr);
        if page_ptr2page_index(page_ptr) != head {
            owned_4k_page_not_in_2m_tail(krnl, page_ptr, head);
        }
    }
}

pub proof fn page_ptr_2m_valid_imply_page_index_2m_valid(page_ptr: PagePtr)
    requires
        page_ptr_2m_valid(page_ptr),
    ensures
        page_index_2m_valid(page_ptr2page_index(page_ptr)),
{
}

pub(super) proof fn distinct_2m_heads_have_disjoint_tails(
    left: PageIndex, right: PageIndex,
)
    requires
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left != right,
    ensures
        page_2m_tail_indices(left).disjoint(
            page_2m_tail_indices(right),
        ),
{
}

pub(super) open spec fn page_2m_tail_prefix_indices(head: PageIndex, count: usize) -> Set<PageIndex> {
    Set::range((head + 1) as usize, (head + 1 + count) as usize)
}

pub open spec fn owned_2m_tail_lock_perms_wf(
    perms: Map<PageIndex, LockPerm>, pages: PageLockedArray, lctx: &LocalContext, head: PageIndex,
) -> bool {
    &&& perms.dom() == page_2m_tail_indices(head)
    &&& forall|index: PageIndex|
        #![trigger perms.dom().contains(index)]
        perms.dom().contains(index) ==> {
            &&& index_valid(NUM_PAGES, index)
            &&& pages.spec_index(index).view().is_init()
            &&& pages.spec_index(index).view().view().state is Merged2m
            &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
            &&& perms.spec_index(index).state() is WriteLock
            &&& perms.spec_index(index).thread_id() == lctx.thread_id()
            &&& perms.spec_index(index).lock_id()
                == pages.spec_index(index).view().locking_thread()->Write_lock_id
    }
}

pub fn wlock_owned_2m_page_tails(
    krnl: &mut KernelK,
    head: PageIndex,
    Tracked(lctx): Tracked<&mut LocalContext>,
) -> (ret: Tracked<Map<PageIndex, LockPerm>>)
    requires
        old(krnl).inv(),
        page_index_2m_valid(head),
        old(krnl).pg_arr.spec_index(head).view().view().state is Owned2m,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().disjoint(
            page_2m_tail_indices(head),
        ),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < MERGED_PAGE_LOCK_MAJOR || (old(krnl).pg_arr.lock_id_by_index(held_page).major == MERGED_PAGE_LOCK_MAJOR && held_page < head + 1),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        forall|held_page: PageIndex| #![trigger final(lctx).page_lock_map().dom().contains(held_page)] final(lctx).page_lock_map().dom().contains(held_page) ==> final(krnl).pg_arr.lock_id_by_index(held_page).major < MERGED_PAGE_LOCK_MAJOR || (final(krnl).pg_arr.lock_id_by_index(held_page).major == MERGED_PAGE_LOCK_MAJOR && held_page < head + 512),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index)
                && !page_2m_tail_indices(head).contains(index)
            ==> final(krnl).pg_arr.spec_index(index)
                == old(krnl).pg_arr.spec_index(index),
        final(lctx).page_lock_map().remove_keys(
            page_2m_tail_indices(head),
        ) == old(lctx).page_lock_map(),
        final(lctx).page_lock_map().dom()
            == old(lctx).page_lock_map().dom().union(page_2m_tail_indices(head)),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            ..*old(krnl)
        }),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view()]
            index_valid(NUM_PAGES, index) ==>
                final(krnl).pg_arr.spec_index(index).view().view()
                    == old(krnl).pg_arr.spec_index(index).view().view(),
        owned_2m_tail_lock_perms_wf(ret.view(), final(krnl).pg_arr, final(lctx), head),
{
    let tracked mut perms: Map<PageIndex, LockPerm> = Map::tracked_empty();
    let mut count: usize = 0;
    proof {
        assert(page_2m_tail_prefix_indices(head, 0).is_empty()) by {
            assert_sets_equal!(
                page_2m_tail_prefix_indices(head, 0)
                    == Set::<PageIndex>::empty(),
                index => {}
            );
        };
    }
    while count < 511
        invariant
            krnl.inv(),
            page_index_2m_valid(head),
            old(krnl).pg_arr.spec_index(head).view().view().state is Owned2m,
            head + 512usize <= NUM_PAGES,
            0 <= count <= 511,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lctx.page_lock_map().remove_keys(
                page_2m_tail_prefix_indices(head, count),
            ) == old(lctx).page_lock_map(),
            lctx.page_lock_map().dom()
                == old(lctx).page_lock_map().dom()
                    .union(page_2m_tail_prefix_indices(head, count)),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map() == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            krnl.pt_mp == old(krnl).pt_mp,
            krnl.it_mp == old(krnl).it_mp,
            krnl.irt == old(krnl).irt,
            krnl.cpu_arr == old(krnl).cpu_arr,
            krnl.pcid_needflush == old(krnl).pcid_needflush,
            krnl.cpu_published == old(krnl).cpu_published,
            krnl.cpu_tlb == old(krnl).cpu_tlb,
            krnl.iommu_tlb == old(krnl).iommu_tlb,
            krnl.rt_ctn == old(krnl).rt_ctn,
            krnl.ctn_mp == old(krnl).ctn_mp,
            krnl.sched_mp == old(krnl).sched_mp,
            krnl.pcid_allc_mp == old(krnl).pcid_allc_mp,
            krnl.cpu_set_mp == old(krnl).cpu_set_mp,
            krnl.prc_mp == old(krnl).prc_mp,
            krnl.thr_mp == old(krnl).thr_mp,
            krnl.ep_mp == old(krnl).ep_mp,
            krnl.allc_4k_mp == old(krnl).allc_4k_mp,
            krnl.allc_2m_mp == old(krnl).allc_2m_mp,
            krnl.allc_1g_mp == old(krnl).allc_1g_mp,
            krnl.dflt_pt == old(krnl).dflt_pt,
            forall|index: PageIndex|
                #![trigger krnl.pg_arr.spec_index(index).view().view()]
                index_valid(NUM_PAGES, index) ==>
                    krnl.pg_arr.spec_index(index).view().view()
                        == old(krnl).pg_arr.spec_index(index).view().view(),
            forall|index: PageIndex|
                #![trigger krnl.pg_arr.spec_index(index)]
                #![trigger old(krnl).pg_arr.spec_index(index)]
                index_valid(NUM_PAGES, index)
                    && !page_2m_tail_prefix_indices(head, count)
                        .contains(index)
                ==> krnl.pg_arr.spec_index(index)
                    == old(krnl).pg_arr.spec_index(index),
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
                    &&& perms.spec_index(index).lock_id()
                        == krnl.pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
                },
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger lctx.page_lock_map().dom().contains(held_page)] lctx.page_lock_map().dom().contains(held_page) ==> krnl.pg_arr.lock_id_by_index(held_page).major < MERGED_PAGE_LOCK_MAJOR || (krnl.pg_arr.lock_id_by_index(held_page).major == MERGED_PAGE_LOCK_MAJOR && held_page < head + 1 + count),
        decreases 511 - count,
    {
        let index = head + 1usize + count;
        proof {
            assert(
                krnl.pg_arr.spec_index(index).view().view().state is Merged2m
            ) by { reveal(hugepage_2m_wf); };
        }
        let Tracked(perm) =
            krnl.wlock_page(index, Tracked(&mut *lctx));
        proof {
            perms.tracked_insert(index, perm);
            assert(
                page_2m_tail_prefix_indices(head, (count + 1) as usize)
                    == page_2m_tail_prefix_indices(head, count).insert(index)
            ) by {
                assert_sets_equal!(
                    page_2m_tail_prefix_indices(head, (count + 1) as usize)
                        == page_2m_tail_prefix_indices(head, count)
                            .insert(index),
                    candidate => {
                    }
                );
            };
            assert(
                lctx.page_lock_map().remove_keys(
                    page_2m_tail_prefix_indices(head, (count + 1) as usize),
                ) == old(lctx).page_lock_map()
            ) by {
                assert_maps_equal!(
                    lctx.page_lock_map().remove_keys(
                        page_2m_tail_prefix_indices(head, (count + 1) as usize),
                    ),
                    old(lctx).page_lock_map(),
                    key => {}
                );
            };
        }
        count = count + 1usize;
    }
    proof {
        assert(
            page_2m_tail_prefix_indices(head, 511)
                == page_2m_tail_indices(head)
        ) by {
            assert_sets_equal!(
                page_2m_tail_prefix_indices(head, 511)
                    == page_2m_tail_indices(head),
                index => {
                }
            );
        };
        assert(held_pages_unchanged(
            old(krnl).pg_arr,
            krnl.pg_arr,
            old(lctx),
        )) by {
            reveal(LockedArray::typed_lock_map_aligned);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by {
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
            broadcast use kernel_pagetable_nonlock_fields_unchanged_for_equal, kernel_iommu_table_nonlock_fields_unchanged_for_equal;
            kernel_no_change_to_nonlock_fields_imply_kernel_u_nonlock_eq(old(krnl), krnl);
        };
    }
    Tracked(perms)
}

pub(super) fn set_owned_2m_page_tail_pair_container(
    pages: &mut PageLockedArray,
    first_head: PageIndex,
    second_head: PageIndex,
    owning_container: RwLockContainerPtr,
    Ghost(reference_pages): Ghost<PageLockedArray>,
    Ghost(preserved_page_ptr_seq): Ghost<Seq<PagePtr>>,
    Ghost(preserved_page_ptrs): Ghost<Set<PagePtr>>,
    Ghost(preserved_indices): Ghost<Set<PageIndex>>,
    Ghost(protected_indices): Ghost<Set<PageIndex>>,
    Tracked(lctx): Tracked<&LocalContext>,
    Tracked(first_perms): Tracked<&Map<PageIndex, LockPerm>>,
    Tracked(second_perms): Tracked<&Map<PageIndex, LockPerm>>,
)
    requires
        old(pages).inv(),
        page_array_wf(*old(pages)),
        page_index_2m_valid(first_head),
        page_index_2m_valid(second_head),
        first_head != second_head,
        reference_pages == *old(pages),
        staged_4k_page_chain(reference_pages, preserved_page_ptr_seq),
        preserved_page_ptrs == preserved_page_ptr_seq.to_set(),
        preserved_indices == preserved_page_ptr_seq.map_values(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
        ).to_set(),
        preserved_indices == preserved_page_ptrs.map(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
        ),
        forall|page_ptr: PagePtr|
            #![trigger preserved_page_ptrs.contains(page_ptr)]
            preserved_page_ptrs.contains(page_ptr)
                ==> page_ptr_valid(page_ptr),
        preserved_indices.disjoint(page_2m_tail_indices(first_head)),
        preserved_indices.disjoint(page_2m_tail_indices(second_head)),
        page_2m_tail_indices(first_head).disjoint(protected_indices),
        page_2m_tail_indices(second_head).disjoint(protected_indices),
        old(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        owned_2m_tail_lock_perms_wf(*first_perms, *old(pages), lctx, first_head),
        owned_2m_tail_lock_perms_wf(*second_perms, *old(pages), lctx, second_head),
    ensures
        final(pages).inv(),
        page_array_wf(*final(pages)),
        final(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        owned_2m_tail_lock_perms_wf(*first_perms, *final(pages), lctx, first_head),
        owned_2m_tail_lock_perms_wf(*second_perms, *final(pages), lctx, second_head),
        staged_4k_page_chain(*final(pages), preserved_page_ptr_seq),
        forall|index: PageIndex|
            #![trigger first_perms.dom().contains(index)]
            first_perms.dom().contains(index)
            ==> final(pages).spec_index(index).view().view()
                    .owning_container == owning_container,
        forall|index: PageIndex|
            #![trigger second_perms.dom().contains(index)]
            second_perms.dom().contains(index)
            ==> final(pages).spec_index(index).view().view()
                    .owning_container == owning_container,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().mappings()]
            index_valid(NUM_PAGES, index)
            ==> final(pages).spec_index(index).view().view().mappings()
                == reference_pages.spec_index(index)
                    .view().view().mappings(),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view().state]
            index_valid(NUM_PAGES, index)
            ==> final(pages).spec_index(index).view().view().state
                == reference_pages.spec_index(index).view().view().state,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)
                .view().view().owning_container]
            index_valid(NUM_PAGES, index)
                && !page_2m_tail_indices(first_head).contains(index)
                && !page_2m_tail_indices(second_head).contains(index)
            ==> final(pages).spec_index(index).view().view()
                    .owning_container
                == reference_pages.spec_index(index).view().view()
                    .owning_container,
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index)]
            #![trigger reference_pages.spec_index(index)]
            index_valid(NUM_PAGES, index)
                && !page_2m_tail_indices(first_head).contains(index)
                && !page_2m_tail_indices(second_head).contains(index)
            ==> final(pages).spec_index(index)
                == reference_pages.spec_index(index),
        forall|index: PageIndex|
            #![trigger preserved_indices.contains(index)]
            preserved_indices.contains(index)
                && index_valid(NUM_PAGES, index)
            ==> final(pages).spec_index(index)
                == reference_pages.spec_index(index),
        forall|index: PageIndex|
            #![trigger protected_indices.contains(index)]
            protected_indices.contains(index)
                && index_valid(NUM_PAGES, index)
            ==> final(pages).spec_index(index)
                == reference_pages.spec_index(index),
        forall|page_ptr: PagePtr|
            #![trigger preserved_page_ptrs.contains(page_ptr)]
            preserved_page_ptrs.contains(page_ptr)
            ==> final(pages).spec_index(page_ptr2page_index(page_ptr))
                == reference_pages.spec_index(
                    page_ptr2page_index(page_ptr),
                ),
{
    proof {
        broadcast use page_ptr_sequence_index_in_equal_set;
        preserved_page_ptr_seq.to_set_ensures();
        distinct_2m_heads_have_disjoint_tails(first_head, second_head);
    }
    let mut count: usize = 0;
    while count < 511
        invariant
            pages.inv(),
            page_array_wf(*pages),
            page_index_2m_valid(first_head),
            page_index_2m_valid(second_head),
            first_head != second_head,
            preserved_indices.disjoint(
                page_2m_tail_indices(first_head),
            ),
            preserved_indices.disjoint(
                page_2m_tail_indices(second_head),
            ),
            page_2m_tail_indices(first_head).disjoint(
                protected_indices,
            ),
            page_2m_tail_indices(second_head).disjoint(
                protected_indices,
            ),
            preserved_indices == preserved_page_ptrs.map(
                |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
            ),
            reference_pages == *old(pages),
            preserved_page_ptrs == preserved_page_ptr_seq.to_set(),
            preserved_indices == preserved_page_ptr_seq.map_values(
                |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
            ).to_set(),
            forall|page_ptr: PagePtr|
                #![trigger preserved_page_ptrs.contains(page_ptr)]
                preserved_page_ptrs.contains(page_ptr)
                    ==> page_ptr_valid(page_ptr),
            0 <= count <= 511,
            pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
            first_perms.dom() == page_2m_tail_indices(first_head),
            forall|index: PageIndex|
                #![trigger first_perms.dom().contains(index)]
                first_perms.dom().contains(index) ==> {
                    &&& index_valid(NUM_PAGES, index)
                    &&& pages.spec_index(index).view().is_init()
                    &&& pages.spec_index(index).view().view().state
                        is Merged2m
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
                    &&& first_perms.spec_index(index).state() is WriteLock
                    &&& first_perms.spec_index(index).thread_id()
                        == lctx.thread_id()
                    &&& first_perms.spec_index(index).lock_id()
                        == pages.spec_index(index).view()
                            .locking_thread()->Write_lock_id
                },
            second_perms.dom() == page_2m_tail_indices(second_head),
            forall|index: PageIndex|
                #![trigger second_perms.dom().contains(index)]
                second_perms.dom().contains(index) ==> {
                    &&& index_valid(NUM_PAGES, index)
                    &&& pages.spec_index(index).view().is_init()
                    &&& pages.spec_index(index).view().view().state
                        is Merged2m
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
                    &&& second_perms.spec_index(index).state() is WriteLock
                    &&& second_perms.spec_index(index).thread_id()
                        == lctx.thread_id()
                    &&& second_perms.spec_index(index).lock_id()
                        == pages.spec_index(index).view()
                            .locking_thread()->Write_lock_id
                },
            forall|index: PageIndex|
                #![trigger pages.spec_index(index).view().view()]
                index_valid(NUM_PAGES, index) ==> {
                    if page_2m_tail_prefix_indices(first_head, count)
                        .contains(index)
                        || page_2m_tail_prefix_indices(second_head, count)
                            .contains(index)
                    {
                        &&& pages.spec_index(index).view().view()
                            .owning_container == owning_container
                        &&& pages.spec_index(index).view().view().state
                            == old(pages).spec_index(index).view().view().state
                        &&& pages.spec_index(index).view().view().mappings()
                            == old(pages).spec_index(index).view().view()
                                .mappings()
                        &&& pages.spec_index(index).view().locking_thread()
                            == old(pages).spec_index(index).view()
                                .locking_thread()
                    } else {
                        pages.spec_index(index)
                            == old(pages).spec_index(index)
                    }
                },
            forall|index: PageIndex|
                #![trigger pages.spec_index(index)]
                index_valid(NUM_PAGES, index)
                    && !page_2m_tail_prefix_indices(first_head, count)
                        .contains(index)
                    && !page_2m_tail_prefix_indices(second_head, count)
                        .contains(index)
                ==> pages.spec_index(index)
                    == old(pages).spec_index(index),
            forall|index: PageIndex|
                #![trigger preserved_indices.contains(index)]
                preserved_indices.contains(index)
                    && index_valid(NUM_PAGES, index)
                ==> pages.spec_index(index)
                    == reference_pages.spec_index(index),
            forall|index: PageIndex|
                #![trigger protected_indices.contains(index)]
                protected_indices.contains(index)
                    && index_valid(NUM_PAGES, index)
                ==> pages.spec_index(index)
                    == reference_pages.spec_index(index),
            forall|i: int|
                #![trigger pages.spec_index(page_ptr2page_index(
                    preserved_page_ptr_seq.spec_index(i),
                )).view().view().free_list]
                0 <= i < preserved_page_ptr_seq.len() ==> {
                    &&& page_ptr_valid(
                        preserved_page_ptr_seq.spec_index(i),
                    )
                    &&& index_valid(
                        NUM_PAGES,
                        page_ptr2page_index(
                            preserved_page_ptr_seq.spec_index(i),
                        ),
                    )
                    &&& pages.spec_index(page_ptr2page_index(
                        preserved_page_ptr_seq.spec_index(i),
                    )) == reference_pages.spec_index(
                        page_ptr2page_index(
                            preserved_page_ptr_seq.spec_index(i),
                        ),
                    )
                },
        decreases 511 - count,
    {
        let first_index = first_head + 1usize + count;
        let second_index = second_head + 1usize + count;
        proof {
            assert(page_2m_tail_indices(first_head).contains(first_index)) by { vstd::set_lib::range_set_properties((first_head + 1) as usize, (first_head + 512) as usize); };
            assert(page_2m_tail_indices(second_head).contains(second_index) && !page_2m_tail_indices(second_head).contains(first_index)) by { vstd::set_lib::range_set_properties((second_head + 1) as usize, (second_head + 512) as usize); };
        }
        let first_page = pages.borrow_mut_typed(
            first_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(first_perms.tracked_borrow(first_index)),
        );
        first_page.owning_container = owning_container;
        proof {
            assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
        }
        let second_page = pages.borrow_mut_typed(
            second_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(second_perms.tracked_borrow(second_index)),
        );
        second_page.owning_container = owning_container;
        proof {
            assert(page_array_wf(*pages)) by { reveal(page_array_wf); };
            broadcast use page_ptr_sequence_index_in_equal_set;
            broadcast use page_ptr_sequence_index_in_mapped_set;
            preserved_page_ptr_seq.to_set_ensures();
            assert(
                page_2m_tail_prefix_indices(first_head, (count + 1) as usize) == page_2m_tail_prefix_indices(first_head, count)
                    .insert(first_index)
            ) by {
                assert_sets_equal!(
                    page_2m_tail_prefix_indices(first_head, (count + 1) as usize) == page_2m_tail_prefix_indices(first_head, count)
                        .insert(first_index),
                    candidate => {
                    }
                );
            };
            assert(
                page_2m_tail_prefix_indices(second_head, (count + 1) as usize) == page_2m_tail_prefix_indices(second_head, count)
                    .insert(second_index)
            ) by {
                assert_sets_equal!(
                    page_2m_tail_prefix_indices(second_head, (count + 1) as usize) == page_2m_tail_prefix_indices(second_head, count)
                        .insert(second_index),
                    candidate => {
                    }
                );
            };
        }
        count = count + 1usize;
    }
    proof {
        assert(
            page_2m_tail_prefix_indices(first_head, 511)
                == page_2m_tail_indices(first_head)
        ) by {
            assert_sets_equal!(
                page_2m_tail_prefix_indices(first_head, 511)
                    == page_2m_tail_indices(first_head),
                index => {
                }
            );
        };
        assert(
            page_2m_tail_prefix_indices(second_head, 511)
                == page_2m_tail_indices(second_head)
        ) by {
            assert_sets_equal!(
                page_2m_tail_prefix_indices(second_head, 511)
                    == page_2m_tail_indices(second_head),
                index => {
                }
            );
        };
    }
}

pub fn wunlock_owned_2m_page_tails(
    krnl: &mut KernelK,
    head: PageIndex,
    Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(perms): Tracked<Map<PageIndex, LockPerm>>,
)
    requires
        old(krnl).inv(),
        page_index_2m_valid(head),
        owned_2m_tail_lock_perms_wf(perms, old(krnl).pg_arr, old(lctx), head),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        kernel_k_to_nonlock_kernel_u(*final(krnl))
            == kernel_k_to_nonlock_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map()
            == old(lctx).page_lock_map()
                .remove_keys(page_2m_tail_indices(head)),
        final(lctx).page_lock_map().dom()
            == old(lctx).page_lock_map().dom()
                .difference(page_2m_tail_indices(head)),
        held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), page_2m_tail_indices(head)),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index)
                && !page_2m_tail_indices(head).contains(index)
            ==> final(krnl).pg_arr.spec_index(index)
                == old(krnl).pg_arr.spec_index(index),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map()
            == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map()
            == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map()
            == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps()
            == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps()
            == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps()
            == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            ..*old(krnl)
        }),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view()]
            index_valid(NUM_PAGES, index) ==>
                final(krnl).pg_arr.spec_index(index).view().view()
                    == old(krnl).pg_arr.spec_index(index).view().view(),
        forall|index: PageIndex|
            #![trigger page_2m_tail_indices(head).contains(index)]
            page_2m_tail_indices(head).contains(index) ==>
                !final(lctx).page_lock_map().dom().contains(index),
{
    let tracked mut perms = perms;
    let mut count: usize = 0;
    while count < 511
        invariant
            krnl.inv(),
            page_index_2m_valid(head),
            0 <= count <= 511,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire
                || lctx.kernel_view_locking_state() is Release,
            count > 0
                ==> lctx.kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(krnl, &*lctx),
            lctx.page_lock_map()
                == old(lctx).page_lock_map().remove_keys(
                    page_2m_tail_prefix_indices(head, count),
                ),
            lctx.page_lock_map().dom()
                == old(lctx).page_lock_map().dom()
                    .difference(page_2m_tail_prefix_indices(head, count)),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
            lctx.pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            lctx.process_lock_map() == old(lctx).process_lock_map(),
            lctx.thread_lock_map() == old(lctx).thread_lock_map(),
            lctx.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
            lctx.scheduler_lock_map() == old(lctx).scheduler_lock_map(),
            lctx.pcid_allocator_lock_map()
                == old(lctx).pcid_allocator_lock_map(),
            lctx.cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
            lctx.pagetable_lock_map()
                == old(lctx).pagetable_lock_map(),
            lctx.iommu_table_lock_map()
                == old(lctx).iommu_table_lock_map(),
            lctx.allocator_4k_lock_maps()
                == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps()
                == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps()
                == old(lctx).allocator_1g_lock_maps(),
            krnl.pt_mp == old(krnl).pt_mp,
            krnl.it_mp == old(krnl).it_mp,
            krnl.irt == old(krnl).irt,
            krnl.cpu_arr == old(krnl).cpu_arr,
            krnl.pcid_needflush == old(krnl).pcid_needflush,
            krnl.cpu_published == old(krnl).cpu_published,
            krnl.cpu_tlb == old(krnl).cpu_tlb,
            krnl.iommu_tlb == old(krnl).iommu_tlb,
            krnl.rt_ctn == old(krnl).rt_ctn,
            krnl.ctn_mp == old(krnl).ctn_mp,
            krnl.sched_mp == old(krnl).sched_mp,
            krnl.pcid_allc_mp == old(krnl).pcid_allc_mp,
            krnl.cpu_set_mp == old(krnl).cpu_set_mp,
            krnl.prc_mp == old(krnl).prc_mp,
            krnl.thr_mp == old(krnl).thr_mp,
            krnl.ep_mp == old(krnl).ep_mp,
            krnl.allc_4k_mp == old(krnl).allc_4k_mp,
            krnl.allc_2m_mp == old(krnl).allc_2m_mp,
            krnl.allc_1g_mp == old(krnl).allc_1g_mp,
            krnl.dflt_pt == old(krnl).dflt_pt,
            forall|index: PageIndex|
                #![trigger krnl.pg_arr.spec_index(index).view().view()]
                index_valid(NUM_PAGES, index) ==>
                    krnl.pg_arr.spec_index(index).view().view()
                        == old(krnl).pg_arr.spec_index(index).view().view(),
            forall|index: PageIndex|
                #![trigger krnl.pg_arr.spec_index(index)]
                #![trigger old(krnl).pg_arr.spec_index(index)]
                index_valid(NUM_PAGES, index)
                    && !page_2m_tail_prefix_indices(head, count)
                        .contains(index)
                ==> krnl.pg_arr.spec_index(index)
                    == old(krnl).pg_arr.spec_index(index),
            perms.dom()
                == page_2m_tail_indices(head)
                    .difference(page_2m_tail_prefix_indices(head, count)),
            forall|index: PageIndex|
                #![trigger perms.dom().contains(index)]
                perms.dom().contains(index) ==> {
                    &&& index_valid(NUM_PAGES, index)
                    &&& krnl.pg_arr.spec_index(index).view().view().state
                        is Merged2m
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), index, TypedLockMode::Write)
                    &&& perms.spec_index(index).state() is WriteLock
                    &&& perms.spec_index(index).thread_id()
                        == lctx.thread_id()
                    &&& perms.spec_index(index).lock_id()
                        == krnl.pg_arr.spec_index(index).view()
                            .locking_thread()->Write_lock_id
                },
            forall|index: PageIndex|
                #![trigger page_2m_tail_prefix_indices(head, count)
                    .contains(index)]
                page_2m_tail_prefix_indices(head, count).contains(index) ==>
                    !lctx.page_lock_map().dom().contains(index),
        decreases 511 - count,
    {
        let index = head + 1usize + count;
        proof {
            assert(perms.dom().contains(index)) by { vstd::set_lib::range_set_properties((head + 1) as usize, (head + 512) as usize); vstd::set_lib::range_set_properties((head + 1) as usize, (head + 1 + count) as usize); };
        }
        let tracked perm = perms.tracked_remove(index);
        krnl.wunlock_page(index, Tracked(&mut *lctx), Tracked(perm));
        proof {
            assert(
                page_2m_tail_prefix_indices(head, (count + 1) as usize)
                    == page_2m_tail_prefix_indices(head, count)
                        .insert(index)
            ) by {
                assert_sets_equal!(
                    page_2m_tail_prefix_indices(head, (count + 1) as usize)
                        == page_2m_tail_prefix_indices(head, count)
                            .insert(index),
                    candidate => {
                    }
                );
            };
            assert(
                lctx.page_lock_map()
                    == old(lctx).page_lock_map().remove_keys(
                        page_2m_tail_prefix_indices(head, (count + 1) as usize),
                    )
            ) by {
                assert_maps_equal!(
                    lctx.page_lock_map(),
                    old(lctx).page_lock_map().remove_keys(
                            page_2m_tail_prefix_indices(head, (count + 1) as usize),
                        ),
                    key => {}
                );
            };
        }
        count = count + 1usize;
    }
    proof {
        assert(
            page_2m_tail_prefix_indices(head, 511)
                == page_2m_tail_indices(head)
        ) by {
            assert_sets_equal!(
                page_2m_tail_prefix_indices(head, 511)
                    == page_2m_tail_indices(head),
                index => {
                }
            );
        };
        held_pages_unchanged_except_for_changed_set(old(krnl).pg_arr, krnl.pg_arr, old(lctx), page_2m_tail_indices(head));
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by {
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
            broadcast use kernel_pagetable_nonlock_fields_unchanged_for_equal, kernel_iommu_table_nonlock_fields_unchanged_for_equal;
            kernel_no_change_to_nonlock_fields_imply_kernel_u_nonlock_eq(old(krnl), krnl);
        };
    }
}
}
