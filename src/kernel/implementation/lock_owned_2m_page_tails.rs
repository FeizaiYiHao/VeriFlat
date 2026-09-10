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
    assert(page_2m_ptr_prefix(head, count).contains(page_index2page_ptr(head))) by {
        reveal(page_2m_ptr_prefix);
    };
}

pub proof fn page_2m_all_ptrs_contains_head(head: PageIndex)
    requires
        page_index_2m_valid(head),
    ensures
        page_2m_all_ptrs(head).contains(page_index2page_ptr(head)),
{
    page_2m_ptr_prefix_contains_head(head, 512);
    reveal(page_2m_all_ptrs);
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
    assert(head + 512usize <= NUM_PAGES) by (nonlinear_arith)
        requires
            head % 512 == 0,
            head < NUM_PAGES,
            NUM_PAGES == 512 * 4096;
    assert(index_valid(NUM_PAGES, index)) by (nonlinear_arith)
        requires
            index < head + count,
            count <= 512,
            head + 512 <= NUM_PAGES;
    if index == last {
        assert(page_2m_ptr_prefix(head, count).contains(page_index2page_ptr(index))) by {
            reveal(page_2m_ptr_prefix);
        };
    } else {
        assert(index < head + count - 1) by (nonlinear_arith)
            requires
                index < head + count,
                index != head + count - 1;
        page_2m_ptr_prefix_contains_index(head, (count - 1) as nat, index);
        assert(page_2m_ptr_prefix(head, count).contains(page_index2page_ptr(index))) by {
            reveal(page_2m_ptr_prefix);
        };
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
    reveal(page_2m_all_ptrs);
}

broadcast proof fn page_2m_ptr_prefix_member_bounds(head: PageIndex, count: nat, page_ptr: PagePtr)
    requires
        page_index_2m_valid(head),
        count <= 512,
        #[trigger] page_2m_ptr_prefix(head, count).contains(page_ptr),
    ensures
        page_ptr_valid(page_ptr),
        head <= page_ptr2page_index(page_ptr) < head + count,
        page_ptr2page_index(page_ptr) == head
            || spec_page_index_merge_2m_valid(head, page_ptr2page_index(page_ptr)),
    decreases count,
{
    assert(count > 0) by {
        if count == 0 {
            assert(!page_2m_ptr_prefix(head, count).contains(page_ptr)) by {
                reveal(page_2m_ptr_prefix);
            };
        }
    };
    let last = (head as int + count as int - 1) as usize;
    assert(index_valid(NUM_PAGES, last)) by (nonlinear_arith)
        requires
            head < NUM_PAGES,
            count <= 512,
            count > 0,
            head + 512 <= NUM_PAGES,
            last == head + count - 1;
    if page_ptr == spec_page_index2page_ptr(last) {
        page_index_valid_imply_page_ptr_valid();
        page_index_roundtrip();
    } else {
        assert(page_2m_ptr_prefix(head, (count - 1) as nat).contains(page_ptr)) by {
            reveal(page_2m_ptr_prefix);
        };
        page_2m_ptr_prefix_member_bounds(head, (count - 1) as nat, page_ptr);
    }
    assert(page_ptr2page_index(page_ptr) == head
        || spec_page_index_merge_2m_valid(head, page_ptr2page_index(page_ptr))) by (nonlinear_arith)
        requires
            head <= page_ptr2page_index(page_ptr) < head + count,
            count <= 512;
}

proof fn ordered_2m_heads_have_disjoint_all_ptrs(left: PageIndex, right: PageIndex)
    requires
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left + 512 <= right,
    ensures
        page_2m_all_ptrs(left).disjoint(page_2m_all_ptrs(right)),
{
    assert(page_2m_all_ptrs(left).disjoint(page_2m_all_ptrs(right))) by {
        reveal(Set::disjoint);
        reveal(page_2m_all_ptrs);
        broadcast use page_2m_ptr_prefix_member_bounds;
    };
}

pub proof fn distinct_2m_heads_have_disjoint_all_ptrs(left: PageIndex, right: PageIndex)
    requires
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left != right,
    ensures
        page_2m_all_ptrs(left).disjoint(page_2m_all_ptrs(right)),
{
    let left_quotient = left / 512usize;
    let right_quotient = right / 512usize;
    assert(left == left_quotient * 512usize) by (nonlinear_arith)
        requires
            left % 512usize == 0,
            left_quotient == left / 512usize;
    assert(right == right_quotient * 512usize) by (nonlinear_arith)
        requires
            right % 512usize == 0,
            right_quotient == right / 512usize;
    assert(left + 512usize <= right || right + 512usize <= left) by (nonlinear_arith)
        requires
            left == left_quotient * 512usize,
            right == right_quotient * 512usize,
            left != right;
    if left + 512usize <= right {
        ordered_2m_heads_have_disjoint_all_ptrs(left, right);
    } else {
        assert(right + 512usize <= left) by {
            assert(left + 512usize <= right || right + 512usize <= left) by (nonlinear_arith)
                requires
                    left == left_quotient * 512usize,
                    right == right_quotient * 512usize,
                    left != right;
        };
        ordered_2m_heads_have_disjoint_all_ptrs(right, left);
        assert(page_2m_all_ptrs(left).disjoint(page_2m_all_ptrs(right))) by {
            reveal(Set::disjoint);
        };
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
    assert(krnl.ctn_mp.dom().contains(container_ptr)) by {
        reveal(container_page_owner_wf);
    };
    assert(page_2m_all_ptrs(head).subset_of(krnl.ctn_mp.spec_index(container_ptr).view().owned_pages.view())) by {
        reveal(Set::subset_of);
        reveal(page_2m_all_ptrs);
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
        assert(spec_page_index_merge_2m_valid(head, page_ptr2page_index(page_ptr))) by {
            reveal(page_2m_tail_indices);
        };
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
        reveal(page_2m_all_ptrs);
        page_2m_ptr_prefix_member_bounds(head, 512, page_ptr);
        if page_ptr2page_index(page_ptr) == head {
            assert(
                krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state is Owned2m
            );
        } else {
            owned_4k_page_not_in_2m_tail(krnl, page_ptr, head);
            assert(
                page_2m_tail_indices(head).contains(
                    page_ptr2page_index(page_ptr),
                )
            ) by {
                reveal(page_2m_tail_indices);
            };
        }
    }
}

pub proof fn page_ptr_2m_valid_imply_page_index_2m_valid(page_ptr: PagePtr)
    requires
        page_ptr_2m_valid(page_ptr),
    ensures
        page_index_2m_valid(page_ptr2page_index(page_ptr)),
{
    let quotient = page_ptr / 0x200000usize;
    assert(page_ptr == quotient * 0x200000usize) by (nonlinear_arith)
        requires
            page_ptr % 0x200000usize == 0,
            quotient == page_ptr / 0x200000usize;
    assert(page_ptr2page_index(page_ptr) == quotient * 512usize) by (nonlinear_arith)
        requires
            page_ptr == quotient * 0x200000usize;
    assert(page_ptr2page_index(page_ptr) % 512usize == 0) by (nonlinear_arith)
        requires
            page_ptr2page_index(page_ptr) == quotient * 512usize;
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
    let left_quotient = left / 512usize;
    let right_quotient = right / 512usize;
    assert(left == left_quotient * 512usize) by (nonlinear_arith)
        requires
            left % 512usize == 0,
            left_quotient == left / 512usize;
    assert(right == right_quotient * 512usize) by (nonlinear_arith)
        requires
            right % 512usize == 0,
            right_quotient == right / 512usize;
    assert(left + 512usize <= right || right + 512usize <= left) by (nonlinear_arith)
        requires
            left == left_quotient * 512usize,
            right == right_quotient * 512usize,
            left != right;
    assert(
        page_2m_tail_indices(left).disjoint(
            page_2m_tail_indices(right),
        )
    ) by {
        reveal(page_2m_tail_indices);
    };
}

pub(super) open spec fn page_2m_tail_prefix_indices(
    head: PageIndex, count: usize,
) -> Set<PageIndex> {
    Set::range((head + 1) as usize, (head + 1 + count) as usize)
}

pub open spec fn merged_page_lock_id(index: PageIndex) -> LockId {
    LockId {
        container: LockOwnerId::None,
        process: LockOwnerId::None,
        major: MERGED_PAGE_LOCK_MAJOR,
        minor: index,
    }
}

pub open spec fn owned_2m_tail_lock_perms_wf(
    perms: Map<PageIndex, LockPerm>, krnl: &KernelK, lctx: &LocalContext, head: PageIndex,
) -> bool {
    &&& perms.dom() == page_2m_tail_indices(head)
    &&& forall|index: PageIndex|
        #![trigger perms.dom().contains(index)]
        perms.dom().contains(index) ==> {
            &&& index_valid(NUM_PAGES, index)
            &&& krnl.pg_arr.spec_index(index).view().view().state is Merged2m
            &&& krnl.pg_arr.spec_index(index).view().wlocked_by(lctx)
            &&& perms.spec_index(index).state() is WriteLock
            &&& perms.spec_index(index).thread_id() == lctx.thread_id()
            &&& perms.spec_index(index).lock_id()
                == krnl.pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
    }
}

pub(super) proof fn non_merged_page_not_in_owned_2m_tails(
    perms: Map<PageIndex, LockPerm>, krnl: &KernelK, lctx: &LocalContext,
    head: PageIndex, index: PageIndex,
)
    requires
        owned_2m_tail_lock_perms_wf(perms, krnl, lctx, head),
        index_valid(NUM_PAGES, index),
        !(krnl.pg_arr.spec_index(index).view().view().state is Merged2m),
    ensures
        !page_2m_tail_indices(head).contains(index),
{
    if page_2m_tail_indices(head).contains(index) {
        assert(perms.dom().contains(index)) by { reveal(owned_2m_tail_lock_perms_wf); };
        assert(
            krnl.pg_arr.spec_index(index).view().view().state is Merged2m
        ) by {
            reveal(owned_2m_tail_lock_perms_wf);
        };
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
        old(lctx).lock_id_acyclic(merged_page_lock_id((head + 1) as usize)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).lock_id_acyclic(merged_page_lock_id(
            (head + 512) as usize,
        )),
        held_pages_unchanged(
            old(krnl).pg_arr,
            final(krnl).pg_arr,
            old(lctx),
        ),
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
        final(krnl).pt_mp == old(krnl).pt_mp,
        final(krnl).it_mp == old(krnl).it_mp,
        final(krnl).irt == old(krnl).irt,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).iommu_tlb == old(krnl).iommu_tlb,
        final(krnl).rt_ctn == old(krnl).rt_ctn,
        final(krnl).ctn_mp == old(krnl).ctn_mp,
        final(krnl).sched_mp == old(krnl).sched_mp,
        final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
        final(krnl).cpu_set_mp == old(krnl).cpu_set_mp,
        final(krnl).prc_mp == old(krnl).prc_mp,
        final(krnl).thr_mp == old(krnl).thr_mp,
        final(krnl).ep_mp == old(krnl).ep_mp,
        final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
        final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
        final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
        final(krnl).dflt_pt == old(krnl).dflt_pt,
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view()]
            index_valid(NUM_PAGES, index) ==>
                final(krnl).pg_arr.spec_index(index).view().view()
                    == old(krnl).pg_arr.spec_index(index).view().view(),
        owned_2m_tail_lock_perms_wf(
            ret.view(),
            final(krnl),
            final(lctx),
            head,
        ),
{
    let tracked mut perms: Map<PageIndex, LockPerm> = Map::tracked_empty();
    let mut count: usize = 0;
    proof {
        assert(head + 512usize <= NUM_PAGES) by (nonlinear_arith)
            requires
                head % 512 == 0,
                head < NUM_PAGES,
                NUM_PAGES == 512 * 4096;
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
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, &*lctx),
            lock_id_set_aligned(&*lctx),
            lctx.page_lock_map().remove_keys(
                page_2m_tail_prefix_indices(head, count),
            ) == old(lctx).page_lock_map(),
            lctx.page_lock_map().dom()
                == old(lctx).page_lock_map().dom()
                    .union(page_2m_tail_prefix_indices(head, count)),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
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
                    &&& krnl.pg_arr.spec_index(index).view().view().state is Merged2m
                    &&& krnl.pg_arr.spec_index(index).view().wlocked_by(&*lctx)
                    &&& perms.spec_index(index).state() is WriteLock
                    &&& perms.spec_index(index).thread_id() == lctx.thread_id()
                    &&& perms.spec_index(index).lock_id()
                        == krnl.pg_arr.spec_index(index).view().locking_thread()->Write_lock_id
                },
            lctx.lock_id_acyclic(merged_page_lock_id((head + 1 + count) as usize)),
        decreases 511 - count,
    {
        let index = head + 1usize + count;
        proof {
            assert(index_valid(NUM_PAGES, index)) by (nonlinear_arith)
                requires
                    count < 511,
                    head + 512 <= NUM_PAGES,
                    index == head + 1 + count;
            assert(spec_page_index_merge_2m_valid(head, index)) by (nonlinear_arith)
                requires
                    count < 511,
                    index == head + 1 + count;
            assert(
                krnl.pg_arr.spec_index(head).view().view().state is Owned2m
            ) by {
                assert(
                    krnl.pg_arr.spec_index(head).view().view().state
                        == old(krnl).pg_arr.spec_index(head).view().view().state
                ) by {
                    assert(
                        krnl.pg_arr.spec_index(head).view().view()
                            == old(krnl).pg_arr.spec_index(head).view().view()
                    ) by {
                        assert(index_valid(NUM_PAGES, head)) by (nonlinear_arith)
                            requires page_index_2m_valid(head);
                    };
                };
            };
            assert(
                krnl.pg_arr.spec_index(index).view().view().state is Merged2m
            ) by { reveal(hugepage_2m_wf); };
            assert(
                krnl.pg_arr.lock_id_by_index(index)
                    == merged_page_lock_id(index)
            ) by { reveal(page_array_wf); reveal(merged_page_lock_id); };
            assert(!lctx.page_lock_map().dom().contains(index)) by {
                if lctx.page_lock_map().dom().contains(index) {
                    assert(
                        lctx.typed_lock_entry(KernelObjId::Page(index))
                            .unwrap().lock_id
                            == krnl.pg_arr.lock_id_by_index(index)
                    ) by { reveal(LockedArray::typed_lock_map_aligned); };
                    assert(
                        lctx.lock_id_set().contains((
                            krnl.pg_arr.lock_id_by_index(index),
                            KernelObjId::Page(index),
                        ))
                    ) by { reveal(lock_id_set_aligned); };
                }
            };
            assert(
                !krnl.pg_arr.spec_index(index).view()
                    .locked_by_thread(lctx.thread_id())
            ) by { reveal(LockedArray::typed_lock_map_aligned); };
            assert(
                lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(index))
            ) by { lctx.lemma_lock_id_eq_imply_acyclic_eq(); };
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
                        reveal(page_2m_tail_prefix_indices);
                    }
                );
            };
            assert(
                lctx.page_lock_map().remove_keys(
                    page_2m_tail_prefix_indices(
                        head,
                        (count + 1) as usize,
                    ),
                ) == old(lctx).page_lock_map()
            ) by {
                reveal(typed_lock_maps_inserted);
                reveal(Map::remove_keys);
                assert_maps_equal!(
                    lctx.page_lock_map().remove_keys(
                        page_2m_tail_prefix_indices(
                            head,
                            (count + 1) as usize,
                        ),
                    ),
                    old(lctx).page_lock_map(),
                    key => {}
                );
            };
            if count + 1usize < 511usize {
                assert(
                    lctx.lock_id_acyclic(
                        merged_page_lock_id((head + 1 + count + 1) as usize),
                    )
                ) by {
                    reveal(LocalContext::lock_id_acyclic);
                    reveal(merged_page_lock_id);
                };
            }
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
                    reveal(page_2m_tail_prefix_indices);
                    reveal(page_2m_tail_indices);
                }
            );
        };
        assert(owned_2m_tail_lock_perms_wf(
            perms,
            krnl,
            lctx,
            head,
        )) by { reveal(owned_2m_tail_lock_perms_wf); };
        assert(held_pages_unchanged(
            old(krnl).pg_arr,
            krnl.pg_arr,
            old(lctx),
        )) by {
            reveal(LockedArray::typed_lock_map_aligned);
            reveal(held_pages_unchanged);
        };
    }
    Tracked(perms)
}

pub(super) fn set_owned_2m_page_tails_container(
    pages: &mut PageLockedArray,
    head: PageIndex,
    owning_container: RwLockContainerPtr,
    Tracked(lctx): Tracked<&LocalContext>,
    Tracked(perms): Tracked<&Map<PageIndex, LockPerm>>,
)
    requires
        old(pages).inv(),
        page_index_2m_valid(head),
        old(pages).typed_lock_map_aligned(
            lctx.page_lock_map(),
            lctx.thread_id(),
        ),
        perms.dom() == page_2m_tail_indices(head),
        forall|index: PageIndex|
            #![trigger perms.dom().contains(index)]
            perms.dom().contains(index) ==> {
                &&& index_valid(NUM_PAGES, index)
                &&& old(pages).spec_index(index).view().is_init()
                &&& old(pages).spec_index(index).view().view().state
                    is Merged2m
                &&& old(pages).spec_index(index).view().wlocked_by(lctx)
                &&& perms.spec_index(index).state() is WriteLock
                &&& perms.spec_index(index).thread_id() == lctx.thread_id()
                &&& perms.spec_index(index).lock_id()
                    == old(pages).spec_index(index).view()
                        .locking_thread()->Write_lock_id
            },
    ensures
        final(pages).inv(),
        final(pages).typed_lock_map_aligned(
            lctx.page_lock_map(),
            lctx.thread_id(),
        ),
        forall|index: PageIndex|
            #![trigger final(pages).spec_index(index).view().view()]
            index_valid(NUM_PAGES, index) ==> {
                if page_2m_tail_indices(head).contains(index) {
                    &&& final(pages).spec_index(index).view().view()
                        .owning_container == owning_container
                    &&& final(pages).spec_index(index).view().view().state
                        == old(pages).spec_index(index).view().view().state
                    &&& final(pages).spec_index(index).view().locking_thread()
                        == old(pages).spec_index(index).view().locking_thread()
                } else {
                    final(pages).spec_index(index)
                        == old(pages).spec_index(index)
                }
            },
{
    let mut count: usize = 0;
    while count < 511
        invariant
            pages.inv(),
            page_index_2m_valid(head),
            0 <= count <= 511,
            pages.typed_lock_map_aligned(
                lctx.page_lock_map(),
                lctx.thread_id(),
            ),
            perms.dom() == page_2m_tail_indices(head),
            forall|index: PageIndex|
                #![trigger perms.dom().contains(index)]
                perms.dom().contains(index) ==> {
                    &&& index_valid(NUM_PAGES, index)
                    &&& pages.spec_index(index).view().is_init()
                    &&& pages.spec_index(index).view().view().state
                        is Merged2m
                    &&& pages.spec_index(index).view().wlocked_by(lctx)
                    &&& perms.spec_index(index).state() is WriteLock
                    &&& perms.spec_index(index).thread_id()
                        == lctx.thread_id()
                    &&& perms.spec_index(index).lock_id()
                        == pages.spec_index(index).view()
                            .locking_thread()->Write_lock_id
                },
            forall|index: PageIndex|
                #![trigger pages.spec_index(index).view().view()]
                index_valid(NUM_PAGES, index) ==> {
                    if page_2m_tail_prefix_indices(head, count)
                        .contains(index)
                    {
                        &&& pages.spec_index(index).view().view()
                            .owning_container == owning_container
                        &&& pages.spec_index(index).view().view().state
                            == old(pages).spec_index(index).view().view().state
                        &&& pages.spec_index(index).view().locking_thread()
                            == old(pages).spec_index(index).view()
                                .locking_thread()
                    } else {
                        pages.spec_index(index)
                            == old(pages).spec_index(index)
                    }
                },
        decreases 511 - count,
    {
        let index = head + 1usize + count;
        proof {
            assert(
                page_2m_tail_indices(head).contains(index)
            ) by {
                reveal(page_2m_tail_indices);
            };
            assert(
                pages.spec_index(index).view()
                    .write_lock_perm_match(&perms.spec_index(index))
            ) by {
                reveal(LockedArray::typed_lock_map_aligned);
            };
        }
        let page = pages.borrow_mut_typed(
            index,
            Ghost(lctx.page_lock_map()),
            Tracked(lctx),
            Tracked(perms.tracked_borrow(index)),
        );
        page.owning_container = owning_container;
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
                        reveal(page_2m_tail_prefix_indices);
                    }
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
                    reveal(page_2m_tail_prefix_indices);
                    reveal(page_2m_tail_indices);
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
        owned_2m_tail_lock_perms_wf(
            perms,
            old(krnl),
            old(lctx),
            head,
        ),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl))
            == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).page_lock_map()
            == old(lctx).page_lock_map()
                .remove_keys(page_2m_tail_indices(head)),
        final(lctx).page_lock_map().dom()
            == old(lctx).page_lock_map().dom()
                .difference(page_2m_tail_indices(head)),
        held_pages_unchanged_except(
            old(krnl).pg_arr,
            final(krnl).pg_arr,
            old(lctx),
            page_2m_tail_indices(head),
        ),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index)
                && !page_2m_tail_indices(head).contains(index)
            ==> final(krnl).pg_arr.spec_index(index)
                == old(krnl).pg_arr.spec_index(index),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
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
        final(krnl).pt_mp == old(krnl).pt_mp,
        final(krnl).it_mp == old(krnl).it_mp,
        final(krnl).irt == old(krnl).irt,
        final(krnl).cpu_arr == old(krnl).cpu_arr,
        final(krnl).cpu_tlb == old(krnl).cpu_tlb,
        final(krnl).iommu_tlb == old(krnl).iommu_tlb,
        final(krnl).rt_ctn == old(krnl).rt_ctn,
        final(krnl).ctn_mp == old(krnl).ctn_mp,
        final(krnl).sched_mp == old(krnl).sched_mp,
        final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
        final(krnl).cpu_set_mp == old(krnl).cpu_set_mp,
        final(krnl).prc_mp == old(krnl).prc_mp,
        final(krnl).thr_mp == old(krnl).thr_mp,
        final(krnl).ep_mp == old(krnl).ep_mp,
        final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
        final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
        final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
        final(krnl).dflt_pt == old(krnl).dflt_pt,
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view()]
            index_valid(NUM_PAGES, index) ==>
                final(krnl).pg_arr.spec_index(index).view().view()
                    == old(krnl).pg_arr.spec_index(index).view().view(),
        forall|index: PageIndex|
            #![trigger page_2m_tail_indices(head).contains(index)]
            page_2m_tail_indices(head).contains(index) ==>
                !final(krnl).pg_arr.spec_index(index).view()
                    .locked_by_thread(final(lctx).thread_id()),
{
    let tracked mut perms = perms;
    let mut count: usize = 0;
    while count < 511
        invariant
            krnl.inv(),
            page_index_2m_valid(head),
            0 <= count <= 511,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire
                || lctx.kernel_view_locking_state() is Release,
            count > 0
                ==> lctx.kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(krnl, &*lctx),
            lock_id_set_aligned(&*lctx),
            lctx.page_lock_map()
                == old(lctx).page_lock_map().remove_keys(
                    page_2m_tail_prefix_indices(head, count),
                ),
            lctx.page_lock_map().dom()
                == old(lctx).page_lock_map().dom()
                    .difference(page_2m_tail_prefix_indices(head, count)),
            lctx.cpu_lock_map() == old(lctx).cpu_lock_map(),
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
                    &&& krnl.pg_arr.spec_index(index).view()
                        .wlocked_by(&*lctx)
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
                    !krnl.pg_arr.spec_index(index).view()
                        .locked_by_thread(lctx.thread_id()),
        decreases 511 - count,
    {
        let index = head + 1usize + count;
        proof {
            assert(
                page_2m_tail_indices(head).contains(index)
            ) by {
                reveal(page_2m_tail_indices);
            };
            assert(
                !page_2m_tail_prefix_indices(head, count).contains(index)
            ) by {
                reveal(page_2m_tail_prefix_indices);
            };
            assert(perms.dom().contains(index)) by { broadcast use vstd::set::lemma_set_difference; };
        }
        let tracked perm = perms.tracked_remove(index);
        krnl.wunlock_page(
            index,
            Tracked(&mut *lctx),
            Tracked(perm),
        );
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
                        reveal(page_2m_tail_prefix_indices);
                    }
                );
            };
            assert(
                lctx.page_lock_map()
                    == old(lctx).page_lock_map().remove_keys(
                        page_2m_tail_prefix_indices(
                            head,
                            (count + 1) as usize,
                        ),
                    )
            ) by {
                reveal(typed_lock_maps_removed);
                reveal(Map::remove_keys);
                assert_maps_equal!(
                    lctx.page_lock_map(),
                    old(lctx).page_lock_map().remove_keys(
                            page_2m_tail_prefix_indices(
                                head,
                                (count + 1) as usize,
                            ),
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
                    reveal(page_2m_tail_prefix_indices);
                    reveal(page_2m_tail_indices);
                }
            );
        };
        held_pages_unchanged_except_for_changed_set(
            old(krnl).pg_arr,
            krnl.pg_arr,
            old(lctx),
            page_2m_tail_indices(head),
        );
    }
}

}
