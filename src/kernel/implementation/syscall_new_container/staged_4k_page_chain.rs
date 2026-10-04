use vstd::{assert_maps_equal, assert_seqs_equal, assert_sets_equal};
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) proof fn page_ptr_sets_disjoint_from_index_disjoint(left: Seq<PagePtr>, right: Seq<PagePtr>)
    requires
        page_ptrs_to_indices(left).disjoint(page_ptrs_to_indices(right)),
    ensures
        left.to_set().disjoint(right.to_set()),
{
    broadcast use Seq::lemma_to_set_map_commutes;
    let left_set = left.to_set();
    let right_set = right.to_set();
    assert(left_set.intersect(right_set) =~= Set::<PagePtr>::empty()) by {
        assert_sets_equal!(
            left_set.intersect(right_set) == Set::<PagePtr>::empty(),
            page_ptr => {
                if left_set.contains(page_ptr) && right_set.contains(page_ptr) {
                    assert(left.to_set().map(|p: PagePtr| page_ptr2page_index(p)).contains(page_ptr2page_index(page_ptr))) by { left.to_set().lemma_map_contains(|p: PagePtr| page_ptr2page_index(p), page_ptr2page_index(page_ptr)); };
                    assert(right.to_set().map(|p: PagePtr| page_ptr2page_index(p)).contains(page_ptr2page_index(page_ptr))) by { right.to_set().lemma_map_contains(|p: PagePtr| page_ptr2page_index(p), page_ptr2page_index(page_ptr)); };
                }
            }
        );
    };
    vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(left_set, right_set);
}

#[verifier::spinoff_prover]
pub(super) proof fn page_ptrs_to_indices_excludes_distinct_valid_page(pages: Seq<PagePtr>, excluded_page: PagePtr)
    requires
        page_ptr_valid(excluded_page),
        forall|i: int|
            #![trigger page_ptr_valid(pages.spec_index(i))]
            0 <= i < pages.len() ==> page_ptr_valid(pages.spec_index(i)),
        !pages.to_set().contains(excluded_page),
    ensures
        !page_ptrs_to_indices(pages).contains(page_ptr2page_index(excluded_page)),
{
    page_ptr_seq_indices_excludes_page(pages, excluded_page);
}

pub(super) proof fn set_disjoint_from_right_subset<A>(left: Set<A>, right: Set<A>, subset: Set<A>)
    requires
        left.disjoint(right),
        subset.subset_of(right),
    ensures
        left.disjoint(subset),
{
}

pub(super) proof fn set_union_subset_of<A>(left: Set<A>, right: Set<A>, superset: Set<A>)
    requires
        left.subset_of(superset),
        right.subset_of(superset),
    ensures
        left.union(right).subset_of(superset),
{
}

#[verifier::spinoff_prover]
pub(super) fn set_4k_page_staging_next(krnl: &mut KernelK, Tracked(lctx): Tracked<&LocalContext>, page_ptr: PagePtr, next: PagePtr, Tracked(page_lock_perm): Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        page_ptr_valid(page_ptr),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Owned4k || old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Free4k,
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == next,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container,
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            ..*old(krnl)
        }),
{
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        assert({
            &&& krnl.pg_arr.inv()
            &&& krnl.pg_arr.spec_index(page_index).view().is_init()
            &&& krnl.pg_arr.spec_index(page_index).view().view().inv()
        }) by { page_ptr_valid_imply_page_index_valid(); reveal(page_array_wf); };
    }
    {
        let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(page_lock_perm));
        set_4k_staging_next(page, next);
    }
    proof {
        assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(page_array_wf); };
        assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(allocator_4k_pages_wf); reveal(allocator_2m_pages_wf); reveal(allocator_1g_pages_wf); };
        assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { reveal(container_page_owner_wf); };
        assert(hugepage_2m_wf(krnl.pg_arr)) by { reveal(hugepage_2m_wf); };
        assert(hugepage_1g_wf(krnl.pg_arr)) by { reveal(hugepage_1g_wf); };
        assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
        assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
        assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { reveal(container_pages_wf); };
        assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { reveal(process_pages_wf); };
        assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
        assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); reveal(page_array_wf); };
        assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_pages_wf); };
        assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by { reveal(scheduler_pages_wf); };
        assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { reveal(pcid_allocator_pages_wf); };
        assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by { reveal(cpu_set_pages_wf); };
        assert(thread_staged_pages_4k_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
        assert(thread_staged_pages_2m_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
        assert(thread_staged_pages_1g_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
        assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { reveal(endpoint_pages_wf); };
        assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by {
            reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(krnl.allc_2m_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
        assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(krnl.allc_1g_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    }
}

#[verifier::spinoff_prover]
pub(super) fn cleanup_published_4k_page_chain(
    krnl: &mut KernelK, count: usize, head: PagePtr, Ghost(page_ptrs): Ghost<Seq<PagePtr>>,
    child_allocator_ptr: RwLockPageAllocatorPtr, child_container_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(page_lock_perms): Tracked<Map<PagePtr, LockPerm>>
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).allc_4k_mp.dom().contains(child_allocator_ptr),
        page_ptrs.len() == count,
        page_ptrs.no_duplicates(),
        head == staged_4k_page_chain_head(page_ptrs),
        page_lock_perms.dom() == page_ptrs.to_set(),
        staged_4k_page_chain(old(krnl).pg_arr, page_ptrs),
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            page_lock_perms.dom().contains(page_ptr) ==> {
                &&& page_ptr_valid(page_ptr)
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_ptr), state: FreePageAllocatorState::GlobalList,
                })
                &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr
                &&& typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                &&& page_lock_perms.spec_index(page_ptr).state() is WriteLock
                &&& page_lock_perms.spec_index(page_ptr).thread_id() == old(lctx).thread_id()
                &&& page_lock_perms.spec_index(page_ptr).lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
            },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().submap_of(old(lctx).page_lock_map()),
        final(lctx).page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs)) == old(lctx).page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs)),
        final(lctx).page_lock_map().dom().disjoint(page_ptrs_to_indices(page_ptrs)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs)),
        held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), page_ptrs_to_indices(page_ptrs)),
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
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(krnl).allc_4k_mp.dom().contains(child_allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(child_allocator_ptr) == old(krnl).allc_4k_mp.spec_index(child_allocator_ptr),
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr,
            ..*old(krnl)
        }),
        forall|page_index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(page_index)]
            #![trigger old(krnl).pg_arr.spec_index(page_index)]
            index_valid(NUM_PAGES, page_index) && !page_ptrs_to_indices(page_ptrs).contains(page_index) ==> final(krnl).pg_arr.spec_index(page_index) == old(krnl).pg_arr.spec_index(page_index),
        forall|page_ptr: PagePtr|
            #![trigger page_ptrs.to_set().contains(page_ptr)]
            page_ptrs.to_set().contains(page_ptr) ==> {
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().free_list == 0
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                    allocator_ptr: Ghost(child_allocator_ptr), state: FreePageAllocatorState::GlobalList,
                })
                &&& final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr
                &&& !final(lctx).page_lock_map().dom().contains(page_ptr2page_index(page_ptr))
            },
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
{
    let tracked mut page_lock_perms = page_lock_perms;
    let mut current = head;
    let mut remaining = count;
    proof {
        assert(page_ptrs.subrange(0, count as int) == page_ptrs
        ) by {
            assert_seqs_equal!(
                page_ptrs.subrange(0, count as int), page_ptrs,
                i => {}
            );
        };
        assert(page_lock_perms.dom() == page_ptrs.subrange(0, remaining as int).to_set()
        ) by {
            assert_sets_equal!(
                page_lock_perms.dom() == page_ptrs.subrange(0, remaining as int).to_set(),
                page_ptr => {
                    page_ptrs.to_set_ensures();
                    page_ptrs.subrange(0, remaining as int).to_set_ensures();
                }
            );
        };
    }
    while remaining > 0
        invariant
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            typed_lock_maps_aligned(krnl, lctx),
            page_ptrs.len() == count,
            page_ptrs.no_duplicates(),
            forall|page_ptr: PagePtr|
                #![trigger page_ptrs.to_set().contains(page_ptr)]
                page_ptrs.to_set().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state is Free4k
                },
            0 <= remaining <= count,
            current == if remaining == 0 {
                STAGED_4K_PAGE_CHAIN_END
            } else {
                page_ptrs.spec_index(remaining - 1)
            },
            page_lock_perms.dom() == page_ptrs.subrange(0, remaining as int).to_set(),
            lctx.page_lock_map().submap_of(old(lctx).page_lock_map()),
            lctx.page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs)) == old(lctx).page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs)),
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
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            krnl.pt_mp == old(krnl).pt_mp,
            krnl.it_mp == old(krnl).it_mp,
            krnl.irt == old(krnl).irt,
            krnl.cpu_arr == old(krnl).cpu_arr,
            krnl.pcid_needflush == old(krnl).pcid_needflush,
            krnl.cpu_published == old(krnl).cpu_published,
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
            krnl.cpu_offline_mp == old(krnl).cpu_offline_mp,
            krnl.cpu_tlb == old(krnl).cpu_tlb,
            krnl.iommu_tlb == old(krnl).iommu_tlb,
            krnl.rt_ctn == old(krnl).rt_ctn,
            krnl.dflt_pt == old(krnl).dflt_pt,
            forall|page_index: PageIndex|
                #![trigger krnl.pg_arr.spec_index(page_index)]
                #![trigger old(krnl).pg_arr.spec_index(page_index)]
                index_valid(NUM_PAGES, page_index) && !page_ptrs_to_indices(page_ptrs).contains(page_index) ==> krnl.pg_arr.spec_index(page_index) == old(krnl).pg_arr.spec_index(page_index),
            forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list]
                0 <= i < remaining ==> {
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                },
            forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list]
                remaining <= i < count ==> {
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == 0
                    &&& !lctx.page_lock_map().dom().contains(page_ptr2page_index(page_ptrs.spec_index(i)))
                },
            forall|page_ptr: PagePtr|
                #![trigger page_ptrs.to_set().contains(page_ptr)]
                page_ptrs.to_set().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Free4k {
                        allocator_ptr: Ghost(child_allocator_ptr), state: FreePageAllocatorState::GlobalList,
                    })
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == child_container_ptr
                },
            forall|page_ptr: PagePtr|
                #![trigger page_lock_perms.dom().contains(page_ptr)]
                page_lock_perms.dom().contains(page_ptr) ==> {
                    &&& page_ptr_valid(page_ptr)
                    &&& typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write)
                    &&& page_lock_perms.spec_index(page_ptr).state() is WriteLock
                    &&& page_lock_perms.spec_index(page_ptr).thread_id() == lctx.thread_id()
                    &&& page_lock_perms.spec_index(page_ptr).lock_id() == krnl.pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id
                },
        decreases remaining,
    {
        let page_ptr = current;
        let old_remaining = remaining;
        let ghost krnl_before = *krnl;
        let ghost lctx_before = *lctx;
        proof {
            broadcast use page_ptr_sequence_index_in_equal_set;
            assert(page_ptrs.to_set().contains(page_ptr)) by { page_ptrs.to_set_ensures(); };
            page_ptr_valid_imply_page_index_valid();
            vstd::seq::lemma_seq_subrange_index(page_ptrs, 0, remaining as int, remaining - 1);
        }
        let page_index = page_ptr2page_index(page_ptr);
        proof { page_array_wf_at(krnl.pg_arr, page_index); }
        let next = {
            let page = krnl.pg_arr.borrow_typed(
                page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_lock_perms.tracked_borrow(page_ptr)));
            page.free_list
        };
        set_4k_page_staging_next(krnl, Tracked(&*lctx), page_ptr, 0, Tracked(page_lock_perms.tracked_borrow(page_ptr)));
        let tracked page_lock_perm = page_lock_perms.tracked_remove(page_ptr);
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        current = next;
        remaining = remaining - 1;
        proof {
            page_ptr_sequence_index_in_mapped_set(page_ptrs, old_remaining - 1);
            assert(page_lock_perms.dom() == page_ptrs.subrange(0, remaining as int).to_set()
            ) by {
                assert_sets_equal!(
                    page_lock_perms.dom() == page_ptrs.subrange(0, remaining as int).to_set(),
                    candidate => {
                        seq_subrange_split_lemma::<PagePtr>();
                        page_ptrs.subrange(0, remaining as int).to_set_ensures();
                        page_ptrs.subrange(0, (remaining + 1) as int).to_set_ensures();
                    }
                );
            };
            assert(lctx.page_lock_map().submap_of(old(lctx).page_lock_map())
            ) by { submap_by_transitivity(lctx.page_lock_map(), lctx_before.page_lock_map(), old(lctx).page_lock_map()); };
            assert forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list]
                0 <= i < remaining implies {
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == if i == 0 {
                            STAGED_4K_PAGE_CHAIN_END
                        } else {
                            page_ptrs.spec_index(i - 1)
                        }
                } by {
                let other_ptr = page_ptrs.spec_index(i);
                assert(page_ptrs.to_set().contains(other_ptr)) by { page_ptrs.to_set_ensures(); };
                assert(page_ptr2page_index(other_ptr) != page_index
                ) by { page_ptr2page_index_injective(); };
            };
            assert forall|i: int|
                #![trigger krnl.pg_arr.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list]
                remaining <= i < count implies {
                    &&& krnl.pg_arr.spec_index(page_ptr2page_index(page_ptrs.spec_index(i))).view().view().free_list == 0
                    &&& !lctx.page_lock_map().dom().contains(page_ptr2page_index(page_ptrs.spec_index(i)))
            } by {
                let other_ptr = page_ptrs.spec_index(i);
                assert(page_ptrs.to_set().contains(other_ptr)) by { page_ptrs.to_set_ensures(); };
                if i != remaining {
                    assert(page_ptr2page_index(other_ptr) != page_index
                    ) by { page_ptr2page_index_injective(); };
                    assert(!lctx.page_lock_map().dom().contains(page_ptr2page_index(other_ptr))
                    ) by {
                        assert(krnl_before.pg_arr.spec_index(page_ptr2page_index(other_ptr)).view().view().free_list == 0
                        ) by { page_ptrs.to_set_ensures(); page_ptr_valid_imply_page_index_valid(); };
                        assert(!lctx_before.page_lock_map().dom().contains(page_ptr2page_index(other_ptr))
                        ) by { page_ptrs.to_set_ensures(); page_ptr_valid_imply_page_index_valid(); };
                    };
                }
            };
        }
    }
    proof {
        assert(held_pages_unchanged_except(old(krnl).pg_arr, krnl.pg_arr, old(lctx), page_ptrs_to_indices(page_ptrs))) by { held_pages_unchanged_except_for_changed_set(old(krnl).pg_arr, krnl.pg_arr, old(lctx), page_ptrs_to_indices(page_ptrs)); };
        let mapped = page_ptrs.map_values(|p: PagePtr| page_ptr2page_index(p));
        assert(lctx.page_lock_map().dom().disjoint(page_ptrs_to_indices(page_ptrs))
        ) by {
            let held_indices = lctx.page_lock_map().dom();
            let staged_indices = mapped.to_set();
            assert(held_indices.intersect(staged_indices) =~= Set::<PageIndex>::empty()) by {
                assert_sets_equal!(
                    held_indices.intersect(staged_indices) == Set::<PageIndex>::empty(),
                    page_index => {
                        if held_indices.contains(page_index) && staged_indices.contains(page_index) {
                            mapped.to_set_ensures();
                            mapped.index_of_first_ensures(page_index);
                            let i = mapped.index_of_first(page_index).unwrap();
                            assert(page_ptrs.to_set().contains(page_ptrs.spec_index(i))) by { page_ptrs.to_set_ensures(); };
                            assert(krnl.pg_arr.spec_index(page_index).view().view().free_list == 0
                            ) by { page_ptrs.to_set_ensures(); page_ptr_valid_imply_page_index_valid(); };
                        }
                    }
                );
            };
            vstd::set_lib::lemma_set_disjoint_iff_empty_intersection(held_indices, staged_indices);
        };
        assert(lctx.page_lock_map() == old(lctx).page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs))
        ) by {
            assert_maps_equal!(
                lctx.page_lock_map(), old(lctx).page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs)),
                page_index => {}
            );
        };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use kernel_endpoint_nonlock_fields_unchanged_for_equal; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    }
}

#[verifier::spinoff_prover]
pub(super) fn allocate_staged_4k_page_chain(
    krnl: &mut KernelK, count: usize, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>
) -> (ret: (PagePtr, Ghost<Seq<PagePtr>>, Tracked<Map<PagePtr, LockPerm>>))
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).kernel_view_locking_state() is Acquire,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= count,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        count == 0 ==> final(steps).view() == old(steps).view() && *final(krnl) == *old(krnl),
        count > 0 ==> final(steps).view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
        old(steps).snapshot_k() == *old(krnl) || count > 0 ==> final(steps).snapshot_k() == *final(krnl),
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        ret.1.view().len() == count,
        ret.1.view().no_duplicates(),
        ret.0 == staged_4k_page_chain_head(ret.1.view()),
        staged_4k_page_chain(final(krnl).pg_arr, ret.1.view()),
        ret.2.view().dom() == ret.1.view().to_set(),
        allocated_4k_page_lock_perms_wf(ret.2.view(), final(krnl), final(lctx), thread_ptr, container_ptr),
        ret.1.view().to_set().subset_of(final(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages.view(),),
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(ret.1.view().to_set()),
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m,
        final(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
        final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress,
        thread_effective_quota_4k(final(krnl).thr_mp.spec_index(thread_ptr)) == thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) - count,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).page_lock_map().remove_keys(page_ptrs_to_indices(ret.1.view())) == old(lctx).page_lock_map(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(ret.1.view())),
        page_ptrs_to_indices(ret.1.view()).disjoint(old(lctx).page_lock_map().dom()),
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
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        forall|held_page: PageIndex| #![trigger final(lctx).page_lock_map().dom().contains(held_page)] final(lctx).page_lock_map().dom().contains(held_page) ==> final(krnl).pg_arr.lock_id_by_index(held_page).major < ALLOCATOR_CACHE_MAJOR,
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
        held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.owners() == final(steps).snapshot_k().irt.owners(),
        final(krnl).irt.iommu_roots() == final(steps).snapshot_k().irt.iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
{
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

    let mut head = STAGED_4K_PAGE_CHAIN_END;
    let ghost mut page_ptrs = Seq::<PagePtr>::empty();
    let tracked mut page_lock_perms:
        Map<PagePtr, LockPerm> = Map::tracked_empty();
    let mut i = 0usize;
    proof {
        broadcast use group_held_objects_unchanged_transitive;
        assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
        assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(page_ptrs.to_set())
        ) by {
            vstd::set::axiom_set_ext_equal(
                krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(),
                old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(page_ptrs.to_set()),
            );
        };
    }
    while i < count
        invariant
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            i == 0 ==> steps.view() == old(steps).view() && *krnl == *old(krnl) && steps.snapshot_u() == old(steps).snapshot_u(),
            i > 0 ==> steps.view() == record_user_view_change(old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(*old(krnl))),
            i > 0 || old(steps).snapshot_k() == *old(krnl) ==> steps.snapshot_k() == *krnl,
            forall|pt: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt) ==> old(krnl).pt_mp.dom().contains(pt),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            krnl.inv(),
            krnl.ctn_mp.dom().contains(container_ptr),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            !krnl.thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress == old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress,
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == lctx.thread_id(),
            thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            lctx.kernel_view_locking_state() is Acquire,
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == steps.snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == steps.snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
            page_ptrs.len() == i,
            page_ptrs.no_duplicates(),
            head == staged_4k_page_chain_head(page_ptrs),
            staged_4k_page_chain(krnl.pg_arr, page_ptrs),
            page_lock_perms.dom() == page_ptrs.to_set(),
            allocated_4k_page_lock_perms_wf(page_lock_perms, krnl, lctx, thread_ptr, container_ptr),
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(page_ptrs.to_set()),
            krnl.thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            krnl.thr_mp.spec_index(thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_2m,
            krnl.thr_mp.spec_index(thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_1g,
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) == thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) - i,
            thread_effective_quota_4k(krnl.thr_mp.spec_index(thread_ptr)) >= count - i,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            lctx.page_lock_map().remove_keys(page_ptrs_to_indices(page_ptrs)) == old(lctx).page_lock_map(),
            lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(page_ptrs)),
            page_ptrs_to_indices(page_ptrs).disjoint(old(lctx).page_lock_map().dom()),
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
            lctx.allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
            lctx.allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
            lctx.allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
            typed_lock_maps_aligned(krnl, lctx),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_MAJOR),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            held_threads_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), set![thread_ptr]),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, krnl.sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            steps.nonlock_view() == old(steps).nonlock_view(),
            0 <= i <= count,
        decreases count - i,
    {
        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        proof { assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; }; }
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(
            krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm)
        );
        proof {
            assert(!page_ptrs.contains(page_ptr) && !page_ptrs.to_set().contains(page_ptr)) by { page_ptrs.to_set_ensures(); };
            assert(staged_4k_page_chain(krnl.pg_arr, page_ptrs)) by { broadcast use page_ptr_sequence_index_in_equal_set; };
            assert(lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(page_ptrs.push(page_ptr)))
            ) by {
                seq_push_lemma::<PagePtr>();
                assert_sets_equal!(
                    lctx.page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_ptrs_to_indices(page_ptrs.push(page_ptr),),),
                    page_index => {
                        broadcast use Seq::lemma_push_map_commute;
                        page_ptrs.map_values(|p: PagePtr| page_ptr2page_index(p)).to_set_ensures();
                        page_ptrs.map_values(|p: PagePtr| page_ptr2page_index(p)).push(page_ptr2page_index(page_ptr)).to_set_ensures();
                    }
                );
            };
            assert(page_ptrs_to_indices(page_ptrs.push(page_ptr)).disjoint(old(lctx).page_lock_map().dom())
            ) by {
                seq_push_lemma::<PagePtr>();
                assert_sets_equal!(
                    page_ptrs.push(page_ptr).map_values(|p: PagePtr| page_ptr2page_index(p)).to_set() == page_ptrs.map_values(|p: PagePtr| page_ptr2page_index(p)).to_set().insert(page_ptr2page_index(page_ptr)),
                    page_index => {
                        broadcast use Seq::lemma_push_map_commute;
                        page_ptrs.map_values(|p: PagePtr| page_ptr2page_index(p)).to_set_ensures();
                        page_ptrs.map_values(|p: PagePtr| page_ptr2page_index(p)).push(page_ptr2page_index(page_ptr)).to_set_ensures();
                    }
                );
            };
        }
        set_4k_page_staging_next(krnl, Tracked(&*lctx), page_ptr, head, Tracked(&page_lock_perm));
        proof {
            assert(staged_4k_page_chain(krnl.pg_arr, page_ptrs)) by { broadcast use page_ptr_sequence_index_in_equal_set; page_ptr2page_index_injective(); };
            assert(staged_4k_page_chain(krnl.pg_arr, page_ptrs.push(page_ptr))) by {
                broadcast use page_ptr_sequence_index_in_equal_set; broadcast use vstd::seq::lemma_seq_push_len; broadcast use vstd::seq::lemma_seq_push_index_same;
                broadcast use vstd::seq::lemma_seq_push_index_different;
                vstd::seq::lemma_seq_push_len(page_ptrs, page_ptr);
                vstd::seq::lemma_seq_push_index_same(page_ptrs, page_ptr, page_ptrs.len() as int);
                if page_ptrs.len() > 0 {
                    vstd::seq::lemma_seq_push_index_different(page_ptrs, page_ptr, page_ptrs.len() - 1);
                }
                seq_push_lemma::<PagePtr>();
                page_ptrs.to_set_ensures();
                page_ptr2page_index_injective();
            };
            assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(page_ptrs.push(page_ptr).to_set())
            ) by {
                assert_sets_equal!(
                    old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(page_ptrs.to_set()).insert(page_ptr) == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().union(page_ptrs.push(page_ptr).to_set()),
                    x => {
                        seq_push_lemma::<PagePtr>();
                        page_ptrs.to_set_ensures();
                        page_ptrs.push(page_ptr).to_set_ensures();
                    }
                );
            };
            assert(page_lock_perms.insert(page_ptr, page_lock_perm).dom() == page_ptrs.push(page_ptr).to_set()
            ) by {
                assert_sets_equal!(
                    page_lock_perms.insert(page_ptr, page_lock_perm).dom() == page_ptrs.push(page_ptr).to_set(),
                    x => {
                        seq_push_lemma::<PagePtr>();
                        page_ptrs.to_set_ensures();
                        page_ptrs.push(page_ptr).to_set_ensures();
                    }
                );
            };
            assert(allocated_4k_page_lock_perms_wf(
                page_lock_perms.insert(page_ptr, page_lock_perm), krnl, lctx, thread_ptr, container_ptr
            )) by { page_ptr2page_index_injective(); };
            page_lock_perms.tracked_insert(page_ptr, page_lock_perm);
            page_ptrs = page_ptrs.push(page_ptr);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            use_type_invariant(&*steps);
            assert(steps.snapshot_u() == kernel_k_to_kernel_u(*krnl)) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); };
            steps.rebase_snapshot_k_if_unchanged(&*krnl);
        }
        head = page_ptr;
        i = i + 1;
    }
    proof {
        assert(page_ptrs.to_set().subset_of(
            krnl.ctn_mp.spec_index(container_ptr).view().owned_pages.view(),
        )) by { page_ptrs.to_set_ensures(); page_ptr_roundtrip(); reveal(container_page_owner_wf); };
    }
    (head, Ghost(page_ptrs), Tracked(page_lock_perms))
}
}
