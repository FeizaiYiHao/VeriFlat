use vstd::assert_maps_equal;
use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn wlock_new_container_2m_page_tails(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, left: PageIndex, right: PageIndex,
) -> (ret: (Tracked<Map<PageIndex, LockPerm>>, Tracked<Map<PageIndex, LockPerm>>))
    requires
        old(krnl).inv(),
        page_index_2m_valid(left),
        page_index_2m_valid(right),
        left != right,
        old(krnl).pg_arr.spec_index(left).view().view().state is Owned2m,
        old(krnl).pg_arr.spec_index(right).view().view().state is Owned2m,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().disjoint(page_2m_tail_indices(left).union(page_2m_tail_indices(right))),
        old(lctx).lock_id_acyclic(merged_page_lock_id((left + 1) as usize)),
        old(lctx).lock_id_acyclic(merged_page_lock_id((right + 1) as usize)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        final(lctx).page_lock_map().remove_keys(page_2m_tail_indices(left).union(page_2m_tail_indices(right))) == old(lctx).page_lock_map(),
        final(lctx).page_lock_map().dom() == old(lctx).page_lock_map().dom().union(page_2m_tail_indices(left)).union(page_2m_tail_indices(right)),
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
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index)]
            #![trigger old(krnl).pg_arr.spec_index(index)]
            index_valid(NUM_PAGES, index) && !page_2m_tail_indices(left).union(page_2m_tail_indices(right)).contains(index)
                ==> final(krnl).pg_arr.spec_index(index) == old(krnl).pg_arr.spec_index(index),
        forall|index: PageIndex|
            #![trigger final(krnl).pg_arr.spec_index(index).view().view()]
            index_valid(NUM_PAGES, index) ==> final(krnl).pg_arr.spec_index(index).view().view() == old(krnl).pg_arr.spec_index(index).view().view(),
        owned_2m_tail_lock_perms_wf(ret.0.view(), final(krnl).pg_arr, final(lctx), left),
        owned_2m_tail_lock_perms_wf(ret.1.view(), final(krnl).pg_arr, final(lctx), right),
{
    proof {
        assert(page_2m_tail_indices(left).disjoint(page_2m_tail_indices(right))) by {
            reveal(page_2m_tail_indices);
        };
    }
    let (Tracked(left_perms), Tracked(right_perms)) = if left < right {
        let Tracked(left_perms) = wlock_owned_2m_page_tails(krnl, left, Tracked(&mut *lctx));
        proof {
            assert(lctx.lock_id_acyclic(merged_page_lock_id((right + 1) as usize))) by {
                reveal(LocalContext::lock_id_acyclic);
                reveal(owned_2m_tail_lock_perms_wf);
                reveal(page_2m_tail_indices);
                reveal(merged_page_lock_id);
            };
        }
        let Tracked(right_perms) = wlock_owned_2m_page_tails(krnl, right, Tracked(&mut *lctx));
        (Tracked(left_perms), Tracked(right_perms))
    } else {
        let Tracked(right_perms) = wlock_owned_2m_page_tails(krnl, right, Tracked(&mut *lctx));
        proof {
            assert(lctx.lock_id_acyclic(merged_page_lock_id((left + 1) as usize))) by {
                reveal(LocalContext::lock_id_acyclic);
                reveal(owned_2m_tail_lock_perms_wf);
                reveal(page_2m_tail_indices);
                reveal(merged_page_lock_id);
            };
        }
        let Tracked(left_perms) = wlock_owned_2m_page_tails(krnl, left, Tracked(&mut *lctx));
        (Tracked(left_perms), Tracked(right_perms))
    };
    proof {
        assert(lctx.page_lock_map().remove_keys(page_2m_tail_indices(left).union(page_2m_tail_indices(right))) == old(lctx).page_lock_map()) by {
            reveal(Map::remove_keys);
            assert_maps_equal!(
                lctx.page_lock_map().remove_keys(page_2m_tail_indices(left).union(page_2m_tail_indices(right))),
                old(lctx).page_lock_map(),
                index => {}
            );
        };
        assert(owned_2m_tail_lock_perms_wf(left_perms, krnl.pg_arr, lctx, left)) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_2m_tail_indices);
        };
        assert(owned_2m_tail_lock_perms_wf(right_perms, krnl.pg_arr, lctx, right)) by {
            reveal(owned_2m_tail_lock_perms_wf);
            reveal(page_2m_tail_indices);
        };
    }
    (Tracked(left_perms), Tracked(right_perms))
}


}
