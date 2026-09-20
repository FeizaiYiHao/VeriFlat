use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
#[verifier::spinoff_prover]
pub(super) fn set_4k_page_staging_next(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&LocalContext>, page_ptr: PagePtr, next: PagePtr,
    Tracked(page_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lock_id_set_aligned(lctx),
        page_ptr_valid(page_ptr),
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().state is Owned4k
            || old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().state is Free4k,
        page_lock_perm.state() is WriteLock,
        page_lock_perm.thread_id() == lctx.thread_id(),
        page_lock_perm.lock_id()
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        kernel_k_to_kernel_u(*final(krnl))
            == kernel_k_to_kernel_u(*old(krnl)),
        final(krnl).pg_arr.entries_unchanged_except(
            &old(krnl).pg_arr,
            page_ptr2page_index(page_ptr),
        ),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().free_list == next,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().state
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().state,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
            .view().view().owning_container
            == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().view().owning_container,
        typed_lock_map_contains_mode(lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_lock_perm.lock_id()
            == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr))
                .view().locking_thread()->Write_lock_id,
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
        }) by {
            page_ptr_valid_imply_page_index_valid();
            reveal(page_array_wf);
        };
    }
    {
        let page = krnl.pg_arr.borrow_mut_typed(
            page_index,
            Ghost(lctx.page_lock_map()),
            Tracked(lctx),
            Tracked(page_lock_perm),
        );
        set_4k_staging_next(page, next);
    }
    proof {
        assert(krnl.subsystems_inv()) by {
            reveal(KernelK::default_pagetable_wf);
            reveal(page_array_wf);
        };
        assert(allocator_pages_wf(
            krnl.pg_arr,
            krnl.allc_4k_mp,
            krnl.allc_2m_mp,
            krnl.allc_1g_mp,
        )) by {
            reveal(allocator_4k_pages_wf);
            reveal(allocator_2m_pages_wf);
            reveal(allocator_1g_pages_wf);
        };
        assert(container_page_owner_wf(
            krnl.ctn_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_page_owner_wf);
        };
        assert(hugepage_2m_wf(krnl.pg_arr)) by {
            reveal(hugepage_2m_wf);
        };
        assert(hugepage_1g_wf(krnl.pg_arr)) by {
            reveal(hugepage_1g_wf);
        };
        assert(page_pagetable_wf(
            krnl.pt_mp,
            krnl.pg_arr,
        )) by {
            page_pagetable_wf_preserved_for_nonmapped_page_change(
                old(krnl).pt_mp,
                krnl.pt_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
                page_index,
            );
        };
        assert(container_process_page_pagetable_wf(
            krnl.ctn_mp,
            krnl.prc_mp,
            krnl.pt_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_process_page_pagetable_wf);
        };
        assert(container_pages_wf(
            krnl.pg_arr,
            krnl.ctn_mp,
        )) by {
            reveal(container_pages_wf);
        };
        assert(process_pages_wf(
            krnl.pg_arr,
            krnl.prc_mp,
        )) by {
            reveal(process_pages_wf);
        };
        assert(pagetable_pages_wf(
            krnl.pt_mp,
            krnl.pg_arr,
        )) by {
            reveal(pagetable_pages_wf);
        };
        assert(iommu_table_pages_wf(
            krnl.it_mp,
            krnl.pg_arr,
        )) by {
            reveal(iommu_table_pages_wf);
        };
        assert(thread_pages_wf(
            krnl.thr_mp,
            krnl.pg_arr,
        )) by {
            reveal(thread_pages_wf);
        };
        assert(scheduler_pages_wf(
            krnl.sched_mp,
            krnl.pg_arr,
        )) by {
            reveal(scheduler_pages_wf);
        };
        assert(pcid_allocator_pages_wf(
            krnl.pg_arr,
            krnl.pcid_allc_mp,
        )) by {
            reveal(pcid_allocator_pages_wf);
        };
        assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by { reveal(cpu_set_pages_wf); };
        assert(thread_staged_pages_4k_wf(
            krnl.thr_mp,
            krnl.pg_arr,
        )) by {
            thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(
                old(krnl).thr_mp,
                krnl.thr_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
            );
        };
        assert(thread_staged_pages_2m_wf(
            krnl.thr_mp,
            krnl.pg_arr,
        )) by {
            thread_staged_pages_2m_wf_preserved_for_temp_cache_and_owned_page_state_eq(
                old(krnl).thr_mp,
                krnl.thr_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
            );
        };
        assert(thread_staged_pages_1g_wf(
            krnl.thr_mp,
            krnl.pg_arr,
        )) by {
            thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(
                old(krnl).thr_mp,
                krnl.thr_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
            );
        };
        assert(endpoint_pages_wf(
            krnl.ep_mp,
            krnl.pg_arr,
        )) by {
            reveal(endpoint_pages_wf);
        };
        assert(krnl.allocator_free_pages_wf()) by {
            reveal(allocator_free_page_ptrs_wf);
        };
        assert(container_process_allocator_quota_wf(
            krnl.ctn_mp,
            krnl.prc_mp,
            krnl.thr_mp,
            krnl.allc_4k_mp,
            krnl.allc_2m_mp,
            krnl.allc_1g_mp,
        )) by {
            reveal(container_process_allocator_quota_4k_wf);
            reveal(container_process_allocator_quota_2m_wf);
            reveal(container_process_allocator_quota_1g_wf);
        };
        assert(container_allocator_wf(
            krnl.ctn_mp,
            krnl.allc_4k_mp,
            krnl.allc_2m_mp,
            krnl.allc_1g_mp,
        )) by {
            reveal(container_allocator_wf);
        };
        assert(container_allocator_free_4k_page_wf(
            krnl.allc_4k_mp,
            krnl.pg_arr,
        )) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
            reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        assert(container_allocator_free_2m_page_wf(
            krnl.allc_2m_mp,
            krnl.pg_arr,
        )) by {
            container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(
                krnl.allc_2m_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
                page_index,
            );
        };
        assert(container_allocator_free_1g_page_wf(
            krnl.allc_1g_mp,
            krnl.pg_arr,
        )) by {
            container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(
                krnl.allc_1g_mp,
                old(krnl).pg_arr,
                krnl.pg_arr,
                page_index,
            );
        };
        assert(
            kernel_k_to_kernel_u(*krnl)
                == kernel_k_to_kernel_u(*old(krnl))
        ) by {
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                old(krnl),
                krnl,
            );
        };
    }
}


}
