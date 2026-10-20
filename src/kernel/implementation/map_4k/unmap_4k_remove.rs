use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_4k_remove_eof::*;

verus! {
pub fn remove_4k_mapping_without_free(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>, page_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).addr == page_ptr,
        page_ptr_valid(page_ptr),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page,
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable, pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable)),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.view().state() is WriteLock,
        page_perm.view().thread_id() == old(lctx).thread_id(),
        page_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize))), TypedLockMode::Write),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().remove(va),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).page_closure() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).page_closure(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_entries == old(krnl).pt_mp.spec_index(pagetable).view().kernel_entries,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_lock == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_lock,
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count - 1,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings().remove((pagetable, va)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == if old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 { PageState::Mapped4k } else { PageState::Unavailable },
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
{
    let page_index = page_ptr2page_index(page_ptr);
    let indices = va2index(va);
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable).inv() && spec_index2va(indices) == va) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3); };
    proof {
        let window_va = spec_index2va((indices.0, indices.1, indices.2, 0usize));
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_va);
        assert(spec_v2l4index(window_va) == indices.0 && spec_v2l3index(window_va) == indices.1 && spec_v2l2index(window_va) == indices.2) by {
            broadcast use spec_va_2m_valid_index_roundtrip; spec_index2va_injective();
        };
    }
    let l1_ptr;
    {
        let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
        let l4 = pt.get_entry_l4(indices.0).unwrap();
        let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
        let l2 = pt.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).unwrap();
        l1_ptr = l2.addr;
    }
    assert(index_valid(NUM_PAGES, page_index) && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().inv() && krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k && krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((pagetable, va))) by {
        page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index); mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, va);
    };
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    page_array_remove_4k_mapping_without_free(&mut krnl.pg_arr, page_index, pagetable, va, Tracked(&*lctx), page_perm);
    pagetable_map_unmap_4k_kernel(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, indices, l1_ptr, Tracked(&mut *lctx), pagetable_perm);
    proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }

    proof {
        assert(remove_4k_mapping_without_free_eof_transition_framing(*old(krnl), *krnl, pagetable, va, page_ptr)) by { reveal(remove_4k_mapping_without_free_eof_transition_framing); };
        remove_4k_mapping_without_free_eof(*old(krnl), *krnl, pagetable, va, page_ptr);
        assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).user_view(LockStateU::Unlocked).mapping_4k =~= pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).user_view(LockStateU::Unlocked).mapping_4k);
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_k_to_nonlock_kernel_u(*krnl) == kernel_k_to_nonlock_kernel_u(*old(krnl))) by { kernel_cpu_process_thread_nonlock_fields_unchanged_implies_u_nonlock_eq(old(krnl), krnl); };
    }
}
}
