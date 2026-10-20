use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_4k_present_eof::*;

verus! {
/// Clear the user present bit of the 4K leaf `va` of the write-held `pagetable`; the leaf's 2M window is locked around the
/// write and released before return, so the caller holds no window of any table on entry and exit.
pub fn clear_4k_mapping_present(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < PAGE_TABLE_WINDOW_LOCK_MAJOR,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, final(krnl).pt_lower.view().spec_index(pagetable)),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k()
            == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().insert(va, MapEntry { present: false, ..pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va) }),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
{
    let indices = va2index(va);
    let ghost window_va = spec_index2va((indices.0, indices.1, indices.2, 0usize));
    proof {
        let (l4i, l3i, l2i) = (indices.0, indices.1, indices.2);
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
        assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
    }
    let Tracked(window_perm) = krnl.lock_pagetable_window(pagetable, indices.0, indices.1, indices.2, pagetable_perm, Tracked(&mut *lctx));
    let ghost locked = *krnl;
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_4k_at(indices.0, indices.1, indices.2, indices.3);
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
    pagetable_map_clear_4k_present(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, indices, l1_ptr, Tracked(&mut *lctx), pagetable_perm);
    proof {
        assert(clear_4k_mapping_present_eof_transition_framing(locked, *krnl, pagetable, va)) by { reveal(clear_4k_mapping_present_eof_transition_framing); };
        clear_4k_mapping_present_eof(locked, *krnl, pagetable, va);
    }
    krnl.unlock_pagetable_window(pagetable, indices.0, indices.1, indices.2, pagetable_perm, Tracked(&mut *lctx), Tracked(window_perm));
    proof {
        assert(lctx.pagetable_window_lock_map() =~= old(lctx).pagetable_window_lock_map()) by {
            map_insert_remove_absent_lemma(old(lctx).pagetable_window_lock_map(), (pagetable, window_va), TypedHeldLock { lock_id: window_lock_id_at(pagetable, window_va), mode: TypedLockMode::Write });
        };
        assert(krnl.pt_lower.view() =~= old(krnl).pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
    }
}
}
