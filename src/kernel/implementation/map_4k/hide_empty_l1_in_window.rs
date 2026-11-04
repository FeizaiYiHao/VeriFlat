use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::hide_empty_l1_in_window_eof::*;

verus! {
/// The L2 page and the L1 page that the 2M window `indices` of the read-held `pagetable` links and resolves.
fn hide_empty_l1_table_ptrs(krnl: &KernelK, pagetable: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), Tracked(lctx): Tracked<&LocalContext>, pagetable_perm: Tracked<&LockPerm>)
    -> (ret: (PageMapPtr, PageMapPtr))
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(pagetable),
        krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= indices.0 && pei_valid(indices.0) && pei_valid(indices.1) && pei_valid(indices.2),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == lctx.thread_id(),
        krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
    ensures
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == ret.0,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == ret.1,
{
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), pagetable_perm);
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let l2 = pt.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).unwrap();
    (l3.addr, l2.addr)
}

/// Hide the L1 page that the 2M window of `va` in the read-held `pagetable` links and that maps no 4K page: every CPU is
/// listed stale for the window first, then its L2 entry is published with the present bit clear and the L1 address kept.
/// The caller holds the window; no user-visible state changes, so the snapshot moves to the returned state. Returns the
/// window's L2 page and the hidden L1 page.
pub fn hide_empty_l1_in_window(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    pagetable_perm: Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>) -> (ret: (PageMapPtr, PageMapPtr))
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) is Some,
        forall|l1i: L1Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, l1i)))]
            pei_valid(l1i) ==> !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, l1i))),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is Some
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus->Some_0.subset_of(Set::range(0usize, NUM_CPUS)),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
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
        {
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            let l4i = spec_va2index(va).0;
            let l3i = spec_va2index(va).1;
            let l2i = spec_va2index(va).2;
            &&& pre.spec_resolve_mapping_l3(l4i, l3i) is Some && pre.spec_resolve_mapping_l3(l4i, l3i)->0.addr == ret.0
            &&& pre.spec_resolve_mapping_l2(l4i, l3i, l2i)->0.addr == ret.1
            &&& post.mapping_4k() == pre.mapping_4k()
            &&& post.mapping_2m() == pre.mapping_2m()
            &&& post.mapping_1g() == pre.mapping_1g()
            &&& post.page_closure() == pre.page_closure()
            &&& post.lower.pagetable_window_locks == pre.lower.pagetable_window_locks
            &&& post.lower.window_stale_cpus == pre.lower.window_stale_cpus.insert((ret.0, l2i), Set::range(0usize, NUM_CPUS))
            &&& post.lower.l2_entry_hides_l1(ret.0, l2i)
            &&& post.lower.l2_entry(ret.0, l2i).addr == ret.1
            &&& post.spec_resolve_mapping_l2(l4i, l3i, l2i) is None
            &&& forall|l1i: L1Index| #![trigger post.lower.l1_page(ret.0, l2i).spec_index(l1i)] pei_valid(l1i) ==> !post.lower.l1_page(ret.0, l2i).spec_index(l1i).perm.kernel_present
        },
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_entry(p, i)]
            (p, i) != (ret.0, spec_va2index(va).2) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_entry(p, i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry(p, i),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && w != window_of(va)
            ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w),
{
    let indices = va2index(va);
    proof {
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        spec_va_4k_index_roundtrip_at(window_of(va).va, indices.0, indices.1, indices.2, 0usize);
    }
    let (l2_ptr, l1_ptr) = hide_empty_l1_table_ptrs(krnl, pagetable, (indices.0, indices.1, indices.2), Tracked(&*lctx), pagetable_perm);
    krnl.replace_window_stale_cpus(pagetable, Ghost(WindowStaleUpdate::Set { window: window_of(va), cpus: Set::range(0usize, NUM_CPUS) }), Tracked(&*lctx));
    let ghost locked = *krnl;
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
    }
    pagetable_map_hide_l1_page_rlocked(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), l2_ptr, l1_ptr, Tracked(window_perm), Tracked(&mut *lctx),
        pagetable_perm);
    proof {
        assert(hide_empty_l1_in_window_eof_transition_framing(locked, *krnl, pagetable, va, l2_ptr)) by { reveal(hide_empty_l1_in_window_eof_transition_framing); };
        hide_empty_l1_in_window_eof(locked, *krnl, pagetable, va, l2_ptr);
        hide_empty_l1_in_window_eof_hidden_l1_empty(locked, *krnl, pagetable, va, l2_ptr);
        hide_empty_l1_in_window_eof_held_windows(*old(krnl), *krnl, pagetable, va, l2_ptr, *old(lctx));
        assert(krnl.pt_lower.view() =~= old(krnl).pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    (l2_ptr, l1_ptr)
}
}
