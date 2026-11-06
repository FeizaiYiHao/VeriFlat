use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_hide_entry_eof::*;

verus! {
/// List every CPU stale for the write-held `pagetable`, hide its resolving L3 entry `(l4i, l3i)`, which links an L2 page with no 2M or 4K leaf, as a placeholder keeping that page, and mark the 1G mmap progress of the write-held thread `thrd_ptr` hidden. The windows under the entry leave
/// the process's user window locks, so the step is recorded against the returned state and local context of the step's end.
pub(super) fn mmap_1g_hide_l3_entry(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, thrd_ptr: RwLockThreadPtr, Ghost(progress): Ghost<SyscallProgress>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
) -> (ret: (Ghost<KernelK>, Ghost<LocalContext>))
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i),
        pei_valid(l3i),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i) is Some,
        forall|i: L2Index|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_2m_l2(l4i, l3i, i)]
            #![trigger old(krnl).pt_lower.view().spec_index(pagetable).l2_entry(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i)->0.addr, i)]
            pei_valid(i) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_2m_l2(l4i, l3i, i) is None,
        forall|i: L2Index, j: L1Index|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_4k_l1(l4i, l3i, i, j)]
            #![trigger old(krnl).pt_lower.view().spec_index(pagetable).l1_page(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i)->0.addr, i).spec_index(j)]
            pei_valid(i) && pei_valid(j) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_4k_l1(l4i, l3i, i, j) is None,
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view().subset_of(Set::range(0usize, NUM_CPUS)),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(progress),
        progress is Mmap1g,
    ensures
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(ret.0@) }),
        final(steps).snapshot_k() == *final(krnl),
        ret.0@.inv(),
        ret.0@ == (KernelK { pt_mp: ret.0@.pt_mp, pt_lower: ret.0@.pt_lower, thrd_mp: ret.0@.thrd_mp, ..*old(krnl) }),
        ret.0@.pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        ret.0@.pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, ret.0@.pt_lower.view().spec_index(pagetable)),
        ret.0@.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        ret.0@.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ret.0@.pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr,
        ret.0@.pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
        ret.0@.pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
        ret.0@.pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        ret.0@.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
        ret.0@.thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        ret.0@.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        ret.0@.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        ret.0@.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        ret.0@.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            syscall_progress: Ghost(Some(SyscallProgress::Mmap1g {
                range: progress->Mmap1g_range, mapped: progress->Mmap1g_mapped, directory: progress->Mmap1g_directory, hidden: true, flushed: progress->Mmap1g_flushed,
            })),
            ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
        }),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable);
            &&& new_c.page_closure() == old_c.page_closure()
            &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g()
            &&& new_c.lower.pagetable_window_locks == old_c.lower.pagetable_window_locks.remove_keys(old_c.lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i))
            &&& new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus && new_c.lower.l2_perms == old_c.lower.l2_perms && new_c.lower.l1_rev_map == old_c.lower.l1_rev_map
            &&& old_c.lower.hidden_l1_tables_in_locked_windows() ==> new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|i4: L4Index| #![trigger new_c.spec_resolve_mapping_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_resolve_mapping_l4(i4) == old_c.spec_resolve_mapping_l4(i4)
            &&& forall|i4: L4Index| #![trigger new_c.spec_held_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_held_l4(i4) == old_c.spec_held_l4(i4)
            &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_resolve_mapping_l3(i4, i3)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != (l4i, l3i) ==> new_c.spec_resolve_mapping_l3(i4, i3) == old_c.spec_resolve_mapping_l3(i4, i3)
            &&& new_c.spec_resolve_mapping_l3(l4i, l3i) is None
            &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_l3(i4, i3)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != (l4i, l3i) ==> new_c.spec_held_l3(i4, i3) == old_c.spec_held_l3(i4, i3)
            &&& new_c.spec_held_l3(l4i, l3i) == Some(PageEntry { addr: old_c.spec_resolve_mapping_l3(l4i, l3i)->0.addr,
                    perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } })
            &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_1g_l3(i4, i3)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_held_1g_l3(i4, i3) == old_c.spec_held_1g_l3(i4, i3)
            &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_resolve_mapping_1g_l3(i4, i3)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_resolve_mapping_1g_l3(i4, i3) == old_c.spec_resolve_mapping_1g_l3(i4, i3)
            &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_l2(i4, i3, i2)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_held_l2(i4, i3, i2) == old_c.spec_held_l2(i4, i3, i2)
            &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_2m_l2(i4, i3, i2)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_held_2m_l2(i4, i3, i2) == old_c.spec_held_2m_l2(i4, i3, i2)
            &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_c.spec_held_4k_l1(i4, i3, i2, i1)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_c.spec_held_4k_l1(i4, i3, i2, i1) == old_c.spec_held_4k_l1(i4, i3, i2, i1)
        }),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable) == whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable),
        kernel_step_boundary_framing(ret.0@, *final(krnl), ret.1@),
        typed_lock_maps_unchanged(old(lctx), &ret.1@),
        ret.1@.cpu_id() == old(lctx).cpu_id() && ret.1@.thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
{
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    }
    krnl.replace_table_stale_cpus(pagetable, Ghost(TableStaleUpdate::Set { cpus: Set::range(0usize, NUM_CPUS) }), Tracked(&*lctx), pagetable_perm);
    let ghost locked = *krnl;
    proof {
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        wlocker_holds_no_windows_implies_l2_windows_unlocked(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, l4i, l3i,
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(l4i, l3i)->0.addr);
    }
    pagetable_map_hide_l3_entry(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (l4i, l3i), Tracked(&mut *lctx), pagetable_perm);
    proof {
        assert(mmap_1g_hide_l3_entry_eof_transition_framing(locked, *krnl, pagetable, l4i, l3i)) by { reveal(mmap_1g_hide_l3_entry_eof_transition_framing); };
        mmap_1g_hide_l3_entry_eof(locked, *krnl, pagetable, l4i, l3i);
    }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::Mmap1g {
        range: progress->Mmap1g_range, mapped: progress->Mmap1g_mapped, directory: progress->Mmap1g_directory, hidden: true, flushed: progress->Mmap1g_flushed,
    })), Tracked(&*lctx), thread_perm);
    let ghost hidden_k = *krnl;
    let ghost hidden_lctx = *lctx;
    proof {
        kernel_pagetable_l3_windows_removed_implies_u_neq(&steps.snapshot_k(), &*krnl, pagetable, l4i, l3i);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
    }
    (Ghost(hidden_k), Ghost(hidden_lctx))
}
} // verus!
