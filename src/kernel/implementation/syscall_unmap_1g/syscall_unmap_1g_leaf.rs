use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_unmap_1g_leaf_eof::*;

verus! {
/// List every CPU stale for the write-held `pagetable`, clear the present bit of its 1G leaf `va`, and advance the unmap progress of the write-held thread `thrd_ptr` by one page. The leaf leaves the process's 1G user mapping, so the step is recorded against the returned state and local
/// context of the step's end.
pub(super) fn unmap_1g_hide_leaf(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thrd_ptr: RwLockThreadPtr, Ghost(range): Ghost<VaRange1G>, Ghost(unmapped): Ghost<usize>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
) -> (ret: (Ghost<KernelK>, Ghost<LocalContext>))
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_1g_valid(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().spec_index(va).present,
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
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap1g { range, unmapped, flushed: false }),
    ensures
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(ret.0@) }),
        final(steps).snapshot_k() == *final(krnl),
        ret.0@.inv(),
        ret.0@ == (KernelK { pt_mp: ret.0@.pt_mp, thrd_mp: ret.0@.thrd_mp, ..*old(krnl) }),
        ret.0@.pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
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
        ret.0@.thrd_mp.spec_index(thrd_ptr).view()
            == (Thread { syscall_progress: Ghost(Some(SyscallProgress::Unmap1g { range, unmapped: (unmapped + 1) as usize, flushed: false })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable);
            &&& new_c.lower == old_c.lower
            &&& new_c.mapping_1g() == old_c.mapping_1g().insert(va, MapEntry { present: false, ..old_c.mapping_1g().spec_index(va) })
            &&& forall|i4: L4Index| #![trigger new_c.spec_resolve_mapping_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_resolve_mapping_l4(i4) == old_c.spec_resolve_mapping_l4(i4)
            &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_resolve_mapping_l3(i4, i3)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_resolve_mapping_l3(i4, i3) == old_c.spec_resolve_mapping_l3(i4, i3)
            &&& forall|i4: L4Index| #![trigger new_c.spec_held_l4(i4)] old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_held_l4(i4) == old_c.spec_held_l4(i4)
            &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_l3(i4, i3)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_held_l3(i4, i3) == old_c.spec_held_l3(i4, i3)
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
    let l4i = v2l4index(va);
    let l3i = v2l3index(va);
    proof {
        spec_va_1g_valid_index_roundtrip(va);
        krnl.default_pagetable_wf_at(pagetable);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc);
    }
    let ghost prc_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
    krnl.replace_table_stale_cpus(pagetable, Ghost(TableStaleUpdate::Set { cpus: Set::range(0usize, NUM_CPUS) }), Tracked(&*lctx), pagetable_perm);
    let ghost locked = *krnl;
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        krnl.pt_mp.spec_index(pagetable).view().wf_mapping_1g_at(l4i, l3i); krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    pagetable_map_hide_1g_leaf(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable, (l4i, l3i), Tracked(&mut *lctx), pagetable_perm);
    proof {
        assert(unmap_1g_hide_leaf_eof_transition_framing(locked, *krnl, pagetable, va)) by { reveal(unmap_1g_hide_leaf_eof_transition_framing); };
        unmap_1g_hide_leaf_eof(locked, *krnl, pagetable, va);
    }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::Unmap1g { range, unmapped: (unmapped + 1) as usize, flushed: false })), Tracked(&*lctx), thread_perm);
    let ghost leaf_k = *krnl;
    let ghost leaf_lctx = *lctx;
    proof {
        assert(kernel_process_1g_mapping_changed(&steps.snapshot_k(), &*krnl, prc_ptr, pagetable, va)) by { reveal(kernel_process_1g_mapping_changed); };
        krnl.kernel_step_boundary_process_1g_mapping_changed(&mut *lctx, &mut *steps, prc_ptr, pagetable, va);
    }
    (Ghost(leaf_k), Ghost(leaf_lctx))
}
} // verus!
