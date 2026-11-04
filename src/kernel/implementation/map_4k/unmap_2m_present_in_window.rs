use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::unmap_2m_present_in_window_eof::*;

verus! {
/// The L2 page that the 2M window `indices` of the read-held `pagetable` links.
fn clear_2m_mapping_l2_ptr(krnl: &KernelK, pagetable: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), Tracked(lctx): Tracked<&LocalContext>, pagetable_perm: Tracked<&LockPerm>)
    -> (ret: PageMapPtr)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(pagetable),
        krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= indices.0 && pei_valid(indices.0) && pei_valid(indices.1) && pei_valid(indices.2),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(indices.0, indices.1) is Some,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == lctx.thread_id(),
        krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
    ensures whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == ret,
{
    proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), pagetable_perm);
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    l3.addr
}

/// Clear the present bit of the 2M leaf `va` of the read-held `pagetable` while the caller holds its window, listing every
/// CPU stale for the window first, and advance the unmap progress of the write-held thread `thrd_ptr` by one page. The leaf
/// leaves the process's 2M user mapping, so the step is recorded against the returned state and local context of the step's end.
pub fn clear_2m_mapping_present_in_window(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, va: VAddr, thrd_ptr: RwLockThreadPtr, Ghost(range): Ghost<VaRange2M>, Ghost(unmapped): Ghost<usize>,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
    Tracked(window_perm): Tracked<&LockPerm>,
) -> (ret: (Ghost<KernelK>, Ghost<LocalContext>))
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).pt_mp.dom().contains(pagetable),
        va_2m_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(va),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va).present,
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus is Some
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).stale_cpus->Some_0.subset_of(Set::range(0usize, NUM_CPUS)),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range, unmapped, flushed: false }),
    ensures
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(*old(krnl)), new_u: kernel_k_to_kernel_u(ret.0@) }),
        final(steps).snapshot_k() == *final(krnl),
        ({
            let before = kernel_k_to_kernel_u(*old(krnl));
            let process = old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc;
            &&& before.process_map.dom().contains(process)
            &&& before.process_map[process].pagetable is Some
            &&& before.process_map[process].pagetable->Some_0.mapping_2m.dom().contains(va)
            &&& before.thread_map.dom().contains(thrd_ptr)
            &&& kernel_k_to_kernel_u(ret.0@) == (KernelU {
                process_map: before.process_map.insert(process, ProcessU {
                    pagetable: Some(PageTableU { mapping_2m: before.process_map[process].pagetable->Some_0.mapping_2m.remove(va), ..before.process_map[process].pagetable->Some_0 }),
                    ..before.process_map[process]
                }),
                thread_map: before.thread_map.insert(thrd_ptr, ThreadU {
                    syscall_progress: Some(SyscallProgress::Unmap2m { range, unmapped: (unmapped + 1) as usize, flushed: false }),
                    ..before.thread_map[thrd_ptr]
                }),
                ..before
            })
        }),
        ret.0@ == (KernelK { pt_mp: ret.0@.pt_mp, pt_lower: ret.0@.pt_lower, thrd_mp: ret.0@.thrd_mp, ..*old(krnl) }),
        ret.0@.pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable),
        ret.0@.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        ret.0@.pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        ret.0@.thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        ret.0@.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        ret.0@.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        ret.0@.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        ret.0@.thrd_mp.spec_index(thrd_ptr).view()
            == (Thread { syscall_progress: Ghost(Some(SyscallProgress::Unmap2m { range, unmapped: (unmapped + 1) as usize, flushed: false })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        ret.0@.pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable, ret.0@.pt_lower.view().spec_index(pagetable)),
        whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable).mapping_2m()
            == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().insert(va, MapEntry { present: false, ..whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(va) }),
        whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable).lower.window_stale_cpus == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.insert((
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va)), Set::range(0usize, NUM_CPUS)),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable).lower.l2_owner(p, i) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable).lower.l2_page(p).entry_lock(i).l1()]
            pei_valid(i) && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(p, i) ==> !whole_pagetable(ret.0@.pt_mp, ret.0@.pt_lower.view(), pagetable).lower.l2_entry_hides_l1(p, i),
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
    let indices = va2index(va);
    proof {
        broadcast use spec_va_2m_valid_index_roundtrip;
        assert(indices.0 == spec_v2l4index(va) && indices.1 == spec_v2l3index(va) && indices.2 == spec_v2l2index(va));
        assert(window_of(va).va == va);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).wf_mapping_2m_at(indices.0, indices.1, indices.2);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc);
    }
    let ghost prc_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
    let l2_ptr = clear_2m_mapping_l2_ptr(krnl, pagetable, (indices.0, indices.1, indices.2), Tracked(&*lctx), pagetable_perm);
    krnl.replace_window_stale_cpus(pagetable, Ghost(WindowStaleUpdate::Set { window: window_of(va), cpus: Set::range(0usize, NUM_CPUS) }), Tracked(&*lctx));
    let ghost locked = *krnl;
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable, window_of(va));
    }
    pagetable_map_clear_2m_present_rlocked(&krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, (indices.0, indices.1, indices.2), l2_ptr, Tracked(window_perm), Tracked(&mut *lctx),
        pagetable_perm);
    proof {
        assert(clear_2m_mapping_present_in_window_eof_transition_framing(locked, *krnl, pagetable, va, l2_ptr)) by { reveal(clear_2m_mapping_present_in_window_eof_transition_framing); };
        clear_2m_mapping_present_in_window_eof(locked, *krnl, pagetable, va, l2_ptr);
    }
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::Unmap2m { range, unmapped: (unmapped + 1) as usize, flushed: false })), Tracked(&*lctx), thread_perm);
    let ghost leaf_k = *krnl;
    let ghost leaf_lctx = *lctx;
    proof {
        assert(krnl.pt_lower.view() =~= old(krnl).pt_lower.view().insert(pagetable, krnl.pt_lower.view().spec_index(pagetable)));
        assert(kernel_process_2m_mapping_changed(&steps.snapshot_k(), &*krnl, prc_ptr, pagetable, va)) by { reveal(kernel_process_2m_mapping_changed); };
        kernel_pagetable_2m_present_cleared_and_progress_changed_implies_u_step(&*old(krnl), &leaf_k, pagetable, va, thrd_ptr);
        krnl.kernel_step_boundary_process_2m_mapping_changed_windowed(&mut *lctx, &mut *steps, prc_ptr, pagetable, va, prc_ptr, pagetable, thrd_ptr, thrd_ptr);
    }
    (Ghost(leaf_k), Ghost(leaf_lctx))
}
}
