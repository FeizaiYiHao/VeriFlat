use vstd::prelude::*;
use crate::*;

verus! {
pub fn mark_pcid_needflush_and_load(krnl: &mut KernelK, cpu_id: CpuId, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>, needflush_perm: Tracked<&LockPerm>) -> (ret: (PageTableRoot, Pcid))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_perm.view().state() is WriteLock,
        needflush_perm.view().thread_id() == old(lctx).thread_id(),
        needflush_perm.view().lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] old(krnl).pt_mp.dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).lock_id_set() == old(lctx).lock_id_set(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pcid_needflush: final(krnl).pcid_needflush, ..*old(krnl) }),
        ret == final(krnl).cpu_published[cpu_id as int].view(),
        page_ptr_valid(ret.0),
        pcid_valid(ret.1),
        cpu_id != final(lctx).cpu_id() && final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid ==> ret == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, pcid),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush,
        final(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid) == old(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread(),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).pcid_needflush.spec_index(c, p)] #![trigger old(krnl).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(krnl).pcid_needflush.spec_index(c, p) == old(krnl).pcid_needflush.spec_index(c, p),
{
    krnl.mark_pcid_needflush(cpu_id, pcid, Tracked(&*lctx), needflush_perm);
    assert(krnl.pcid_needflush.lock_id_by_index(cpu_id, pcid) == old(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid)) by { reveal(pcid_needflush_wf); };
    let ret = krnl.load_published_pcid_cr3(cpu_id, Tracked(&mut *lctx));
    proof {
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl);
        };
    }
    ret
}
pub fn flush_remote_pcid_and_clear(krnl: &mut KernelK, cpu_id: CpuId, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>, needflush_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lctx.kernel_view_locking_state() is Release,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id != lctx.cpu_id(),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_perm.view().state() is WriteLock,
        needflush_perm.view().thread_id() == lctx.thread_id(),
        needflush_perm.view().lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] old(krnl).pt_mp.dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, ..*old(krnl) }),
        final(krnl).cpu_tlb.view() == old(krnl).cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        final(krnl).cpu_tlb.spec_index((cpu_id, pcid)).is_empty(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).cpu_tlb.spec_index((c, p))] #![trigger old(krnl).cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(krnl).cpu_tlb.spec_index((c, p)) == old(krnl).cpu_tlb.spec_index((c, p)),
        !final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush,
        final(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid) == old(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread(),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).pcid_needflush.spec_index(c, p)] #![trigger old(krnl).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(krnl).pcid_needflush.spec_index(c, p) == old(krnl).pcid_needflush.spec_index(c, p),
{
    assert(krnl.pcid_needflush.spec_index(cpu_id, pcid).inv()) by { reveal(pcid_needflush_wf); };
    krnl.cpu_tlb.flush_remote_pcid(cpu_id, pcid, Tracked(lctx));
    let entry = krnl.pcid_needflush.borrow_mut_typed(cpu_id, pcid, Ghost(lctx.pcid_needflush_lock_map()), Tracked(lctx), needflush_perm);
    entry.set(false);
    proof {
        assert(krnl.subsystems_inv()) by { reveal(pcid_needflush_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
            kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl);
        };
        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
        assert(typed_lock_maps_aligned(krnl, lctx)) by { reveal(LockedArray2D::typed_lock_map_aligned); };
    }
}

pub fn flush_local_pcid_and_clear(krnl: &mut KernelK, cpu_id: CpuId, pcid: Pcid, cr3: PageTableRoot, Tracked(lctx): Tracked<&LocalContext>, needflush_perm: Tracked<&LockPerm>, cpu_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        lctx.kernel_view_locking_state() is Release,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == lctx.cpu_id(),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        page_ptr_valid(cr3),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == lctx.thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(lctx.pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_perm.view().state() is WriteLock,
        needflush_perm.view().thread_id() == lctx.thread_id(),
        needflush_perm.view().lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] old(krnl).pt_mp.dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        typed_lock_maps_aligned(final(krnl), lctx),
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_tlb: final(krnl).cpu_tlb, pcid_needflush: final(krnl).pcid_needflush, ..*old(krnl) }),
        final(krnl).cpu_arr.entries_unchanged_except(&old(krnl).cpu_arr, cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view_rodata() == old(krnl).cpu_arr.spec_index(cpu_id).view().view_rodata(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view_ghost() == old(krnl).cpu_arr.spec_index(cpu_id).view().view_ghost(),
        final(krnl).cpu_tlb.view() == old(krnl).cpu_tlb.view().insert((cpu_id, pcid), SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() }),
        final(krnl).cpu_tlb.spec_index((cpu_id, pcid)).is_empty(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).cpu_tlb.spec_index((c, p))] #![trigger old(krnl).cpu_tlb.spec_index((c, p))] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(krnl).cpu_tlb.spec_index((c, p)) == old(krnl).cpu_tlb.spec_index((c, p)),
        !final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view().needflush,
        final(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid) == old(krnl).pcid_needflush.lock_id_by_index(cpu_id, pcid),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread(),
        final(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).view_ghost(),
        forall|c: CpuId, p: Pcid| #![trigger final(krnl).pcid_needflush.spec_index(c, p)] #![trigger old(krnl).pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> final(krnl).pcid_needflush.spec_index(c, p) == old(krnl).pcid_needflush.spec_index(c, p),
{
    assert(krnl.pcid_needflush.spec_index(cpu_id, pcid).inv()) by { reveal(pcid_needflush_wf); };
    assert(krnl.cpu_arr.inv() && krnl.cpu_arr.spec_index(cpu_id).view().is_init()) by { reveal(cpu_array_wf); };
    let cpu = krnl.cpu_arr.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(lctx), cpu_perm);
    cpu.flush_current_tlb(cpu_id, cr3, pcid, &mut krnl.cpu_tlb, Tracked(lctx));
    let entry = krnl.pcid_needflush.borrow_mut_typed(cpu_id, pcid, Ghost(lctx.pcid_needflush_lock_map()), Tracked(lctx), needflush_perm);
    entry.set(false);
    proof {
        assert(krnl.subsystems_inv()) by { reveal(cpu_array_wf); reveal(pcid_needflush_wf); reveal(cpu_published_wf); reveal(KernelK::default_pagetable_wf); };
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
        assert(krnl.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by { reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
        assert(typed_lock_maps_aligned(krnl, lctx)) by { reveal(LockedArray2D::typed_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); };
    }
}

}
