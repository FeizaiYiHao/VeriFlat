use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_1g_spec::*;
use super::syscall_unmap_1g_trace::*;
use super::syscall_unmap_1g_helpers::unmap_1g_unmap_and_finish;

verus! {
/// With cpu `cpu_id` and its running thread write-held since the entry snapshot `entry_lctx` was aligned with: write-locks the pagetable of the thread's process and unmaps the range when every page of it is a present 1G leaf; otherwise releases every lock with no step and returns Error.
pub(super) fn unmap_1g_lock_pagetable_and_unmap(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, len: usize,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, Ghost(entry_lctx): Ghost<LocalContext>, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        !(len == 0 || len > usize::MAX / 0x40000000 || !spec_va_1g_valid(va) || va >= usize::MAX - len * 0x40000000 || !spec_va_1g_range_valid(va, len)),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        ({
            let pre = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view();
            let post = old(krnl).cpu_arr.spec_index(cpu_id).view();
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_perm.lock_id() })
            &&& post.view().view() == pre.view().view()
            &&& post.view().kernel_call_perm() is None
            &&& post.being_killed() == pre.being_killed()
            &&& post.killer_info() == pre.killer_info()
            &&& cpu_perm.state() is WriteLock
            &&& cpu_perm.thread_id() == old(lctx).thread_id()
        }),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_perm),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).ctn_mp.dom().contains(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        ret is Success || ret is Error,
        ret == unmap_1g_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, len),
        !(ret is Success) ==> final(steps).view().len() == 0,
        ret is Success ==> unmap_1g_syscall_trace(final(steps).view(), cpu_id, va, len),
        ret is Success ==> {
            let process = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap();
            let pt = old(steps).snapshot_k().prc_mp.spec_index(process).view().pagetable;
            let va_range = spec_va_range_1g(va, len);
            &&& final(krnl).pt_mp.dom().contains(pt)
            &&& forall|j: int| #![trigger va_range.view()[j]] 0 <= j < len ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_1g().dom().contains(va_range.view()[j])
        },
{
    let va_range = VaRange1G::new(va, len);
    assert(krnl.prc_mp.view().spec_index(prc_ptr).is_init() && krnl.prc_mp.view().spec_index(prc_ptr).addr() == prc_ptr) by { process_perms_wf_at(krnl.prc_mp, prc_ptr); };
    let process = krnl.prc_mp.borrow_rodata(prc_ptr).borrow();
    let pagetable = process.pagetable;
    let cr3 = process.cr3;
    let pcid = process.pcid;
    assert({
        &&& krnl.pt_mp.dom().contains(pagetable)
        &&& krnl.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable
        &&& krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3
        &&& krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid)
        &&& krnl.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
        &&& page_ptr_valid(cr3)
        &&& pcid_valid(pcid)
        &&& pcid != KERNEL_DEFAULT_PCID
    }) by {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        process_perms_wf_at(krnl.prc_mp, prc_ptr); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, prc_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable);
        krnl.pt_mp.spec_index(pagetable).view().table_pages_wf_cr3_at();
    };
    assert(old(steps).snapshot_k().pt_mp.dom().contains(pagetable)
        && pagetable == old(steps).snapshot_k().prc_mp.spec_index(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view().pagetable) by {
        process_cpu_wf_at(old(steps).snapshot_k().prc_mp, old(steps).snapshot_k().cpu_arr, cpu_id);
        process_pagetable_wf_process_at(old(steps).snapshot_k().prc_mp, old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    proof { krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr); }
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    proof {
        assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable));
        krnl.default_pagetable_wf_at(pagetable);
    }
    if unmap_1g_range_mapped_present(krnl, &va_range, pagetable, Tracked(&*lctx), Tracked(&pagetable_perm)) {
        unmap_1g_unmap_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, len, &va_range, prc_ptr, thrd_ptr, pagetable, cr3, pcid, Ghost(entry_lctx),
            Tracked(cpu_perm), Tracked(thread_perm), Tracked(pagetable_perm));
        RetValueType::Success
    } else {
        proof {
            broadcast use spec_va_1g_valid_index_roundtrip;
            assert(va_range == spec_va_range_1g(va, len));
            unmap_1g_result_from_k(&old(steps).snapshot_k(), cpu_id, va, len, RetValueType::Error);
        }
        unmap_1g_unlock_all_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thrd_ptr, pagetable, Ghost(entry_lctx), Tracked(cpu_perm), Tracked(thread_perm),
            Tracked(pagetable_perm));
        RetValueType::Error
    }
}

/// With cpu `cpu_id` and its running thread write-held and the pagetable `pagetable` of the thread's process write-held since the entry snapshot `entry_lctx` was aligned with, and nothing else changed: releases all three locks and records no step.
fn unmap_1g_unlock_all_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot,
    Ghost(entry_lctx): Ghost<LocalContext>, Tracked(cpu_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>, Tracked(pagetable_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, pt_mp: old(krnl).pt_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).thrd_mp.unchanged_except(&old(steps).snapshot_k().thrd_mp, thrd_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
        ({
            let pre = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view();
            let post = old(krnl).cpu_arr.spec_index(cpu_id).view();
            &&& !pre.locked()
            &&& post.locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: cpu_perm.lock_id() })
            &&& post.view().view() == pre.view().view()
            &&& post.being_killed() == pre.being_killed()
            &&& post.killer_info() == pre.killer_info()
            &&& cpu_perm.state() is WriteLock
            &&& cpu_perm.thread_id() == old(lctx).thread_id()
        }),
        wlock_ensures(old(steps).snapshot_k().thrd_mp.spec_index(thrd_ptr), old(krnl).thrd_mp.spec_index(thrd_ptr), old(steps).snapshot_k().thrd_mp.lock_id_by_key(thrd_ptr), old(lctx), thread_perm),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable).locked(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread() == (RwLockState::Write { thread_id: old(lctx).thread_id(), lock_id: pagetable_perm.lock_id() }),
        old(krnl).pt_mp.spec_index(pagetable).view() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).view(),
        old(krnl).pt_mp.spec_index(pagetable).being_killed() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).being_killed(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index|
            #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view().state.view() is TablesEmptied)
            && !(old(krnl).prc_mp.spec_index(old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr).view().state.view() is Zombie) ==> forall|l4i: L4Index, l3i: L3Index|
            #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
                ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
{
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable), None);
    }
}

/// Whether every page of `range` is a present 1G leaf of the pagetable `pagetable_ptr`, read under this thread's write lock on it. No krnl or LocalContext state changes.
fn unmap_1g_range_mapped_present(krnl: &KernelK, range: &VaRange1G, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>)
    -> (ret: bool)
    requires
        krnl.inv(),
        range.wf(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock,
        pagetable_lock_perm.thread_id() == lctx.thread_id(),
        pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
    ensures
        ret == forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_1g().dom().contains(range.view()[j])
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_1g().spec_index(range.view()[j]).present
        },
{
    assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).is_init() && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()) by {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    };
    let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let ghost table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let mut i = 0usize;
    while i < range.len
        invariant
            i <= range.len,
            range.wf(),
            table == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr),
            table.higher == *pagetable,
            table.wf(),
            pagetable.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> table.mapping_1g().dom().contains(range.view()[j]) && table.mapping_1g().spec_index(range.view()[j]).present,
        decreases range.len - i,
    {
        let va = range.index(i);
        let l4i = v2l4index(va);
        let l3i = v2l3index(va);
        proof { spec_va_1g_valid_index_roundtrip(va); pagetable.wf_mapping_1g_at(l4i, l3i); }
        match pagetable.get_entry_l4(l4i) {
            None => { return false; },
            Some(l4_entry) => {
                match pagetable.get_entry_1g_l3(l4i, l3i, &l4_entry) {
                    None => { return false; },
                    Some(l3_entry) => { if !l3_entry.perm.present { return false; } },
                }
            },
        }
        i = i + 1;
    }
    true
}
} // verus!
