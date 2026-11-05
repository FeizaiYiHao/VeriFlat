use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_2m_spec::*;
use super::syscall_unmap_2m_trace::*;
use super::syscall_unmap_2m_helpers::unmap_2m_unmap_and_finish;

verus! {
/// With cpu `cpu_id` and its running thread write-held since the entry snapshot `entry_lctx` was aligned with: read-locks
/// the pagetable of the thread's process, locks the 2M windows of the range whose L3 entry links an L2 page, and
/// unmaps the range when every page of it is a present user 2M leaf; otherwise releases every lock with no step and returns
/// Error.
pub(super) fn unmap_2m_lock_pagetable_and_unmap(
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
        !(len == 0 || len > usize::MAX / 0x200000 || !spec_va_2m_valid(va) || va >= usize::MAX - len * 0x200000 || !spec_va_2m_range_valid(va, len)),
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
        ret == unmap_2m_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, len),
        !(ret is Success) ==> final(steps).view().len() == 0,
        ret is Success ==> unmap_2m_syscall_trace(final(steps).view(), cpu_id, va, len),
        ret is Success ==> {
            let process = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap();
            let pt = old(steps).snapshot_k().prc_mp.spec_index(process).view().pagetable;
            let va_range = spec_va_range_2m(va, len);
            &&& final(krnl).pt_mp.dom().contains(pt)
            &&& forall|j: int| #![trigger va_range.view()[j]] 0 <= j < len ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt).mapping_2m().dom().contains(va_range.view()[j])
        },
{
    let va_range = VaRange2M::new(va, len);
    proof { va_2m_range_valid_implies_covering_4k_range_valid(va, len); }
    let cover = VaRange4K::new(va, len * 512);
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
    proof {
        krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    }
    let Tracked(pagetable_perm) = krnl.rlock_pagetable(cpu_id, pagetable, Tracked(&mut *lctx));
    assert(krnl.pt_mp.perms_wf()) by { pagetable_perms_wf_map(krnl.pt_mp); };
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_perm));
    let indices = va2index(va);
    let l4_ok = pt.kernel_l4_end <= indices.0;
    if l4_ok {
        let Tracked(window_perms) = krnl.lock_pagetable_range_existing_windows(pagetable, &cover, Tracked(&pagetable_perm), Tracked(&mut *lctx));
        if unmap_2m_range_mapped_present(krnl, &va_range, &cover, pagetable, Tracked(&*lctx), Tracked(&pagetable_perm)) {
            unmap_2m_unmap_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, len, &va_range, &cover, prc_ptr, thrd_ptr, pagetable, cr3, pcid, Ghost(entry_lctx),
                Tracked(cpu_perm), Tracked(thread_perm), Tracked(pagetable_perm), Tracked(window_perms));
            return RetValueType::Success;
        }
        krnl.unlock_pagetable_range_existing_windows(pagetable, &cover, Tracked(&pagetable_perm), Tracked(&mut *lctx), Tracked(window_perms));
        proof {
            assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.pagetable_window_locks =~= whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).lower.pagetable_window_locks);
        }
    }
    proof {
        let table = whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable);
        assert(va_range == spec_va_range_2m(va, len));
        assert(!(spec_v2l4index(va) >= table.kernel_l4_end() && forall|j: int| #![trigger va_range.view()[j]] 0 <= j < len
            ==> table.mapping_2m().dom().contains(va_range.view()[j]) && table.mapping_2m()[va_range.view()[j]].present));
    }
    unmap_2m_unlock_all_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thrd_ptr, pagetable, Ghost(entry_lctx), Tracked(cpu_perm), Tracked(thread_perm),
        Tracked(pagetable_perm));
    proof { unmap_2m_result_from_k(&old(steps).snapshot_k(), cpu_id, va, len, RetValueType::Error); }
    RetValueType::Error
}

/// With cpu `cpu_id` and its running thread write-held and the pagetable `pagetable` of the thread's process read-held since
/// the entry snapshot `entry_lctx` was aligned with, no window held, and no mapping or window lock changed: releases all three
/// locks and records no step.
fn unmap_2m_unlock_all_rejected(
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
        *old(krnl) == (KernelK {
            cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thrd_mp: old(krnl).thrd_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..old(steps).snapshot_k()
        }),
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
        old(steps).snapshot_k().pt_mp.spec_index(pagetable).inv(),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable).wlocked(),
        !old(steps).snapshot_k().pt_mp.spec_index(pagetable).locked_by_thread(old(lctx).thread_id()),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread() == (RwLockState::Read {
            reader_map: (if old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread() is Read { old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map } else { Map::empty() })
                .insert(old(lctx).thread_id(), pagetable_perm.lock_id()),
        }),
        old(krnl).pt_mp.spec_index(pagetable).view() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).view(),
        old(krnl).pt_mp.spec_index(pagetable).being_killed() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).being_killed(),
        old(krnl).pt_lower.view() =~= old(steps).snapshot_k().pt_lower.view().insert(pagetable, old(krnl).pt_lower.view().spec_index(pagetable)),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_4k(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_2m(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g() == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_1g(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.pagetable_window_locks == whole_pagetable(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).lower.pagetable_window_locks,
        pagetable_perm.state() is ReadLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_clean(),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
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
    proof {
        if old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread() is Read {
            assert(old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.insert(lctx.thread_id(), pagetable_perm.lock_id()).remove(lctx.thread_id())
                =~= old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map);
        } else {
            assert(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), pagetable_perm.lock_id()).remove(lctx.thread_id()).dom() =~= Set::empty());
        }
    }
    krnl.runlock_pagetable(cpu_id, pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thrd_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view());
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, Some(thrd_ptr), None, Some(pagetable), None);
    }
}
/// Whether every page of `range` is a present 2M leaf of the pagetable `pagetable_ptr`, read under this thread's read lock on
/// it. On success each page also lies in a 2M window of the covering 4K range under a linked L3 entry, and is the base of
/// its own window. No krnl or LocalContext state changes.
fn unmap_2m_range_mapped_present(krnl: &KernelK, range: &VaRange2M, cover: &VaRange4K, pagetable_ptr: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>)
    -> (ret: bool)
    requires
        krnl.inv(),
        range.wf(),
        range.len > 0,
        *cover == range.covering_4k_range(),
        cover.wf(),
        krnl.pt_mp.typed_lock_map_aligned(lctx.pagetable_lock_map(), lctx.thread_id()),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(range.start),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == lctx.thread_id(),
        krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_lock_perm.lock_id()),
    ensures
        ret == forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(range.view()[j])
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(range.view()[j]).present
        },
        ret ==> forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            &&& krnl.pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(range.view()[j])
            &&& window_of(range.view()[j]).va == range.view()[j]
            &&& va_range_2m_windows(range.covering_4k_range()).contains(window_of(range.view()[j]))
            &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])) is Some
        },
{
    proof {
        va_range_2m_windows_contains_window_of_first_n_pages(*cover, cover.len as int);
        range.wf_implies_view_index_is_start_plus_offset(); cover.wf_implies_view_index_is_start_plus_offset();
    }
    assert({
        &&& krnl.pt_mp.perms_wf()
        &&& krnl.pt_mp.spec_index(pagetable_ptr).is_init()
        &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()
        &&& krnl.pt_lower.view().dom().contains(pagetable_ptr)
    }) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); };
    let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
    let ghost table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let mut i = 0usize;
    while i < range.len
        invariant
            i <= range.len,
            range.wf(),
            *cover == range.covering_4k_range(),
            cover.wf(),
            table == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr),
            table == (WholePageTable { higher: *pagetable, lower: *lower }),
            table.wf(),
            pagetable.kernel_l4_end <= spec_v2l4index(range.start),
            forall|j: int| #![trigger cover.view()[j]] 0 <= j < cover.len ==> va_range_2m_windows(*cover).contains(window_of(cover.view()[j])),
            forall|k: usize| 0 <= k < cover.len ==> cover.view().spec_index(k as int) == spec_va_add_range(cover.start, k),
            forall|k: usize| 0 <= k < range.len ==> range.view().spec_index(k as int) == spec_va_add_range_2m(range.start, k),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> {
                &&& table.mapping_2m().dom().contains(range.view()[j])
                &&& table.mapping_2m().spec_index(range.view()[j]).present
                &&& pagetable.kernel_l4_end <= spec_v2l4index(range.view()[j])
                &&& window_of(range.view()[j]).va == range.view()[j]
                &&& va_range_2m_windows(*cover).contains(window_of(range.view()[j]))
                &&& table.higher.spec_resolve_mapping_l3(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])) is Some
            },
        decreases range.len - i,
    {
        let va = range.index(i);
        let indices = va2index(va);
        proof {
            broadcast use spec_va_2m_valid_index_roundtrip;
            assert(((512 * i) as usize) < cover.len && (512 * i) * 4096 == i * 0x200000) by (nonlinear_arith) requires i < range.len, cover.len == range.len * 512;
            assert(cover.view()[(512 * i) as int] == va);
            assert(spec_va_4k_valid(range.start) && spec_va_4k_valid(va) && range.start <= va);
            spec_v2l4index_monotonic(range.start, va);
            table.wf_mapping_2m_at(indices.0, indices.1, indices.2);
        }
        let (l3_entry, _) = pagetable.resolve_mapping_4k_l3(indices.0, indices.1);
        match l3_entry {
            None => { return false; },
            Some(l3_entry) => {
                match pagetable.get_entry_2m_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3_entry) {
                    None => { return false; },
                    Some(l2_entry) => { if !l2_entry.perm.present { return false; } },
                }
            },
        }
        i = i + 1;
    }
    true
}
} // verus!
