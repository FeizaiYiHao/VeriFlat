use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_4k_spec::*;
use super::syscall_unmap_4k_trace::*;
use super::syscall_unmap_4k_helpers::unmap_4k_unmap_and_finish;

verus! {
/// With cpu `cpu_id`, its container, process, and running thread write-held since the entry snapshot `entry_lctx` was
/// aligned with: write-locks the process pagetable and unmaps the range when every page of it is a present user 4K leaf;
/// otherwise releases all five locks with no step and returns Error.
pub(super) fn unmap_4k_lock_pagetable_and_unmap(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize,
    container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, Ghost(entry_lctx): Ghost<LocalContext>,
    Tracked(cpu_perm): Tracked<LockPerm>, Tracked(container_perm): Tracked<LockPerm>, Tracked(process_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).view().len() == 0,
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        !(range == 0 || range > usize::MAX / 4096 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range)),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_perm),
        wlock_ensures(old(steps).snapshot_k().ctn_mp.spec_index(container_ptr), old(krnl).ctn_mp.spec_index(container_ptr), old(steps).snapshot_k().ctn_mp.lock_id_by_key(container_ptr), old(lctx), container_perm),
        wlock_ensures(old(steps).snapshot_k().prc_mp.spec_index(process_ptr), old(krnl).prc_mp.spec_index(process_ptr), old(steps).snapshot_k().prc_mp.lock_id_by_key(process_ptr), old(lctx), process_perm),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_perm),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(container_ptr).view().zombie,
        !old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
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
        ret == unmap_4k_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range),
        ret is Success ==> range + 3 <= final(steps).nonlock_view().len() <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4,
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0 && kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
        !(ret is Success) ==> final(steps).view().len() == 0,
        ret is Success ==> unmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range),
        ret is Success ==> {
            let process = old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap();
            let pt = old(steps).snapshot_k().prc_mp.spec_index(process).view().pagetable;
            &&& range > 0
            &&& va_4k_range_valid(va, range)
            &&& final(krnl).pt_mp.dom().contains(pt)
            &&& final(krnl).pt_mp.spec_index(pt).view().mapping_4k() == old(steps).snapshot_k().pt_mp.spec_index(pt).view().mapping_4k().remove_keys(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize)).to_set())
            &&& final(krnl).pt_mp.spec_index(pt).view().mapping_2m() == old(steps).snapshot_k().pt_mp.spec_index(pt).view().mapping_2m()
            &&& final(krnl).pt_mp.spec_index(pt).view().mapping_1g() == old(steps).snapshot_k().pt_mp.spec_index(pt).view().mapping_1g()
        },
{
    let va_range = VaRange4K::new(va, range);
    assert(krnl.prc_mp.view().spec_index(process_ptr).is_init() && krnl.prc_mp.view().spec_index(process_ptr).addr() == process_ptr) by { process_perms_wf_at(krnl.prc_mp, process_ptr); };
    let process = krnl.prc_mp.borrow_rodata(process_ptr).borrow();
    let pagetable = process.pagetable;
    let cr3 = process.cr3;
    let pcid = process.pcid;
    assert({
        &&& krnl.pt_mp.dom().contains(pagetable)
        &&& krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable
        &&& krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3
        &&& krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid)
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3
        &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
        &&& page_ptr_valid(cr3)
        &&& pcid_valid(pcid)
        &&& pcid != KERNEL_DEFAULT_PCID
    }) by {
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr);
        process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, process_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable); krnl.pt_mp.spec_index(pagetable).view().table_pages_wf_cr3_at();
    };
    assert(old(steps).snapshot_k().pt_mp.dom().contains(pagetable)
        && pagetable == old(steps).snapshot_k().prc_mp.spec_index(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap()).view().pagetable) by {
        process_cpu_wf_at(old(steps).snapshot_k().prc_mp, old(steps).snapshot_k().cpu_arr, cpu_id);
        process_pagetable_match_process_at(old(steps).snapshot_k().prc_mp, old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view().current_process.unwrap());
    };
    let Tracked(pagetable_perm) = krnl.wlock_pagetable(pagetable, Tracked(&mut *lctx));
    assert(krnl.pt_mp.perms_wf()) by { pagetable_perms_wf_map(krnl.pt_mp); };
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&pagetable_perm));
    let indices = va2index(va);
    proof { assert(va_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })) by { va_range.va_range_lemma(); }; }
    if pt.kernel_l4_end <= indices.0 && share_mapping_4k_source_precheck(krnl, &va_range, pagetable, Tracked(&*lctx), Tracked(&pagetable_perm)) {
        unmap_4k_unmap_and_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, &va_range, container_ptr, process_ptr, thread_ptr, pagetable, cr3, pcid,
            Ghost(entry_lctx), Tracked(cpu_perm), Tracked(container_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(pagetable_perm));
        return RetValueType::Success;
    }
    unmap_4k_unlock_all_rejected(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable, Ghost(entry_lctx),
        Tracked(cpu_perm), Tracked(container_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(pagetable_perm));
    proof { unmap_4k_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, RetValueType::Error); }
    RetValueType::Error
}

/// With cpu `cpu_id`, its container, process, running thread, and the process pagetable `pagetable` write-held since the
/// entry snapshot `entry_lctx` was aligned with and nothing else changed: releases all five locks and records no step.
fn unmap_4k_unlock_all_rejected(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, pagetable: RwLockPageTableRoot, Ghost(entry_lctx): Ghost<LocalContext>,
    Tracked(cpu_perm): Tracked<LockPerm>, Tracked(container_perm): Tracked<LockPerm>, Tracked(process_perm): Tracked<LockPerm>, Tracked(thread_perm): Tracked<LockPerm>,
    Tracked(pagetable_perm): Tracked<LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k().inv(),
        typed_lock_maps_aligned(&old(steps).snapshot_k(), &entry_lctx),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, pt_mp: old(krnl).pt_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, process_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, thread_ptr),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_perm),
        wlock_ensures(old(steps).snapshot_k().ctn_mp.spec_index(container_ptr), old(krnl).ctn_mp.spec_index(container_ptr), old(steps).snapshot_k().ctn_mp.lock_id_by_key(container_ptr), old(lctx), container_perm),
        wlock_ensures(old(steps).snapshot_k().prc_mp.spec_index(process_ptr), old(krnl).prc_mp.spec_index(process_ptr), old(steps).snapshot_k().prc_mp.lock_id_by_key(process_ptr), old(lctx), process_perm),
        wlock_ensures(old(steps).snapshot_k().thr_mp.spec_index(thread_ptr), old(krnl).thr_mp.spec_index(thread_ptr), old(steps).snapshot_k().thr_mp.lock_id_by_key(thread_ptr), old(lctx), thread_perm),
        wlock_ensures(old(steps).snapshot_k().pt_mp.spec_index(pagetable), old(krnl).pt_mp.spec_index(pagetable), old(steps).snapshot_k().pt_mp.lock_id_by_key(pagetable), old(lctx), pagetable_perm),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        !old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).prc_mp.dom().contains(process_ptr),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).pt_mp.dom().contains(pagetable),
        old(krnl).pt_mp.spec_index(pagetable).view().leaves_present(),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pagetable, old(krnl).pt_mp.spec_index(pagetable).view()),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
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
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
{
    krnl.wunlock_pagetable(pagetable, Tracked(&mut *lctx), Tracked(pagetable_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_perm));
    krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_perm));
    proof { steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, Some(pagetable), None); }
}
} // verus!
