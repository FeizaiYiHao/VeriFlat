use vstd::prelude::*;
use crate::*;
use super::syscall_new_process_spec::*;
use super::syscall_new_process_trace::*;

verus! {
/// Exec state handed from the owner lock phase of `new_process_lock_entry` to its pcid, endpoint, and source checks.
pub(super) struct NewProcessOwnerLocked {
    pub container_ptr: RwLockContainerPtr, pub parent_ptr: RwLockProcessPtr, pub current_thread_ptr: RwLockThreadPtr, pub scheduler_ptr: RwLockSchedulerPtr,
    pub allocator_ptr: RwLockPageAllocatorPtr, pub pcid_allocator_ptr: RwLockPcidAllocatorPtr, pub source_range: VaRange4K,
    pub cpu_lock_perm: Tracked<LockPerm>, pub parent_lock_perm: Tracked<LockPerm>, pub current_thread_lock_perm: Tracked<LockPerm>, pub pcid_allocator_lock_perm: Tracked<LockPerm>,
}

/// Owner lock phase of the new-process entry: validates the arguments and write-locks cpu `cpu_id`, its current process
/// and thread, and its container's pcid allocator, rejecting bad arguments, an idle or killed cpu, and a killed process or
/// thread with every lock released and a stutter trace.
pub(super) fn new_process_lock_cpu_owner(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr,
    range: usize, endpoint_index: Option<EndpointIdx>, with_iommu: bool, Ghost(initial_regs): Ghost<Registers>,
) -> (ret: Result<NewProcessOwnerLocked, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Err ==> ({
            let r = ret->Err_0;
            &&& new_process_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, initial_regs, endpoint_index, with_iommu, r)
            &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& final(lctx).no_locks_held()
            &&& final(steps).nonlock_view().len() == 0
            &&& !(r is SuccessPairUsize || r is SuccessThreeUsize)
            &&& !(new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is Success)
            &&& r == new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu)
        }),
        ret is Ok ==> ({
            let x = ret->Ok_0;
            let base: usize = if with_iommu { 6usize } else { 4usize };
            let cpu = final(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& *final(steps) == *old(steps)
            &&& !(range == 0 || range > usize::MAX / 4096 || range > (usize::MAX - base) / 3 || !spec_va_4k_valid(va) || va >= usize::MAX - range * 4096 || !spec_va_4k_range_valid(va, range))
            &&& x.source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })
            &&& x.source_range.wf()
            &&& final(krnl).inv()
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl) })
            &&& final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, x.parent_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, x.current_thread_ptr)
            &&& final(krnl).pcid_allc_mp.unchanged_except(&old(krnl).pcid_allc_mp, x.pcid_allocator_ptr)
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl))
            &&& old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None
            &&& old(krnl).prc_mp.spec_index(x.parent_ptr).locking_thread() is None
            &&& old(krnl).thr_mp.spec_index(x.current_thread_ptr).locking_thread() is None
            &&& old(krnl).pcid_allc_mp.spec_index(x.pcid_allocator_ptr).locking_thread() is None
            &&& final(krnl).cpu_arr.spec_index(cpu_id).value.killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).value.killer_info()
            &&& !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() && !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& cpu.state == CpuState::Running && cpu.current_process == Some(x.parent_ptr) && cpu.current_thread == Some(x.current_thread_ptr) && cpu.owning_container == x.container_ptr
            &&& final(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
            &&& final(krnl).ctn_mp.dom().contains(x.container_ptr)
            &&& final(krnl).ctn_mp.spec_index(x.container_ptr).view_rodata().view().scheduler == x.scheduler_ptr
            &&& final(krnl).ctn_mp.spec_index(x.container_ptr).view_rodata().view().allocator_ptr_4k == x.allocator_ptr
            &&& final(krnl).ctn_mp.spec_index(x.container_ptr).view_rodata().view().pcid_allocator == x.pcid_allocator_ptr
            &&& final(krnl).pcid_allc_mp.dom().contains(x.pcid_allocator_ptr)
            &&& final(krnl).pcid_allc_mp.perms_wf()
            &&& final(krnl).pcid_allc_mp.spec_index(x.pcid_allocator_ptr).is_init()
            &&& final(krnl).pcid_allc_mp.spec_index(x.pcid_allocator_ptr).view().wf()
            &&& final(krnl).pcid_allc_mp.spec_index(x.pcid_allocator_ptr).view() == old(krnl).pcid_allc_mp.spec_index(x.pcid_allocator_ptr).view()
            &&& final(krnl).prc_mp.dom().contains(x.parent_ptr)
            &&& final(krnl).prc_mp.spec_index(x.parent_ptr).view() == old(krnl).prc_mp.spec_index(x.parent_ptr).view()
            &&& final(krnl).prc_mp.spec_index(x.parent_ptr).view_rodata() == old(krnl).prc_mp.spec_index(x.parent_ptr).view_rodata()
            &&& final(krnl).prc_mp.spec_index(x.parent_ptr).view_ghost() == old(krnl).prc_mp.spec_index(x.parent_ptr).view_ghost()
            &&& !final(krnl).prc_mp.spec_index(x.parent_ptr).being_killed() && !old(krnl).prc_mp.spec_index(x.parent_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(x.parent_ptr).view_rodata().view().owning_container == x.container_ptr
            &&& !final(krnl).prc_mp.spec_index(x.parent_ptr).view().zombie
            &&& (final(krnl).prc_mp.spec_index(x.parent_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(x.parent_ptr).view().state.view() is Zombie)
            &&& final(krnl).thr_mp.dom().contains(x.current_thread_ptr)
            &&& final(krnl).thr_mp.perms_wf()
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).is_init()
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().endpoint_descriptors.wf()
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view() == old(krnl).thr_mp.spec_index(x.current_thread_ptr).view()
            &&& !final(krnl).thr_mp.spec_index(x.current_thread_ptr).being_killed() && !old(krnl).thr_mp.spec_index(x.current_thread_ptr).being_killed()
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().owning_proc == x.parent_ptr
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().owning_container == x.container_ptr
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().syscall_progress.view() is None
            &&& !final(krnl).thr_mp.spec_index(x.current_thread_ptr).view_ghost().exited
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().free_quota_pending_clean()
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& x.cpu_lock_perm.view().state() is WriteLock && x.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& x.cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), x.parent_ptr, TypedLockMode::Write)
            &&& x.parent_lock_perm.view().state() is WriteLock && x.parent_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& x.parent_lock_perm.view().lock_id() == final(krnl).prc_mp.spec_index(x.parent_ptr).locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), x.current_thread_ptr, TypedLockMode::Write)
            &&& x.current_thread_lock_perm.view().state() is WriteLock && x.current_thread_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& x.current_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(x.current_thread_ptr).locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), x.pcid_allocator_ptr, TypedLockMode::Write)
            &&& x.pcid_allocator_lock_perm.view().state() is WriteLock && x.pcid_allocator_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& x.pcid_allocator_lock_perm.view().lock_id() == final(krnl).pcid_allc_mp.spec_index(x.pcid_allocator_ptr).locking_thread()->Write_lock_id
            &&& forall|held_cpu_id: CpuId| #![trigger final(lctx).cpu_lock_map().dom().contains(held_cpu_id)] final(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(final(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).process_lock_map().dom() =~= set![x.parent_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![x.current_thread_ptr]
            &&& final(lctx).pcid_allocator_lock_map().dom() =~= set![x.pcid_allocator_ptr]
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).container_lock_map().dom().is_empty()
            &&& final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_window_lock_map().dom().is_empty()
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& final(lctx).iommu_root_table_lock_map().dom().is_empty()
            &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ2m)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ1g)
        }),
{
    let base_quota: usize = if with_iommu { 6usize } else { 4usize };
    if range == 0 || range > usize::MAX / 4096usize || range > (usize::MAX - base_quota) / 3usize || !va_4k_valid(va)
        || va >= usize::MAX - range * 4096usize || !va_4k_range_valid(va, range)
    {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, None);
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, initial_regs, endpoint_index, with_iommu, RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }
    let source_range = VaRange4K::new(va, range);
    let cpu_lock_res = wlock_cpu_if_running(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id);
    if cpu_lock_res.is_none() {
        proof {
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, initial_regs, endpoint_index, with_iommu, RetValueType::CpuIdle);
            new_process_result_from_k(old(krnl), cpu_id, va, range, endpoint_index, with_iommu, RetValueType::CpuIdle, 0);
        }
        return Err(RetValueType::CpuIdle);
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    proof {
        assert({
            &&& krnl.prc_mp.dom().contains(parent_ptr)
            &&& krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr
            &&& !krnl.prc_mp.spec_index(parent_ptr).view().zombie
            &&& krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
        }) by { process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); };
        assert({
            &&& krnl.thr_mp.dom().contains(current_thread_ptr)
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().container_depth == krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().container_depth
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().process_depth == krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().depth
        }) by { thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); };
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
            &&& krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().container_depth == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
            &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
        }) by {
            container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, parent_ptr); container_perms_wf_at(krnl.ctn_mp, container_ptr); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
        };
    }
    let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
    let pcid_allocator_ptr = container_rodata.borrow().pcid_allocator;
    let scheduler_ptr = container_rodata.borrow().scheduler;
    let allocator_ptr = container_rodata.borrow().allocator_ptr_4k;
    proof {
        assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr) && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().wf()
            && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().owning_container.view() == container_ptr
            && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().container_depth.view() == krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth) by {
            container_pcid_allocator_wf_container_at(krnl.ctn_mp, krnl.pcid_allc_mp, container_ptr); pcid_allocator_perms_wf_at(krnl.pcid_allc_mp, pcid_allocator_ptr);
        };
    }
    let process_res = krnl.wlock_process_unless_killed(parent_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), None, None, None, None);
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, initial_regs, endpoint_index, with_iommu, RetValueType::ErrorProcessKilled);
            new_process_result_from_k(old(krnl), cpu_id, va, range, endpoint_index, with_iommu, RetValueType::ErrorProcessKilled, 0);
        }
        return Err(RetValueType::ErrorProcessKilled);
    }
    let Tracked(parent_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), Some(current_thread_ptr), None, None, None);
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, initial_regs, endpoint_index, with_iommu, RetValueType::ErrorThreadKilled);
            new_process_result_from_k(old(krnl), cpu_id, va, range, endpoint_index, with_iommu, RetValueType::ErrorThreadKilled, 0);
        }
        return Err(RetValueType::ErrorThreadKilled);
    }
    let Tracked(current_thread_lock_perm) = thread_res.unwrap();
    let Tracked(pcid_allocator_lock_perm) = krnl.wlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    Ok(NewProcessOwnerLocked {
        container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_range, cpu_lock_perm: Tracked(cpu_lock_perm),
        parent_lock_perm: Tracked(parent_lock_perm), current_thread_lock_perm: Tracked(current_thread_lock_perm), pcid_allocator_lock_perm: Tracked(pcid_allocator_lock_perm),
    })
}

/// With cpu `cpu_id`, `parent_ptr`, `current_thread_ptr`, `pcid_allocator_ptr`, and the optional `endpoint` write-held and
/// the optional `source_pagetable` read-held, all unchanged since the entry snapshot and no window held: releases them all
/// and finishes the call with `error` and a stutter trace.
pub(super) fn new_process_unlock_and_stutter(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, parent_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, endpoint: Option<RwLockEndpointPtr>, source_pagetable: Option<RwLockPageTableRoot>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(parent_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
    Tracked(pcid_allocator_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<Option<LockPerm>>, Tracked(source_pagetable_lock_perm): Tracked<Option<LockPerm>>,
    Ghost(va): Ghost<VAddr>, Ghost(range): Ghost<usize>, Ghost(initial_regs): Ghost<Registers>, Ghost(endpoint_index): Ghost<Option<EndpointIdx>>, Ghost(with_iommu): Ghost<bool>,
    Ghost(error): Ghost<RetValueType>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        !(error is SuccessPairUsize || error is SuccessThreeUsize),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ep_mp: old(krnl).ep_mp, pt_mp: old(krnl).pt_mp,
            pt_lower: old(krnl).pt_lower, pcid_allc_mp: old(krnl).pcid_allc_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, parent_ptr),
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
        old(krnl).pcid_allc_mp.unchanged_except(&old(steps).snapshot_k().pcid_allc_mp, pcid_allocator_ptr),
        match endpoint { Some(e) => old(krnl).ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, e), None => old(krnl).ep_mp == old(steps).snapshot_k().ep_mp },
        match source_pagetable {
            Some(p) => old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, p),
            None => old(krnl).pt_mp == old(steps).snapshot_k().pt_mp && old(krnl).pt_lower == old(steps).snapshot_k().pt_lower,
        },
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).value.killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.killer_info(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).locking_thread() is None,
        old(krnl).prc_mp.spec_index(parent_ptr).view() == old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).view(),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata() == old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).view_rodata(),
        old(krnl).prc_mp.spec_index(parent_ptr).view_ghost() == old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).view_ghost(),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed() && !old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_ptr).view().state.view() is Zombie,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view() == old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).view(),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() && !old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        old(steps).snapshot_k().pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread() is None,
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view() == old(steps).snapshot_k().pcid_allc_mp.spec_index(pcid_allocator_ptr).view(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_lock_perm.state() is WriteLock && parent_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        pcid_allocator_lock_perm.state() is WriteLock && pcid_allocator_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        (endpoint is Some) == (endpoint_lock_perm is Some),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            let perm = endpoint_lock_perm->Some_0;
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& old(steps).snapshot_k().ep_mp.spec_index(endpoint_ptr).locking_thread() is None
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).view() == old(steps).snapshot_k().ep_mp.spec_index(endpoint_ptr).view()
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed() == old(steps).snapshot_k().ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock && perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        (source_pagetable is Some) == (source_pagetable_lock_perm is Some),
        source_pagetable is Some ==> {
            let pagetable_ptr = source_pagetable->Some_0;
            let perm = source_pagetable_lock_perm->Some_0;
            let entry = old(steps).snapshot_k().pt_mp.spec_index(pagetable_ptr);
            let entry_table = pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable_ptr);
            &&& old(krnl).pt_mp.dom().contains(pagetable_ptr)
            &&& entry.inv() && !entry.wlocked() && !entry.locked_by_thread(old(lctx).thread_id())
            &&& old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == (RwLockState::Read {
                reader_map: (if entry.locking_thread() is Read { entry.locking_thread()->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), perm.lock_id()),
            })
            &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view() == entry.view()
            &&& old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == entry.being_killed()
            &&& old(krnl).pt_lower.view() =~= old(steps).snapshot_k().pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr))
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == entry_table.mapping_4k()
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == entry_table.mapping_2m()
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == entry_table.mapping_1g()
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read)
            &&& perm.state() is ReadLock && perm.thread_id() == old(lctx).thread_id()
        },
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).process_lock_map().dom() =~= set![parent_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> old(lctx).endpoint_lock_map().dom() =~= set![endpoint->Some_0],
        source_pagetable is None ==> old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        source_pagetable is Some ==> old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable->Some_0],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        new_process_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, initial_regs, endpoint_index, with_iommu, error),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        final(steps).nonlock_view().len() == 0,
{
    if source_pagetable.is_some() {
        let tracked perm = source_pagetable_lock_perm.tracked_unwrap();
        proof {
            let entry = steps.snapshot_k().pt_mp.spec_index(source_pagetable->Some_0);
            if entry.locking_thread() is Read {
                assert(entry.locking_thread()->Read_reader_map.insert(lctx.thread_id(), perm.lock_id()).remove(lctx.thread_id()) =~= entry.locking_thread()->Read_reader_map);
            } else {
                assert(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), perm.lock_id()).remove(lctx.thread_id()).dom() =~= Set::empty());
            }
        }
        krnl.runlock_pagetable(source_pagetable.unwrap(), Tracked(&mut *lctx), Tracked(perm));
    }
    if endpoint.is_some() {
        let tracked perm = endpoint_lock_perm.tracked_unwrap();
        krnl.wunlock_endpoint(endpoint.unwrap(), Tracked(&mut *lctx), Tracked(perm));
    }
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
    krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), Some(current_thread_ptr), endpoint, source_pagetable, Some(pcid_allocator_ptr));
        new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range, initial_regs, endpoint_index, with_iommu, error);
    }
}

/// With cpu `cpu_id`, its current process and thread, and its container's pcid allocator write-held: write-locks
/// `endpoint`, if any, read-locks the source page table `pagetable_ptr`, and returns their perms.
pub(super) fn new_process_lock_endpoint_and_source(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, parent_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr, endpoint: Option<RwLockEndpointPtr>, pagetable_ptr: RwLockPageTableRoot,
) -> (ret: (Tracked<Option<LockPerm>>, Tracked<LockPerm>))
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        ({
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& cpu.state == CpuState::Running && cpu.current_process == Some(parent_ptr) && cpu.current_thread == Some(current_thread_ptr)
            &&& old(krnl).ctn_mp.spec_index(cpu.owning_container).view_rodata().view().pcid_allocator == pcid_allocator_ptr
        }),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        endpoint is Some ==> old(krnl).ep_mp.dom().contains(endpoint->Some_0),
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).process_lock_map().dom() =~= set![parent_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).pcid_allocator_lock_map().dom() =~= set![pcid_allocator_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { ep_mp: final(krnl).ep_mp, pt_mp: final(krnl).pt_mp, ..*old(krnl) }),
        match endpoint { Some(e) => final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, e), None => final(krnl).ep_mp == old(krnl).ep_mp },
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        old(krnl).pt_mp.spec_index(pagetable_ptr).inv() && !old(krnl).pt_mp.spec_index(pagetable_ptr).wlocked(),
        !old(krnl).pt_mp.spec_index(pagetable_ptr).locked_by_thread(old(lctx).thread_id()),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == (RwLockState::Read {
            reader_map: (if old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() is Read { old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map } else { Map::empty() })
                .insert(old(lctx).thread_id(), ret.1.view().lock_id()),
        }),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
        final(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).is_init() && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        ret.1.view().state() is ReadLock && ret.1.view().thread_id() == final(lctx).thread_id(),
        (ret.0.view() is Some) == (endpoint is Some),
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            let perm = ret.0.view()->Some_0;
            &&& old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread() is None
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view()
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed() == old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& !final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
            &&& final(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
            &&& typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock && perm.thread_id() == final(lctx).thread_id()
            &&& perm.lock_id() == final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        endpoint is None ==> final(lctx).endpoint_lock_map().dom().is_empty(),
        endpoint is Some ==> final(lctx).endpoint_lock_map().dom() =~= set![endpoint->Some_0],
        final(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).container_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map().dom().is_empty(),
        final(lctx).pcid_needflush_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        final(lctx).holds_no_allocator_locks(PageSize::SZ1g),
{
    let tracked mut endpoint_lock_perm_opt: Option<LockPerm> = None;
    if endpoint.is_some() {
        let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint.unwrap(), Tracked(&mut *lctx));
        proof { endpoint_lock_perm_opt = Some(endpoint_lock_perm); }
    }
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr);
        krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    }
    let source_pagetable_lock_perm = krnl.rlock_pagetable(pagetable_ptr, Tracked(&mut *lctx));
    proof {
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    (Tracked(endpoint_lock_perm_opt), source_pagetable_lock_perm)
}
}
