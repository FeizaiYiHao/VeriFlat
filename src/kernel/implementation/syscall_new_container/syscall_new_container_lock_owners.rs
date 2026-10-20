use vstd::prelude::*;
use crate::*;
use super::syscall_new_container::NewContainerOwnersLocked;
use super::syscall_new_container_spec::*;
use super::syscall_new_container_trace::*;

verus! {
/// Takes the cpu and container locks of `new_container_lock_owners` and locks the caller's process and thread, rejecting
/// every failing check with all locks released and a stutter trace from the entry snapshot; otherwise returns the four
/// locks held with the caller's quota and endpoint slot checked.
pub(super) fn new_container_lock_process_and_thread(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, endpoint_index: Option<EndpointIdx>,
    initial_regs: &Registers, source_range: VaRange4K, parent_container_ptr: RwLockContainerPtr, parent_process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, parent_cpu_set: RwLockCpuSetPtr, Tracked(cpu_lock_perm): Tracked<LockPerm>,
    Tracked(container_lock_perm): Tracked<LockPerm>,
) -> (ret: Result<NewContainerOwnersLocked, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0),
        cpu_id == old(lctx).cpu_id(),
        old(steps).snapshot_k().inv(),
        old(steps).nonlock_view().len() == 0,
        source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) }),
        source_range.wf(),
        0 < range <= (usize::MAX - 9) / 3 && range <= usize::MAX / 4096 && va_4k_valid(va) && index_valid(NUM_CPUS, transfer_cpu_id),
        va < usize::MAX - range * 4096 && va_4k_range_valid(va, range),
        process_quota_4k <= funding_page_count && funding_page_count <= usize::MAX - 9 - 3 * range,
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ctn_mp: old(krnl).ctn_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, parent_container_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().ctn_mp.spec_index(parent_container_ptr).locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view(),
        old(krnl).cpu_arr.spec_index(cpu_id).value.killer_info() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.killer_info(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view() == old(steps).snapshot_k().ctn_mp.spec_index(parent_container_ptr).view(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata() == old(steps).snapshot_k().ctn_mp.spec_index(parent_container_ptr).view_rodata(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost() == old(steps).snapshot_k().ctn_mp.spec_index(parent_container_ptr).view_ghost(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == parent_container_ptr,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(parent_process_ptr),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() && !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(lctx).page_lock_map().dom().is_empty() && old(lctx).endpoint_lock_map().dom().is_empty() && old(lctx).pagetable_lock_map().dom().is_empty() && old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty() && old(lctx).pcid_allocator_lock_map().dom().is_empty() && old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty() && old(lctx).iommu_root_table_lock_map().dom().is_empty() && old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty() && old(lctx).process_lock_map().dom().is_empty() && old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k) && old(lctx).holds_no_allocator_locks(PageSize::SZ2m) && old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr],
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed() && !old(steps).snapshot_k().ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).view().zombie,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().container_depth,
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().cpu_set == parent_cpu_set,
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().owned_processes.view().is_empty(),
        container_lock_perm.state() is WriteLock && container_lock_perm.thread_id() == old(lctx).thread_id(),
        container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr,
        !old(krnl).prc_mp.spec_index(parent_process_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().depth == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().process_depth,
        old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().container_depth == old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().depth,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().container_depth == old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().container_depth,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().process_depth == old(krnl).prc_mp.spec_index(parent_process_ptr).view_rodata().view().depth,
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Err ==> ({
            let r = ret->Err_0;
            &&& new_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index, r)
            &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& final(lctx).no_locks_held()
            &&& final(steps).nonlock_view().len() == 0
            &&& !(r is SuccessThreeUsize)
            &&& !(new_container_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index) is Success)
            &&& r == new_container_syscall_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index)
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0;
            &&& *final(steps) == *old(steps)
            &&& e.source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })
            &&& e.source_range.wf()
            &&& 0 < range <= (usize::MAX - 9) / 3 && range <= usize::MAX / 4096 && va_4k_valid(va) && index_valid(NUM_CPUS, transfer_cpu_id)
            &&& va < usize::MAX - range * 4096 && va_4k_range_valid(va, range)
            &&& process_quota_4k <= funding_page_count && funding_page_count <= usize::MAX - 9 - 3 * range
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, ..old(steps).snapshot_k() })
            &&& final(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id)
            &&& final(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, e.parent_container_ptr)
            &&& final(krnl).prc_mp.unchanged_except(&old(steps).snapshot_k().prc_mp, e.parent_process_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, e.current_thread_ptr)
            &&& old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None
            &&& old(steps).snapshot_k().ctn_mp.spec_index(e.parent_container_ptr).locking_thread() is None
            &&& old(steps).snapshot_k().prc_mp.spec_index(e.parent_process_ptr).locking_thread() is None
            &&& old(steps).snapshot_k().thr_mp.spec_index(e.current_thread_ptr).locking_thread() is None
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view()
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view() == old(steps).snapshot_k().ctn_mp.spec_index(e.parent_container_ptr).view()
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata() == old(steps).snapshot_k().ctn_mp.spec_index(e.parent_container_ptr).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_ghost() == old(steps).snapshot_k().ctn_mp.spec_index(e.parent_container_ptr).view_ghost()
            &&& final(krnl).prc_mp.spec_index(e.parent_process_ptr).view() == old(steps).snapshot_k().prc_mp.spec_index(e.parent_process_ptr).view()
            &&& final(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata() == old(steps).snapshot_k().prc_mp.spec_index(e.parent_process_ptr).view_rodata()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view() == old(steps).snapshot_k().thr_mp.spec_index(e.current_thread_ptr).view()
            &&& final(krnl).inv()
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), final(krnl))
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), final(krnl))
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(e.current_thread_ptr)
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == e.parent_container_ptr
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(e.parent_process_ptr)
            &&& !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() && !old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(krnl).cpu_published[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)
            &&& final(lctx).page_lock_map().dom().is_empty() && final(lctx).endpoint_lock_map().dom().is_empty() && final(lctx).pagetable_lock_map().dom().is_empty() && final(lctx).pagetable_window_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty() && final(lctx).pcid_allocator_lock_map().dom().is_empty() && final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).iommu_table_lock_map().dom().is_empty() && final(lctx).iommu_root_table_lock_map().dom().is_empty() && final(lctx).pcid_needflush_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k) && final(lctx).holds_no_allocator_locks(PageSize::SZ2m) && final(lctx).holds_no_allocator_locks(PageSize::SZ1g)
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom() =~= set![e.parent_container_ptr]
            &&& final(lctx).process_lock_map().dom() =~= set![e.parent_process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.current_thread_ptr]
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& e.cpu_lock_perm.view().state() is WriteLock
            &&& e.cpu_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.cpu_lock_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& final(krnl).ctn_mp.dom().contains(e.parent_container_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).container_lock_map(), e.parent_container_ptr, TypedLockMode::Write)
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).being_killed()
            &&& !old(steps).snapshot_k().ctn_mp.spec_index(e.parent_container_ptr).being_killed()
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view().zombie
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata().view().cpu_set == e.parent_cpu_set
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_ghost().owned_processes.view().is_empty()
            &&& e.container_lock_perm.view().state() is WriteLock
            &&& e.container_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.container_lock_perm.view().lock_id() == final(krnl).ctn_mp.spec_index(e.parent_container_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).prc_mp.dom().contains(e.parent_process_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.parent_process_ptr, TypedLockMode::Write)
            &&& !final(krnl).prc_mp.spec_index(e.parent_process_ptr).being_killed()
            &&& !old(steps).snapshot_k().prc_mp.spec_index(e.parent_process_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata().view().owning_container == e.parent_container_ptr
            &&& (final(krnl).prc_mp.spec_index(e.parent_process_ptr).view().state.view() is Running || final(krnl).prc_mp.spec_index(e.parent_process_ptr).view().state.view() is Zombie)
            &&& !old(steps).snapshot_k().prc_mp.spec_index(e.parent_process_ptr).view().zombie
            &&& e.process_lock_perm.view().state() is WriteLock
            &&& e.process_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.process_lock_perm.view().lock_id() == final(krnl).prc_mp.spec_index(e.parent_process_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).thr_mp.dom().contains(e.current_thread_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.current_thread_ptr, TypedLockMode::Write)
            &&& !final(krnl).thr_mp.spec_index(e.current_thread_ptr).being_killed()
            &&& !old(steps).snapshot_k().thr_mp.spec_index(e.current_thread_ptr).being_killed()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().owning_container == e.parent_container_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().owning_proc == e.parent_process_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().proc_pagetable_ptr == e.source_pagetable_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: cpu_id })
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().syscall_progress.view() is None
            &&& !final(krnl).thr_mp.spec_index(e.current_thread_ptr).view_ghost().exited
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().quota_4k >= 9 + funding_page_count + 3 * range
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().quota_2m >= 2
            &&& endpoint_index is Some ==> old(steps).snapshot_k().thr_mp.spec_index(e.current_thread_ptr).view().endpoint_descriptors.wf()
            &&& endpoint_index is Some ==> e.endpoint is Some && e.endpoint == final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index->Some_0)
            &&& endpoint_index is None ==> e.endpoint is None
            &&& e.thread_lock_perm.view().state() is WriteLock
            &&& e.thread_lock_perm.view().thread_id() == final(lctx).thread_id()
            &&& e.thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread()->Write_lock_id
        }),
{
    let process_res = krnl.wlock_process_unless_killed(parent_process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(parent_container_ptr), Some(parent_process_ptr), None, None, None, None);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                RetValueType::ErrorProcessKilled);
            new_container_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, RetValueType::ErrorProcessKilled);
        }
        return Err(RetValueType::ErrorProcessKilled);
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(parent_container_ptr), Some(parent_process_ptr), Some(current_thread_ptr), None, None, None);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                RetValueType::ErrorThreadKilled);
            new_container_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, RetValueType::ErrorThreadKilled);
        }
        return Err(RetValueType::ErrorThreadKilled);
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    let thread = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let quota_4k = thread.quota_4k;
    let quota_2m = thread.quota_2m;
    let source_pagetable_ptr = thread.proc_pagetable_ptr;
    let endpoint_option = match endpoint_index { Some(index) => *thread.endpoint_descriptors.get(index), None => None };
    let endpoint_missing = endpoint_index.is_some() && endpoint_option.is_none();
    let required_4k = 9usize + funding_page_count + 3 * range;
    let quota_available = quota_4k >= required_4k && quota_2m >= 2;
    if endpoint_missing || !quota_available {
        let error = if endpoint_missing { RetValueType::Error } else { RetValueType::ErrorNoQuota };
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(parent_container_ptr), Some(parent_process_ptr), Some(current_thread_ptr), None, None, None);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, endpoint_index,
                error);
            new_container_result_from_k(&old(steps).snapshot_k(), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, endpoint_index, error);
        }
        return Err(error);
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    Ok(NewContainerOwnersLocked {
        parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr, parent_cpu_set, source_range, endpoint: endpoint_option,
        cpu_lock_perm: Tracked(cpu_lock_perm), container_lock_perm: Tracked(container_lock_perm), process_lock_perm: Tracked(process_lock_perm),
        thread_lock_perm: Tracked(thread_lock_perm),
    })
}
} // verus!
