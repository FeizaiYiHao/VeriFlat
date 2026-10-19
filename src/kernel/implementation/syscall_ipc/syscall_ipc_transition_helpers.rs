use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_ipc_transition_spec::ipc_block_current_eof_transition_framing;

verus! {
/// Releases the default-pcid needflush, endpoint, current-thread, and cpu locks after the blocking transition
/// `locked_k` → `*old(krnl)` summarized by `ipc_block_current_eof_transition_framing`, where `locked_k` is `entry_k` with the
/// needflush entry write-locked, and records the block step and the ordinary syscall trace from `steps.snapshot_k()`.
pub(super) fn ipc_block_current_release_and_end_step(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad,
    pt_regs: &Registers, Ghost(default_cr3): Ghost<PageTableRoot>, Ghost(entry_k): Ghost<KernelK>, Ghost(locked_k): Ghost<KernelK>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    Tracked(needflush_perm): Tracked<LockPerm>,
)
    requires
        entry_k == (KernelK { cpu_arr: entry_k.cpu_arr, thr_mp: entry_k.thr_mp, ep_mp: entry_k.ep_mp, ..old(steps).snapshot_k() }),
        entry_k.cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        entry_k.thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
        entry_k.ep_mp.unchanged_except(&old(steps).snapshot_k().ep_mp, endpoint_ptr),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread() is None,
        old(steps).snapshot_k().ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &entry_k),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, entry_k.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &entry_k),
        entry_k.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        entry_k.prc_mp.dom().contains(entry_k.thr_mp.spec_index(current_thread_ptr).view().owning_proc),
        entry_k.ctn_mp.dom().contains(entry_k.thr_mp.spec_index(current_thread_ptr).view().owning_container),
        entry_k.thr_mp.dom().contains(current_thread_ptr),
        entry_k.thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        entry_k.ep_mp.dom().contains(endpoint_ptr),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(entry_k.thr_mp.spec_index(current_thread_ptr).view().owning_proc),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        entry_k.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        entry_k.thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        entry_k.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        !entry_k.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(current_thread_ptr),
        entry_k.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == entry_k.ep_mp.spec_index(endpoint_ptr).view().queue.length,
        entry_k.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || match entry_k.ep_mp.spec_index(endpoint_ptr).view().queue_state {
                EndpointState::SEND => waiting_state.is_endpoint_send_waiting(),
                EndpointState::RECEIVE => waiting_state.is_endpoint_receive_waiting(),
            },
        locked_k == (KernelK { pcid_needflush: locked_k.pcid_needflush, ..entry_k }),
        forall|c: CpuId, p: Pcid| #![trigger locked_k.pcid_needflush.spec_index(c, p)] #![trigger entry_k.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) ==> {
            &&& locked_k.pcid_needflush.spec_index(c, p).view() == entry_k.pcid_needflush.spec_index(c, p).view()
            &&& ((c != cpu_id || p != KERNEL_DEFAULT_PCID) ==> locked_k.pcid_needflush.spec_index(c, p) == entry_k.pcid_needflush.spec_index(c, p))
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(&entry_k, &locked_k),
        kernel_endpoint_nonlock_fields_unchanged(entry_k.ep_mp, locked_k.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&entry_k, &locked_k),
        ipc_block_current_eof_transition_framing(locked_k, *old(krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, default_cr3),
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        edp_idx_valid(endpoint_index),
        waiting_state.is_endpoint_waiting(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == KERNEL_DEFAULT_PCID,
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == waiting_state,
        *old(krnl).thr_mp.spec_index(current_thread_ptr).view().trap_frame.get_some_0() == *pt_regs,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.state() is WriteLock,
        endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, KERNEL_DEFAULT_PCID), TypedLockMode::Write),
        needflush_perm.state() is WriteLock,
        needflush_perm.thread_id() == old(lctx).thread_id(),
        needflush_perm.lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, KERNEL_DEFAULT_PCID)],
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        ipc_block_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state),
        ipc_block_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id,
            endpoint_index, waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(entry_k, cpu_id)),
        ipc_ordinary_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(entry_k, cpu_id), RetValueType::CpuIdle),
        final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
        final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        ipc_block_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state),
        ipc_block_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, endpoint_index, waiting_state, payload, *pt_regs, ipc_block_flushes_default_pcid(entry_k, cpu_id)),
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    krnl.wunlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx), Tracked(needflush_perm));
    krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost flushed = ipc_block_flushes_default_pcid(entry_k, cpu_id);
        assert(kernel_ipc_block_fields(&steps.snapshot_k(), &*krnl, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, *pt_regs, flushed)) by {
            reveal(kernel_ipc_block_fields); reveal(ipc_block_current_eof_transition_framing);
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
            reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
        };
        steps.end_kernel_step_ipc_block(&*krnl, &*lctx, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, *pt_regs, flushed);
        assert({
            &&& ipc_block_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index, waiting_state)
            &&& ipc_block_step_pre(steps.nonlock_view().last().old_u, cpu_id, endpoint_index, waiting_state)
            &&& ipc_ordinary_syscall_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state,
                payload, *pt_regs, flushed, RetValueType::CpuIdle)
        }) by {
            ipc_block_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, *pt_regs, flushed);
            ipc_block_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, current_thread_ptr, endpoint_ptr, endpoint_index, waiting_state, payload, *pt_regs, flushed);
            assert(!old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.being_killed()) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            };
            ipc_ordinary_trace_block_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, endpoint_index, waiting_state, payload, *pt_regs, flushed);
        };
    }
}
}
