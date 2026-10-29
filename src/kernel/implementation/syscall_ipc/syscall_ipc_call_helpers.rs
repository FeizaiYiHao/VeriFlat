use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_call_spec::*;
use super::syscall_ipc_call_trace::*;

verus! {
/// Releases the caller-pcid needflush, caller, callee, endpoint, and cpu locks after the reply handoff `locked_k` → `*old(krnl)`
/// summarized by `ipc_reply_handoff_eof_transition_framing`, where `locked_k` is `entry_k` with that needflush entry write-locked,
/// and records the reply-handoff step from `steps.snapshot_k()`.
pub(super) fn ipc_reply_handoff_release_and_end_step(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pcid: Pcid,
    callee_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, caller_ptr: RwLockThreadPtr, pt_regs: &Registers,
    Ghost(entry_regs): Ghost<Registers>, Ghost(entry_k): Ghost<KernelK>, Ghost(entry_lctx): Ghost<LocalContext>, Ghost(locked_k): Ghost<KernelK>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(callee_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
    Tracked(caller_lock_perm): Tracked<LockPerm>, Tracked(needflush_perm): Tracked<LockPerm>,
)
    requires
        entry_k == (KernelK { cpu_arr: entry_k.cpu_arr, cpu_op: entry_k.cpu_op, thr_mp: entry_k.thr_mp, ep_mp: entry_k.ep_mp, ..old(steps).snapshot_k() }),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view().view().view(),
        forall|p: RwLockContainerPtr| #![trigger entry_k.ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
            old(steps).snapshot_k().ctn_mp.dom().contains(p) && entry_k.ctn_mp.dom().contains(p) ==> if entry_lctx.container_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
            } else { entry_k.ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger entry_k.prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) && entry_k.prc_mp.dom().contains(p) ==> if entry_lctx.process_lock_map().dom().contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { entry_k.prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger entry_k.thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
            old(steps).snapshot_k().thr_mp.dom().contains(p) && entry_k.thr_mp.dom().contains(p) ==> if entry_lctx.thread_lock_map().dom().contains(p) {
                old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
            } else { entry_k.thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger entry_k.ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
            old(steps).snapshot_k().ep_mp.dom().contains(p) && entry_k.ep_mp.dom().contains(p) ==> if entry_lctx.endpoint_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
            } else { entry_k.ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger entry_k.pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && entry_k.pt_mp.dom().contains(p) ==> if entry_lctx.pagetable_lock_map().dom().contains(p) {
                old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
            } else { entry_k.pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger entry_k.it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
            old(steps).snapshot_k().it_mp.dom().contains(p) && entry_k.it_mp.dom().contains(p) ==> if entry_lctx.iommu_table_lock_map().dom().contains(p) {
                old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
            } else { entry_k.it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger entry_k.cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if entry_lctx.cpu_lock_map().dom().contains(i) {
                old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
            } else { entry_k.cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), &entry_k),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, entry_k.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), &entry_k),
        entry_lctx.cpu_lock_map().dom() =~= set![cpu_id],
        entry_lctx.container_lock_map().dom().is_empty(),
        entry_lctx.process_lock_map().dom().is_empty(),
        entry_lctx.thread_lock_map().dom() =~= set![callee_ptr, caller_ptr],
        entry_lctx.endpoint_lock_map().dom() =~= set![endpoint_ptr],
        entry_lctx.pagetable_lock_map().dom().is_empty(),
        entry_lctx.pagetable_window_lock_map().dom().is_empty(),
        entry_lctx.iommu_table_lock_map().dom().is_empty(),
        entry_k.cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(entry_k.thr_mp.spec_index(callee_ptr).view().owning_proc),
        entry_k.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(callee_ptr),
        entry_k.prc_mp.dom().contains(entry_k.thr_mp.spec_index(callee_ptr).view().owning_proc),
        entry_k.ctn_mp.dom().contains(entry_k.thr_mp.spec_index(callee_ptr).view().owning_container),
        entry_k.thr_mp.dom().contains(callee_ptr),
        entry_k.thr_mp.spec_index(callee_ptr).being_killed() == false,
        entry_k.thr_mp.spec_index(callee_ptr).view().syscall_progress.view() is None,
        entry_k.thr_mp.spec_index(callee_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        entry_k.thr_mp.spec_index(callee_ptr).view().caller == Some(caller_ptr),
        entry_k.thr_mp.spec_index(callee_ptr).view().callee is None,
        entry_k.thr_mp.spec_index(callee_ptr).view().endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        entry_k.ep_mp.dom().contains(endpoint_ptr),
        !entry_k.ep_mp.spec_index(endpoint_ptr).view().queue.view().contains(callee_ptr),
        entry_k.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == entry_k.ep_mp.spec_index(endpoint_ptr).view().queue.length,
        entry_k.ep_mp.spec_index(endpoint_ptr).view().queue.view().len() == 0 || entry_k.ep_mp.spec_index(endpoint_ptr).view().queue_state is RECEIVE,
        caller_ptr != callee_ptr,
        entry_k.thr_mp.dom().contains(caller_ptr),
        entry_k.thr_mp.spec_index(caller_ptr).being_killed() == false,
        entry_k.thr_mp.spec_index(caller_ptr).view().state is WAITING_REPLY,
        entry_k.thr_mp.spec_index(caller_ptr).view().callee == Some(callee_ptr),
        entry_k.thr_mp.spec_index(caller_ptr).view().owning_container == entry_k.thr_mp.spec_index(callee_ptr).view().owning_container,
        entry_k.prc_mp.dom().contains(entry_k.thr_mp.spec_index(caller_ptr).view().owning_proc),
        pcid == entry_k.prc_mp.spec_index(entry_k.thr_mp.spec_index(caller_ptr).view().owning_proc).view_rodata().view().pcid,
        pcid_valid(pcid),
        locked_k == (KernelK { pcid_needflush: locked_k.pcid_needflush, ..entry_k }),
        forall|c: CpuId, p: Pcid| #![trigger locked_k.pcid_needflush.spec_index(c, p)] #![trigger entry_k.pcid_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) ==> {
            &&& locked_k.pcid_needflush.spec_index(c, p).view() == entry_k.pcid_needflush.spec_index(c, p).view()
            &&& ((c != cpu_id || p != pcid) ==> locked_k.pcid_needflush.spec_index(c, p) == entry_k.pcid_needflush.spec_index(c, p))
        },
        kernel_cpu_process_thread_nonlock_fields_unchanged(&entry_k, &locked_k),
        kernel_endpoint_nonlock_fields_unchanged(entry_k.ep_mp, locked_k.ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&entry_k, &locked_k),
        ipc_reply_handoff_eof_transition_framing(locked_k, *old(krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs),
        kernel_container_nonlock_fields_and_quotas_unchanged(&locked_k, old(krnl)),
        *pt_regs == *entry_k.thr_mp.spec_index(caller_ptr).view().trap_frame.get_some_0(),
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        entry_k.cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] is Trap,
        edp_idx_valid(endpoint_index),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thr_mp.dom().contains(callee_ptr),
        old(krnl).thr_mp.spec_index(callee_ptr).being_killed() == false,
        !old(krnl).thr_mp.spec_index(callee_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(callee_ptr).view().state is RECEIVING_CALL,
        old(krnl).thr_mp.spec_index(callee_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(callee_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(callee_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.dom().contains(caller_ptr),
        old(krnl).thr_mp.spec_index(caller_ptr).being_killed() == false,
        !old(krnl).thr_mp.spec_index(caller_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(caller_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(caller_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(caller_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(caller_ptr).view().syscall_progress.view() is None,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), callee_ptr, TypedLockMode::Write),
        callee_lock_perm.state() is WriteLock,
        callee_lock_perm.thread_id() == old(lctx).thread_id(),
        callee_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(callee_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), caller_ptr, TypedLockMode::Write),
        caller_lock_perm.state() is WriteLock,
        caller_lock_perm.thread_id() == old(lctx).thread_id(),
        caller_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(caller_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.state() is WriteLock,
        endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).pcid_needflush_lock_map(), (cpu_id, pcid), TypedLockMode::Write),
        needflush_perm.state() is WriteLock,
        needflush_perm.thread_id() == old(lctx).thread_id(),
        needflush_perm.lock_id() == old(krnl).pcid_needflush.spec_index(cpu_id, pcid).locking_thread()->Write_lock_id,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![callee_ptr, caller_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
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
        old(lctx).pcid_needflush_lock_map().dom() =~= set![(cpu_id, pcid)],
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        ipc_reply_handoff_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, endpoint_index),
        ipc_reply_handoff_step(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, entry_regs, ipc_handoff_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr)),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().last().old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k()),
        final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        ipc_reply_handoff_step_pre(final(steps).nonlock_view().last().old_u, cpu_id, endpoint_index),
        ipc_reply_handoff_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, endpoint_index, entry_regs, ipc_handoff_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        *pt_regs == *old(steps).snapshot_k().thr_mp.spec_index(caller_ptr).view().trap_frame.get_some_0(),
{
    krnl.wunlock_pcid_needflush(cpu_id, pcid, Tracked(&mut *lctx), Tracked(needflush_perm));
    krnl.wunlock_thread(caller_ptr, Tracked(&mut *lctx), Tracked(caller_lock_perm));
    krnl.wunlock_thread(callee_ptr, Tracked(&mut *lctx), Tracked(callee_lock_perm));
    krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
    assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { reveal(ipc_reply_handoff_eof_transition_framing); };
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(krnl.cpu_op.view().view() =~= steps.snapshot_k().cpu_op.view().view()) by { reveal(ipc_reply_handoff_eof_transition_framing); };
        let ghost flushed_pcid = ipc_handoff_flushed_pcid(old(steps).snapshot_k(), cpu_id, caller_ptr);
        assert(kernel_ipc_reply_handoff_fields(&steps.snapshot_k(), &*krnl, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs, flushed_pcid) && krnl.ctn_mp == steps.snapshot_k().ctn_mp) by {
            broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive;
            reveal(kernel_ipc_reply_handoff_fields); reveal(ipc_reply_handoff_eof_transition_framing);
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged);
            reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
        };
        steps.end_kernel_step_ipc_reply_handoff(&*krnl, &*lctx, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs, flushed_pcid);
        ipc_reply_handoff_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs, flushed_pcid);
        ipc_reply_handoff_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, callee_ptr, endpoint_ptr, endpoint_index, caller_ptr, entry_regs, flushed_pcid);
        assert(*pt_regs == *old(steps).snapshot_k().thr_mp.spec_index(caller_ptr).view().trap_frame.get_some_0()) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged); };
    }
}
}
