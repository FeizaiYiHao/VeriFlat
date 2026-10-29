use vstd::prelude::*;
use crate::*;
use super::rebalance_pull_spec::*;
use super::rebalance_pull_trace::*;
use super::rebalance_pull::rebalance_unlock_shard_prefix;

verus! {
/// With `cpu_id`, shards `0..count` of `scheduler_ptr`, and shard `cpu_id` when `local_lock_perm` is present write-held
/// since the entry snapshot and nothing moved: releases them all and finishes the call without recording a step.
pub(super) fn rebalance_pull_release_unpulled(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, scheduler_ptr: RwLockSchedulerPtr,
    count: usize, Tracked(shard_perms): Tracked<Map<CpuId, LockPerm>>, local_lock_perm: Option<Tracked<LockPerm>>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_op: old(krnl).cpu_op, thr_mp: old(krnl).thr_mp, sched_mp: old(krnl).sched_mp, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.entries_unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        old(krnl).cpu_op.view().view() == old(steps).snapshot_k().cpu_op.view().view().update(cpu_id as int, CpuOpState::InStep),
        old(steps).snapshot_k().cpu_op.view().view()[cpu_id as int] == cpu_op_after_step(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state),
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(t)] old(steps).snapshot_k().thr_mp.dom().contains(t) ==> old(krnl).thr_mp.spec_index(t) == old(steps).snapshot_k().thr_mp.spec_index(t),
        old(krnl).sched_mp.unchanged_except(&old(steps).snapshot_k().sched_mp, scheduler_ptr),
        scheduler_shards_of(old(krnl).sched_mp.spec_index(scheduler_ptr)) == scheduler_shards_of(old(steps).snapshot_k().sched_mp.spec_index(scheduler_ptr)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|k: (RwLockSchedulerPtr, CpuId)| #![trigger old(lctx).scheduler_lock_map().dom().contains(k)] old(lctx).scheduler_lock_map().dom().contains(k) <==> (k.0 == scheduler_ptr && (k.1 < count || k.1 == cpu_id)),
        0 < count <= NUM_CPUS,
        local_lock_perm is None ==> cpu_id < count,
        local_lock_perm is Some ==> count <= cpu_id,
        forall|i: CpuId| #![trigger shard_perms.spec_index(i)] #![trigger shard_perms.dom().contains(i)] i < count ==> {
            &&& shard_perms.dom().contains(i)
            &&& shard_perms.spec_index(i).state() is WriteLock
            &&& shard_perms.spec_index(i).thread_id() == old(lctx).thread_id()
            &&& shard_perms.spec_index(i).lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(i).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, i), TypedLockMode::Write)
        },
        local_lock_perm is Some ==> {
            let perm = local_lock_perm.unwrap().view();
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write)
        },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        rebalance_pull_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, false),
{
    if let Some(local_perm) = local_lock_perm { krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), local_perm); }
    rebalance_unlock_shard_prefix(krnl, Tracked(&mut *lctx), scheduler_ptr, count, Tracked(shard_perms));
    proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
    proof { assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; }; }
    release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    proof {
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(old(steps).snapshot_k())) by {
            assert(krnl.cpu_op.view().view() =~= old(steps).snapshot_k().cpu_op.view().view());
            kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl);
        };
        rebalance_pull_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id);
    }
}
} // verus!
