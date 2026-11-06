use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
use super::syscall_kill_container_retire_commit::kill_container_retire_commit;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::kill_container_progress;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_spec::*;

verus! {
/// With every lock `kill_container_retire_held_locks` names write-held for the marked childless container
/// `ctn_ptr`, a child of the write-held `parent_ptr`, retire it into the killer's container `owner_ptr`, release
/// those locks and its marked cpu set `cpu_set_ptr`, and record the step that walks the parent again.
pub(crate) fn kill_container_retire_commit_and_record(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, cpu_set_ptr: RwLockCpuSetPtr,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<LockPerm>, Tracked(parent_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>,
    Tracked(cpu_set_perm): Tracked<LockPerm>, Tracked(flag_perms): Tracked<Map<CpuId, LockPerm>>, Tracked(pcid_perm): Tracked<LockPerm>,
    Tracked(shard_perms): Tracked<Map<CpuId, LockPerm>>, Tracked(caches_4k): Tracked<Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<Map<CpuId, LockPerm>>,
    Tracked(caches_1g): Tracked<Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pool_1g): Tracked<LockPerm>, Tracked(quotas_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quota_1g): Tracked<LockPerm>, Tracked(page_perms): Tracked<Map<PageIndex, LockPerm>>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        kill_container_retire_held_locks(*old(krnl), *old(lctx), ctn_ptr, owner_ptr, cpu_set_perm, flag_perms, pcid_perm, shard_perms, caches_4k, caches_2m, caches_1g, pools_4k,
            pools_2m, pool_1g, quotas_4k, quotas_2m, quota_1g, page_perms),
        ({
            let target = old(krnl).ctn_mp.spec_index(ctn_ptr);
            let ro = target.view_rodata().view();
            &&& owner_ptr != ctn_ptr
            &&& target.being_killed()
            &&& target.view_ghost().retire_ready
            &&& ro.parent == Some(parent_ptr)
            &&& ro.cpu_set == cpu_set_ptr
            &&& target.view_ghost().uppertree_seq.view().contains(owner_ptr)
            &&& target.view().children.view().len() == 0
            &&& target.view_ghost().owned_processes.view() == Set::<RwLockProcessPtr>::empty()
            &&& old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < ro.depth
            &&& old(krnl).cpu_set_mp.spec_index(ro.cpu_set).being_killed()
            &&& old(krnl).cpu_set_mp.spec_index(ro.cpu_set).view().owned_cpus.view().is_empty()
            &&& forall|i: CpuId| #![trigger old(krnl).sched_mp.spec_index(ro.scheduler).shards.spec_index(i)]
                index_valid(NUM_CPUS, i) ==> old(krnl).sched_mp.spec_index(ro.scheduler).shards.spec_index(i).view().view().queue.view().len() == 0
        }),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), ctn_ptr, TypedLockMode::Write),
        container_perm.state() is WriteLock && container_perm.thread_id() == old(lctx).thread_id(),
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(ctn_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(parent_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_perm.state() is WriteLock && parent_perm.thread_id() == old(lctx).thread_id(),
        parent_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        owner_perm.state() is WriteLock && owner_perm.thread_id() == old(lctx).thread_id(),
        owner_perm.lock_id() == old(krnl).ctn_mp.spec_index(owner_ptr).locking_thread()->Write_lock_id,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c)
            ==> old(krnl).ctn_mp.dom().contains(c) && (c != owner_ptr ==> old(krnl).ctn_mp.spec_index(c).being_killed()),
        old(lctx).cpu_id() == cpu_id && index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id] && typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        ({
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& cpu.state is Running
            &&& cpu.current_process == Some(prc_ptr)
            &&& cpu.current_thread == Some(thrd_ptr)
            &&& cpu.owning_container == owner_ptr
        }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        old(krnl).prc_mp.dom().contains(prc_ptr) && old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(lctx).process_lock_map().dom() =~= set![prc_ptr] && typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        old(lctx).thread_lock_map().dom() =~= set![thrd_ptr] && typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.state() is WriteLock && thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        !(old(krnl).thrd_mp.spec_index(thrd_ptr).view().state is SCHEDULED),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_container_progress(ctn_ptr, ContainerKillStage::Retire),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(lctx).cpu_set_lock_map().dom() =~= set![cpu_set_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty() && old(lctx).pcid_needflush_lock_map().dom().is_empty() && old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty() && old(lctx).pagetable_window_lock_map().dom().is_empty() && old(lctx).iommu_table_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*final(krnl), *final(lctx), prc_ptr, thrd_ptr, final(lctx).container_lock_map().dom()),
        final(lctx).thread_lock_map().dom() =~= set![thrd_ptr],
        final(lctx).process_lock_map().dom() =~= set![prc_ptr],
        final(lctx).container_lock_map() == old(lctx).container_lock_map().remove(ctn_ptr),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_container_progress(parent_ptr, ContainerKillStage::Walk),
        !final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && c != ctn_ptr ==> {
            let old_c = old(krnl).ctn_mp.spec_index(c);
            let new_c = final(krnl).ctn_mp.spec_index(c);
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& new_c.locking_thread() == old_c.locking_thread()
            &&& new_c.killer_info() == old_c.killer_info()
            &&& new_c.view_rodata() == old_c.view_rodata()
            &&& new_c.view_ghost().uppertree_seq == old_c.view_ghost().uppertree_seq
            &&& new_c.view_ghost().owned_processes == old_c.view_ghost().owned_processes
            &&& new_c.view_ghost().subtree_set.view() == if old(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().contains(c) {
                old_c.view_ghost().subtree_set.view().remove(ctn_ptr)
            } else { old_c.view_ghost().subtree_set.view() }
        },
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] old(lctx).container_lock_map().dom().contains(c) && c != ctn_ptr
            ==> final(krnl).ctn_mp.dom().contains(c) && final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
{
    let ghost base = *krnl;
    let ghost base_lctx = *lctx;
    let ghost base_steps = steps.view();
    kill_container_retire_commit(krnl, Tracked(&mut *lctx), ctn_ptr, parent_ptr, owner_ptr, Tracked(container_perm), Tracked(parent_perm), Tracked(owner_perm),
        Tracked(cpu_set_perm), Tracked(flag_perms), Tracked(pcid_perm), Tracked(shard_perms), Tracked(caches_4k), Tracked(caches_2m), Tracked(caches_1g), Tracked(pools_4k),
        Tracked(pools_2m), Tracked(pool_1g), Tracked(quotas_4k), Tracked(quotas_2m), Tracked(quota_1g), Tracked(page_perms));
    let ghost retired_k = *krnl;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(kill_container_progress(parent_ptr, ContainerKillStage::Walk)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(base);
        let post_u = kernel_k_to_kernel_u(*krnl);
        let owner_ro = base.ctn_mp.spec_index(owner_ptr).view_rodata().view();
        kill_container_retire_pre_from_k(&base, &base_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr);
        kernel_container_retired_implies_u_step(&base, &retired_k, ctn_ptr, parent_ptr, owner_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&retired_k, &*krnl, thrd_ptr);
        kill_container_retire_step_from_u(pre_u, kernel_k_to_kernel_u(retired_k), post_u, cpu_id, thrd_ptr, ctn_ptr, parent_ptr, owner_ptr,
            retired_k.allc_4k_mp.spec_index(owner_ro.allocator_ptr_4k).quota.view().view(), retired_k.allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m).quota.view().view());
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        kill_container_trace_push(&*steps, base_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
}
} // verus!
