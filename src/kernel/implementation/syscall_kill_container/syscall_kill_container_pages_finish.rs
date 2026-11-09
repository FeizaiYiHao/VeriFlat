use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::KillTraceCtx;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_alloc_page::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
use super::syscall_kill_container_pages_lock::kill_container_pages_unlock;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_trace::kill_container_trace_push;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_trace::kill_container_retire_pre_from_k;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_eof::kill_container_pages_eof_retire_ready;

verus! {
/// With the 4K and 2M caches and the 4K, 2M, and 1G global pools of the marked container `ctn_ptr` drained, mark it ready to retire,
/// record the step that starts retiring it, and release the allocator locks `kill_container_pages_allocator_locks` names.
pub(crate) fn kill_container_pages_retire_and_unlock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, a4: RwLockPageAllocatorPtr, o4: RwLockPageAllocatorPtr,
    a2: RwLockPageAllocatorPtr, o2: RwLockPageAllocatorPtr, a1: RwLockPageAllocatorPtr, o1: RwLockPageAllocatorPtr, Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>,
    Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>,
    Tracked(caches_4k): Tracked<Map<CpuId, LockPerm>>, Tracked(caches_2m): Tracked<Map<CpuId, LockPerm>>, Tracked(pools_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(pools_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(quotas_4k): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_2m): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Tracked(pools_1g): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>,
    Tracked(quotas_1g): Tracked<Map<RwLockPageAllocatorPtr, LockPerm>>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        ctx is Container,
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        kill_container_pages_allocator_locks(*old(krnl), *old(lctx), ctn_ptr, owner_ptr, a4, o4, a2, o2, a1, o1, caches_4k, caches_2m, pools_4k, pools_2m, quotas_4k, quotas_2m,
            pools_1g, quotas_1g),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_container_progress(ctn_ptr, ContainerKillStage::Pages),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view().exited.view(),
        old(krnl).ctn_mp.spec_index(ctn_ptr).view().children.view().len() == 0,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        old(krnl).allc_4k_mp.spec_index(a4).global_pool.view().view().len() == 0,
        old(krnl).allc_2m_mp.spec_index(a2).global_pool.view().view().len() == 0,
        old(krnl).allc_1g_mp.spec_index(a1).global_pool.view().view().len() == 0,
        forall|i: CpuId| #![trigger old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> old(krnl).allc_4k_mp.spec_index(a4).cpu_caches.spec_index(i).view().view().view().len() == 0,
        forall|i: CpuId| #![trigger old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i)] index_valid(NUM_CPUS, i)
            ==> old(krnl).allc_2m_mp.spec_index(a2).cpu_caches.spec_index(i).view().view().view().len() == 0,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_container_pages_killer_state(*final(krnl), *final(lctx), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        killer_held_context(*final(krnl), *final(lctx), prc_ptr, thrd_ptr, final(lctx).container_lock_map().dom()),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view()
            == (Thread { syscall_progress: Ghost(kill_container_progress(ctn_ptr, ContainerKillStage::Retire)), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view().uppertree_seq
            &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), c, TypedLockMode::Write) ==> final(krnl).ctn_mp.spec_index(c).view().root_process_removed.view() == old(krnl).ctn_mp.spec_index(c).view().root_process_removed.view()
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(krnl).ctn_mp.spec_index(ctn_ptr).view().retire_ready.view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().control() == old(krnl).cpu_arr.spec_index(cpu_id).view().control(),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        ({
            &&& final(krnl).prc_mp.spec_index(prc_ptr).view() == old(krnl).prc_mp.spec_index(prc_ptr).view()
            &&& final(krnl).prc_mp.spec_index(prc_ptr).view_rodata() == old(krnl).prc_mp.spec_index(prc_ptr).view_rodata()
            &&& final(krnl).prc_mp.spec_index(prc_ptr).locking_thread() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread()
            &&& final(krnl).prc_mp.spec_index(prc_ptr).control() == old(krnl).prc_mp.spec_index(prc_ptr).control()
        }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s)
            ==> final(krnl).cpu_set_mp.dom().contains(s) && final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
{
    proof {
        let a4_caches = krnl.allc_4k_mp.spec_index(a4).cpu_caches;
        let a2_caches = krnl.allc_2m_mp.spec_index(a2).cpu_caches;
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, a4); allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, a2);
        a4_caches.view_index_eq_element_value(); lemma_cache_len_fold_all_zero(a4_caches.view()); a2_caches.view_index_eq_element_value(); lemma_cache_len_fold_all_zero(a2_caches.view());
        lemma_container_allocator_quota_eq_total_free_without_users(*krnl, ctn_ptr); krnl.thrd_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thrd_ptr);
    }
    let ghost drained = *krnl;
    proof {
        kernel_container_quotas_zero_projection(&drained, ctn_ptr); container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, ctn_ptr);
    }
    {
        let container = krnl.ctn_mp.borrow_mut_typed(ctn_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(container_perm));
        container.retire_ready = Ghost(true);
    }
    proof {
        kill_container_pages_eof_retire_ready(drained, *krnl, ctn_ptr);
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        kernel_endpoint_nonlock_fields_unchanged_for_equal(drained.ep_mp, krnl.ep_mp);
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&drained, &*krnl); steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    let ghost base = *krnl;
    let ghost base_lctx = *lctx;
    let ghost base_steps = steps.view();
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(kill_container_progress(ctn_ptr, ContainerKillStage::Retire)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(base);
        let post_u = kernel_k_to_kernel_u(*krnl);
        kill_container_pages_pre_from_k(&base, &base_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&base, &*krnl, thrd_ptr);
        kill_container_retire_stage_step_from_u(pre_u, post_u, cpu_id, thrd_ptr, ctn_ptr);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        kill_container_trace_push(&*steps, base_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
    let ghost retired = *krnl;
    kill_container_pages_unlock(krnl, Tracked(&mut *lctx), ctn_ptr, owner_ptr, a4, o4, a2, o2, a1, o1, Tracked(caches_4k), Tracked(caches_2m), Tracked(pools_4k),
        Tracked(pools_2m), Tracked(quotas_4k), Tracked(quotas_2m), Tracked(pools_1g), Tracked(quotas_1g));
    proof {
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&retired, &*krnl);
        assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); };
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        container_perms_wf_at(krnl.ctn_mp, ctn_ptr); container_root_removed_implies_no_owned_processes(*krnl, ctn_ptr);
        assert(krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_threads.view().is_empty() && krnl.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_indirect_threads.view().is_empty()) by { container_without_children_and_processes_owns_no_threads(*krnl, ctn_ptr); };
        kill_container_retire_pre_from_k(&*krnl, &*lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr);
    }
}
} // verus!
