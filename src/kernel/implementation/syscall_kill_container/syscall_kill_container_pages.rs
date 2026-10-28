use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::KillTraceCtx;
#[cfg(all(verus_keep_ghost, feature = "split-crates"))]
use veriflat_alloc_page::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
#[cfg(all(verus_keep_ghost, not(feature = "split-crates")))]
use crate::kernel::implementation::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
use super::syscall_kill_container_pages_lock::{kill_container_pages_lock, kill_container_pages_unlock};
use super::syscall_kill_container_pages_drain::kill_container_pages_drain;
use super::syscall_kill_container_pages_move::{kill_container_pages_move_4k, kill_container_pages_move_2m};
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
use super::syscall_kill_container_pages_eof::kill_container_pages_eof_retire_ready;

verus! {
/// Move every free page of the marked container `container_ptr` to the killer's container `owner_ptr`: write-hold the
/// marked container's 4K and 2M allocator caches and both containers' 4K and 2M global pools and quotas, drain the caches
/// into the marked container's pools, move each pooled page with one page of quota in its own step, and start retiring
/// the container, which then holds no quota; the marked container's 1G allocator holds no page.
pub(crate) fn kill_container_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, Tracked(cpu_perm): Tracked<&LockPerm>,
    Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>,
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
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm, *owner_perm),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Pages),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).ctn_mp.spec_index(container_ptr).view().children.view().len() == 0,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        kill_container_pages_killer_state(*final(krnl), *final(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm,
            *owner_perm),
        killer_held_context(*final(krnl), *final(lctx), process_ptr, thread_ptr, final(lctx).container_lock_map().dom()),
        final(krnl).thr_mp.spec_index(thread_ptr).view()
            == (Thread { syscall_progress: Ghost(kill_container_progress(container_ptr, ContainerKillStage::Retire)), ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().retire_ready,
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        forall|s: RwLockCpuSetPtr| #![trigger old(lctx).cpu_set_lock_map().dom().contains(s)] old(lctx).cpu_set_lock_map().dom().contains(s)
            ==> final(krnl).cpu_set_mp.dom().contains(s) && final(krnl).cpu_set_mp.spec_index(s) == old(krnl).cpu_set_mp.spec_index(s),
{
    let tracked mut caches_4k = Map::<CpuId, LockPerm>::tracked_empty();
    let tracked mut caches_2m = Map::<CpuId, LockPerm>::tracked_empty();
    let tracked mut pools_4k = Map::<RwLockPageAllocatorPtr, LockPerm>::tracked_empty();
    let tracked mut pools_2m = Map::<RwLockPageAllocatorPtr, LockPerm>::tracked_empty();
    let tracked mut quotas_4k = Map::<RwLockPageAllocatorPtr, LockPerm>::tracked_empty();
    let tracked mut quotas_2m = Map::<RwLockPageAllocatorPtr, LockPerm>::tracked_empty();
    let (a4, o4, a2, o2) = kill_container_pages_lock(krnl, Tracked(&mut *lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, Tracked(cpu_perm), Tracked(process_perm),
        Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&mut caches_4k), Tracked(&mut caches_2m), Tracked(&mut pools_4k), Tracked(&mut pools_2m),
        Tracked(&mut quotas_4k), Tracked(&mut quotas_2m));
    proof {
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
        steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    kill_container_pages_drain(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&caches_4k), Tracked(&caches_2m), Tracked(&pools_4k), Tracked(&pools_2m),
        Tracked(&quotas_4k), Tracked(&quotas_2m));
    kill_container_pages_move_4k(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&caches_4k), Tracked(&caches_2m), Tracked(&pools_4k), Tracked(&pools_2m),
        Tracked(&quotas_4k), Tracked(&quotas_2m), Ghost(start), Ghost(pre), Ghost(ctx));
    kill_container_pages_move_2m(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&caches_4k), Tracked(&caches_2m), Tracked(&pools_4k), Tracked(&pools_2m),
        Tracked(&quotas_4k), Tracked(&quotas_2m), Ghost(start), Ghost(pre), Ghost(ctx));
    proof {
        let a4_caches = krnl.allc_4k_mp.spec_index(a4).cpu_caches;
        let a2_caches = krnl.allc_2m_mp.spec_index(a2).cpu_caches;
        allocator_perms_wf_map(krnl.allc_4k_mp); allocator_perms_wf_at(krnl.allc_4k_mp, a4); allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, a2);
        a4_caches.lemma_view_index(); lemma_cache_len_fold_all_zero(a4_caches.view()); a2_caches.lemma_view_index(); lemma_cache_len_fold_all_zero(a2_caches.view());
        lemma_container_allocator_quota_eq_total_free_without_users(*krnl, container_ptr); krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    }
    let ghost drained = *krnl;
    proof {
        let target_ghost = krnl.ctn_mp.spec_index(container_ptr).view_ghost();
        kernel_container_quotas_zero_projection(&drained, container_ptr); container_perms_wf_map(krnl.ctn_mp);
        krnl.ctn_mp.update_ghost(container_ptr, ContainerGhost { retire_ready: true, ..target_ghost });
        kill_container_pages_eof_retire_ready(drained, *krnl, container_ptr);
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&drained, &*krnl)) by { broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&drained, &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        kernel_endpoint_nonlock_fields_unchanged_for_equal(drained.ep_mp, krnl.ep_mp);
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&drained, &*krnl); steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    let ghost base = *krnl;
    let ghost base_lctx = *lctx;
    let ghost base_steps = steps.view();
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_container_progress(container_ptr, ContainerKillStage::Retire)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(base);
        let post_u = kernel_k_to_kernel_u(*krnl);
        kill_container_pages_pre_from_k(&base, &base_lctx, cpu_id, process_ptr, thread_ptr, container_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&base, &*krnl, thread_ptr);
        kill_container_retire_stage_step_from_u(pre_u, post_u, cpu_id, thread_ptr, container_ptr);
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_container_trace_push(&*steps, base_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
    let ghost retired = *krnl;
    kill_container_pages_unlock(krnl, Tracked(&mut *lctx), container_ptr, owner_ptr, a4, o4, a2, o2, Tracked(caches_4k), Tracked(caches_2m), Tracked(pools_4k), Tracked(pools_2m),
        Tracked(quotas_4k), Tracked(quotas_2m));
    proof {
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&retired, &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
}
} // verus!
