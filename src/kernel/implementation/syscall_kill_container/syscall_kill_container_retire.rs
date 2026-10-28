use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
use super::syscall_kill_container_retire_lock::*;
use super::syscall_kill_container_retire_commit::kill_container_retire_commit;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::kill_container_progress;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_spec::kill_container_pages_killer_state;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof_entry::kill_container_retire_eof_object_pages;

verus! {
/// Retire the empty marked container `container_ptr`, a child of the write-held `parent_ptr`, into the killer's container
/// `owner_ptr`: write-hold its offline request cells, PCID allocator, object pages, scheduler shards, allocator caches,
/// pools, and quotas with the pools and quotas of `owner_ptr`'s allocators, and its object pages' tails, then remove it
/// with its objects, give its pages to `owner_ptr`, release its locks and its marked cpu set `cpu_set_ptr`, and walk the
/// parent again.
pub(crate) fn kill_container_retire(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, cpu_set_ptr: RwLockCpuSetPtr,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<LockPerm>,
    Tracked(parent_perm): Tracked<&LockPerm>, Tracked(owner_perm): Tracked<&LockPerm>, Tracked(cpu_set_perm): Tracked<LockPerm>,
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
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, container_perm,
            *owner_perm),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Retire),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_perm.state() is WriteLock && parent_perm.thread_id() == old(lctx).thread_id(),
        parent_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(lctx).cpu_set_lock_map().dom() =~= set![cpu_set_ptr],
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
        cpu_set_perm.state() is WriteLock && cpu_set_perm.thread_id() == old(lctx).thread_id(),
        cpu_set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread()->Write_lock_id,
        ({
            let target = old(krnl).ctn_mp.spec_index(container_ptr);
            let ro = target.view_rodata().view();
            &&& ro.cpu_set == cpu_set_ptr
            &&& ro.parent == Some(parent_ptr)
            &&& target.view_ghost().uppertree_seq.view().contains(owner_ptr)
            &&& target.view_ghost().retire_ready
            &&& old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.view().is_empty()
        }),
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
        killer_held_context(*final(krnl), *final(lctx), process_ptr, thread_ptr, final(lctx).container_lock_map().dom()),
        final(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        final(lctx).container_lock_map().dom() == old(lctx).container_lock_map().dom().remove(container_ptr),
        final(lctx).container_lock_map() == old(lctx).container_lock_map().remove(container_ptr),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(parent_ptr, ContainerKillStage::Walk),
        !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) && c != container_ptr ==> {
            let old_c = old(krnl).ctn_mp.spec_index(c);
            let new_c = final(krnl).ctn_mp.spec_index(c);
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& new_c.locking_thread() == old_c.locking_thread()
            &&& new_c.killer_info() == old_c.killer_info()
            &&& new_c.view_rodata() == old_c.view_rodata()
            &&& new_c.view_ghost().uppertree_seq == old_c.view_ghost().uppertree_seq
            &&& new_c.view_ghost().owned_processes == old_c.view_ghost().owned_processes
            &&& new_c.view_ghost().subtree_set.view() == if old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view().contains(c) {
                old_c.view_ghost().subtree_set.view().remove(container_ptr)
            } else { old_c.view_ghost().subtree_set.view() }
        },
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] old(lctx).container_lock_map().dom().contains(c) && c != container_ptr
            ==> final(krnl).ctn_mp.dom().contains(c) && final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    let ghost entry = *krnl;
    proof {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
        container_kill_retire_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
        kill_container_retire_eof_object_pages(*krnl, container_ptr, parent_ptr, owner_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
    }
    let tracked mut flag_perms: Map<CpuId, LockPerm> = Map::tracked_empty();
    let Tracked(pcid_perm) = kill_container_retire_lock_flags_pcid(krnl, Tracked(&mut *lctx), thread_ptr, container_ptr, Tracked(&mut flag_perms));
    let Tracked(page_perms) = kill_container_retire_lock_object_pages(krnl, Tracked(&mut *lctx), thread_ptr, container_ptr);
    let tracked mut shard_perms: Map<CpuId, LockPerm> = Map::tracked_empty();
    kill_container_retire_lock_shards(krnl, Tracked(&mut *lctx), thread_ptr, container_ptr, Tracked(&mut shard_perms));
    let tracked mut caches_4k: Map<CpuId, LockPerm> = Map::tracked_empty();
    let tracked mut caches_2m: Map<CpuId, LockPerm> = Map::tracked_empty();
    let tracked mut caches_1g: Map<CpuId, LockPerm> = Map::tracked_empty();
    kill_container_retire_lock_caches(krnl, Tracked(&mut *lctx), thread_ptr, container_ptr, Tracked(&mut caches_4k), Tracked(&mut caches_2m), Tracked(&mut caches_1g));
    let tracked mut pools_4k: Map<RwLockPageAllocatorPtr, LockPerm> = Map::tracked_empty();
    let tracked mut pools_2m: Map<RwLockPageAllocatorPtr, LockPerm> = Map::tracked_empty();
    let tracked mut quotas_4k: Map<RwLockPageAllocatorPtr, LockPerm> = Map::tracked_empty();
    let tracked mut quotas_2m: Map<RwLockPageAllocatorPtr, LockPerm> = Map::tracked_empty();
    let (Tracked(pool_1g), Tracked(quota_1g)) = kill_container_retire_lock_pools_quotas(krnl, Tracked(&mut *lctx), thread_ptr, container_ptr, owner_ptr, Tracked(&mut pools_4k),
        Tracked(&mut pools_2m), Tracked(&mut quotas_4k), Tracked(&mut quotas_2m));
    let (Tracked(tails_container), Tracked(tails_pcid)) = kill_container_retire_lock_tails(krnl, Tracked(&mut *lctx), container_ptr);
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&entry, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(entry.ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&entry, &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl); steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    let ghost base = *krnl;
    let ghost base_lctx = *lctx;
    let ghost base_steps = steps.view();
    kill_container_retire_commit(krnl, Tracked(&mut *lctx), container_ptr, parent_ptr, owner_ptr, Tracked(container_perm), Tracked(parent_perm), Tracked(owner_perm),
        Tracked(cpu_set_perm), Tracked(flag_perms), Tracked(pcid_perm), Tracked(shard_perms), Tracked(caches_4k), Tracked(caches_2m), Tracked(caches_1g), Tracked(pools_4k),
        Tracked(pools_2m), Tracked(pool_1g), Tracked(quotas_4k), Tracked(quotas_2m), Tracked(quota_1g), Tracked(page_perms), Tracked(tails_container), Tracked(tails_pcid));
    let ghost retired_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_container_progress(parent_ptr, ContainerKillStage::Walk)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let pre_u = kernel_k_to_kernel_u(base);
        let post_u = kernel_k_to_kernel_u(*krnl);
        let owner_ro = base.ctn_mp.spec_index(owner_ptr).view_rodata().view();
        kill_container_retire_pre_from_k(&base, &base_lctx, cpu_id, process_ptr, thread_ptr, container_ptr);
        kernel_container_retired_implies_u_step(&base, &retired_k, container_ptr, parent_ptr, owner_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&retired_k, &*krnl, thread_ptr);
        kill_container_retire_step_from_u(pre_u, kernel_k_to_kernel_u(retired_k), post_u, cpu_id, thread_ptr, container_ptr, parent_ptr, owner_ptr,
            retired_k.allc_4k_mp.spec_index(owner_ro.allocator_ptr_4k).quota.view().view(), retired_k.allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m).quota.view().view());
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_container_trace_push(&*steps, base_steps, start, pre, pre_u, post_u, cpu_id, ctx);
    }
}
} // verus!
