use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::KillTraceCtx;
use super::syscall_kill_container_pages_lock::kill_container_pages_lock;
use super::syscall_kill_container_pages_drain::kill_container_pages_drain;
use super::syscall_kill_container_pages_move::{kill_container_pages_move_4k, kill_container_pages_move_2m, kill_container_pages_move_1g};
use super::syscall_kill_container_pages_finish::kill_container_pages_retire_and_unlock;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_pages_spec::*;

verus! {
/// Move every free page of the marked container `ctn_ptr` to the killer's container `owner_ptr`: write-hold the
/// marked container's 4K and 2M allocator caches and both containers' 4K, 2M, and 1G global pools and quotas, drain the
/// caches into the marked container's pools, move each pooled page with one page of quota in its own step, and start
/// retiring the container, which then holds no quota; 1G caches hold no page.
pub(crate) fn kill_container_pages(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, Tracked(cpu_perm): Tracked<&LockPerm>,
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
        kill_container_pages_killer_state(*old(krnl), *old(lctx), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, *cpu_perm, *process_perm, *thread_perm, *container_perm, *owner_perm),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == kill_container_progress(ctn_ptr, ContainerKillStage::Pages),
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        old(krnl).ctn_mp.spec_index(ctn_ptr).view().children.view().len() == 0,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
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
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            &&& final(krnl).ctn_mp.spec_index(c).view().children == old(krnl).ctn_mp.spec_index(c).view().children
        },
        final(krnl).ctn_mp.spec_index(ctn_ptr).view_ghost().retire_ready,
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
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
    let tracked mut pools_1g = Map::<RwLockPageAllocatorPtr, LockPerm>::tracked_empty();
    let tracked mut quotas_1g = Map::<RwLockPageAllocatorPtr, LockPerm>::tracked_empty();
    let (a4, o4, a2, o2, a1, o1) = kill_container_pages_lock(krnl, Tracked(&mut *lctx), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, Tracked(cpu_perm), Tracked(process_perm),
        Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&mut caches_4k), Tracked(&mut caches_2m), Tracked(&mut pools_4k), Tracked(&mut pools_2m),
        Tracked(&mut quotas_4k), Tracked(&mut quotas_2m), Tracked(&mut pools_1g), Tracked(&mut quotas_1g));
    proof {
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
        steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    kill_container_pages_drain(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, a4, o4, a2, o2, a1, o1, Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&caches_4k), Tracked(&caches_2m), Tracked(&pools_4k), Tracked(&pools_2m),
        Tracked(&quotas_4k), Tracked(&quotas_2m), Tracked(&pools_1g), Tracked(&quotas_1g));
    kill_container_pages_move_4k(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, a4, o4, a2, o2, a1, o1, Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&caches_4k), Tracked(&caches_2m), Tracked(&pools_4k), Tracked(&pools_2m),
        Tracked(&quotas_4k), Tracked(&quotas_2m), Tracked(&pools_1g), Tracked(&quotas_1g), Ghost(start), Ghost(pre), Ghost(ctx));
    kill_container_pages_move_2m(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, a4, o4, a2, o2, a1, o1, Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&caches_4k), Tracked(&caches_2m), Tracked(&pools_4k), Tracked(&pools_2m),
        Tracked(&quotas_4k), Tracked(&quotas_2m), Tracked(&pools_1g), Tracked(&quotas_1g), Ghost(start), Ghost(pre), Ghost(ctx));
    kill_container_pages_move_1g(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, a4, o4, a2, o2, a1, o1, Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(&caches_4k), Tracked(&caches_2m), Tracked(&pools_4k), Tracked(&pools_2m),
        Tracked(&quotas_4k), Tracked(&quotas_2m), Tracked(&pools_1g), Tracked(&quotas_1g), Ghost(start), Ghost(pre), Ghost(ctx));
    kill_container_pages_retire_and_unlock(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, prc_ptr, thrd_ptr, ctn_ptr, owner_ptr, a4, o4, a2, o2, a1, o1,
        Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(owner_perm), Tracked(caches_4k), Tracked(caches_2m), Tracked(pools_4k),
        Tracked(pools_2m), Tracked(quotas_4k), Tracked(quotas_2m), Tracked(pools_1g), Tracked(quotas_1g), Ghost(start), Ghost(pre), Ghost(ctx));
}
} // verus!
