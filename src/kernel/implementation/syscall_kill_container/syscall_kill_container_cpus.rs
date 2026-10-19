use vstd::prelude::*;
use crate::*;
use super::super::syscall_kill_process::syscall_kill_process_spec::KillTraceCtx;
#[cfg(verus_keep_ghost)]
use super::super::syscall_kill_process::syscall_kill_process_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_spec::kill_container_progress;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_trace::kill_container_trace_push;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_cpus_trace::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_cpus_eof::*;

verus! {
/// The Cpus stage of the container kill on the marked target `container_ptr`, which has no child containers, processes,
/// or threads: mark and write-hold its cpu set, move each of its cpus to the killer's container `owner_ptr` one step at
/// a time, and move on to its free pages. The killer keeps the marked set until the target retires and returns its
/// permission.
pub(crate) fn kill_container_cpus(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, killer_info: KillerInfo,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (ret: (RwLockCpuSetPtr, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        ctx is Container,
        old(lctx).cpu_id() == cpu_id,
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*old(krnl), *old(lctx), process_ptr, thread_ptr, old(lctx).container_lock_map().dom()),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(owner_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Walk),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        cpu_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(container_ptr).killer_info() == Some(killer_info),
        killer_info.process == process_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view().children.view().len() == 0,
        old(lctx).cpu_set_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == cpu_id,
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*final(krnl), *final(lctx), process_ptr, thread_ptr, final(lctx).container_lock_map().dom()),
        final(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !final(krnl).ctn_mp.spec_index(owner_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Pages),
        !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        cpu_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        container_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == final(lctx).thread_id(),
        thread_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).ctn_mp.spec_index(owner_ptr) == old(krnl).ctn_mp.spec_index(owner_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        ({
            let (set_ptr, set_perm) = ret;
            let set_perm = set_perm.view();
            &&& final(lctx).cpu_set_lock_map().dom() =~= set![set_ptr]
            &&& typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write)
            &&& final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == set_ptr
            &&& final(krnl).cpu_set_mp.dom().contains(set_ptr)
            &&& final(krnl).cpu_set_mp.spec_index(set_ptr).being_killed()
            &&& final(krnl).cpu_set_mp.spec_index(set_ptr).killer_info() == Some(killer_info)
            &&& final(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view().is_empty()
            &&& set_perm.state() is WriteLock
            &&& set_perm.thread_id() == final(lctx).thread_id()
            &&& set_perm.lock_id() == final(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id
        }),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
        },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    let (set_ptr, Tracked(set_perm)) = kill_container_cpus_enter(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr,
        killer_info, Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Ghost(start), Ghost(pre), Ghost(ctx));
    let ghost entered_lctx = *lctx;
    let ghost entered_k = *krnl;
    let mut i: usize = 0;
    while i < NUM_CPUS
        invariant
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
                &&& krnl.ctn_mp.dom().contains(c)
                &&& krnl.ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                &&& krnl.ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
                &&& krnl.ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& krnl.ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
                &&& krnl.ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
                &&& krnl.ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
            },
            0 <= i <= NUM_CPUS,
            0 <= start <= steps.view().len(),
            ctx is Container,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == cpu_id,
            old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            kill_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id, ctx),
            killer_held_context(*krnl, *lctx, process_ptr, thread_ptr, lctx.container_lock_map().dom()),
            lctx.thread_lock_map().dom() =~= set![thread_ptr],
            lctx.process_lock_map().dom() =~= set![process_ptr],
            typed_lock_map_contains_mode(lctx.container_lock_map(), container_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.container_lock_map(), owner_ptr, TypedLockMode::Write),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr).being_killed(),
            !krnl.ctn_mp.spec_index(owner_ptr).being_killed(),
            krnl.ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
            krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
            krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Cpus),
            !krnl.thr_mp.spec_index(thread_ptr).view_ghost().exited,
            cpu_perm.lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            process_perm.lock_id() == krnl.prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            container_perm.lock_id() == krnl.ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
            thread_perm.state() is WriteLock,
            thread_perm.thread_id() == lctx.thread_id(),
            thread_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            lctx.cpu_set_lock_map().dom() =~= set![set_ptr],
            typed_lock_map_contains_mode(lctx.cpu_set_lock_map(), set_ptr, TypedLockMode::Write),
            krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == set_ptr,
            krnl.cpu_set_mp.dom().contains(set_ptr),
            krnl.cpu_set_mp.spec_index(set_ptr).being_killed(),
            set_perm.state() is WriteLock,
            set_perm.thread_id() == lctx.thread_id(),
            set_perm.lock_id() == krnl.cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id,
            lctx.container_lock_map() == old(lctx).container_lock_map(),
            krnl.ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
            krnl.ctn_mp.spec_index(owner_ptr) == old(krnl).ctn_mp.spec_index(owner_ptr),
            krnl.prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
            krnl.cpu_set_mp.spec_index(set_ptr).killer_info() == Some(killer_info),
            forall|j: CpuId| #![trigger krnl.cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view().contains(j)] j < i ==> !krnl.cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view().contains(j),
        decreases NUM_CPUS - i,
    {
        proof { cpu_set_perms_wf_map(krnl.cpu_set_mp); cpu_set_perms_wf_at(krnl.cpu_set_mp, set_ptr); }
        let (member, closed) = {
            let set = krnl.cpu_set_mp.borrow_typed(set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&set_perm));
            (set.owned_cpus.contains(i), set.owned_cpus.is_closed(i))
        };
        if member {
            kill_container_move_cpu(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, set_ptr, i, closed,
                Tracked(cpu_perm), Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(&set_perm), Ghost(start), Ghost(pre), Ghost(ctx));
        }
        i = i + 1;
    }
    proof { cpu_set_perms_wf_map(krnl.cpu_set_mp); cpu_set_perms_wf_at(krnl.cpu_set_mp, set_ptr); }
    assert(krnl.cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view() =~= Set::<CpuId>::empty());
    kill_container_pages_enter(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, thread_ptr, container_ptr, owner_ptr, set_ptr, Tracked(cpu_perm),
        Tracked(process_perm), Tracked(thread_perm), Tracked(container_perm), Tracked(&set_perm), Ghost(start), Ghost(pre), Ghost(ctx));
    (set_ptr, Tracked(set_perm))
}

/// Mark and write-hold the cpu set of the marked target `container_ptr`, which has no child containers, processes, or
/// threads, for the target's killer, and move the kill on to the target's cpus.
fn kill_container_cpus_enter(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, killer_info: KillerInfo,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
) -> (ret: (RwLockCpuSetPtr, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        ctx is Container,
        old(lctx).cpu_id() == cpu_id,
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*old(krnl), *old(lctx), process_ptr, thread_ptr, old(lctx).container_lock_map().dom()),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(owner_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Walk),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        cpu_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.spec_index(container_ptr).killer_info() == Some(killer_info),
        killer_info.process == process_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view().children.view().len() == 0,
        old(lctx).cpu_set_lock_map().dom().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == cpu_id,
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*final(krnl), *final(lctx), process_ptr, thread_ptr, final(lctx).container_lock_map().dom()),
        final(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !final(krnl).ctn_mp.spec_index(owner_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Cpus),
        !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        cpu_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        container_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == final(lctx).thread_id(),
        thread_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).ctn_mp.spec_index(owner_ptr) == old(krnl).ctn_mp.spec_index(owner_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        ({
            let (set_ptr, set_perm) = ret;
            let set_perm = set_perm.view();
            &&& final(lctx).cpu_set_lock_map().dom() =~= set![set_ptr]
            &&& typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write)
            &&& final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == set_ptr
            &&& final(krnl).cpu_set_mp.dom().contains(set_ptr)
            &&& final(krnl).cpu_set_mp.spec_index(set_ptr).being_killed()
            &&& final(krnl).cpu_set_mp.spec_index(set_ptr).killer_info() == Some(killer_info)
            &&& set_perm.state() is WriteLock
            &&& set_perm.thread_id() == final(lctx).thread_id()
            &&& set_perm.lock_id() == final(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id
        }),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
        },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof {
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, container_ptr);
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id);
    }
    let set_ptr = krnl.ctn_mp.borrow_rodata(container_ptr).borrow().cpu_set;
    let Tracked(set_perm) = krnl.wlock_cpu_set_and_mark_kill(container_ptr, set_ptr, killer_info, Tracked(&mut *lctx));
    let ghost marked_k = *krnl;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_container_progress(container_ptr, ContainerKillStage::Cpus)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let entered_k = *krnl;
        kill_container_cpus_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, container_ptr, ContainerKillStage::Walk);
        kernel_cpu_set_locked_and_marked_implies_u_step(&before, &marked_k, container_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&marked_k, &entered_k, thread_ptr);
        kill_container_cpus_step_from_u(kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(marked_k), kernel_k_to_kernel_u(entered_k), cpu_id, thread_ptr, container_ptr);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_container_trace_push(&*steps, before_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(entered_k), cpu_id, ctx);
    }
    (set_ptr, Tracked(set_perm))
}

/// Move the kill on from the marked target `container_ptr`, whose held marked cpu set `set_ptr` holds no cpu any more,
/// to its free pages.
fn kill_container_pages_enter(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, set_ptr: RwLockCpuSetPtr,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>,
    Tracked(set_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        ctx is Container,
        old(lctx).cpu_id() == cpu_id,
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*old(krnl), *old(lctx), process_ptr, thread_ptr, old(lctx).container_lock_map().dom()),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(owner_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Cpus),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        cpu_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).cpu_set_lock_map().dom() =~= set![set_ptr],
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == set_ptr,
        old(krnl).cpu_set_mp.dom().contains(set_ptr),
        old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
        set_perm.state() is WriteLock,
        set_perm.thread_id() == old(lctx).thread_id(),
        set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view().is_empty(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == cpu_id,
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*final(krnl), *final(lctx), process_ptr, thread_ptr, final(lctx).container_lock_map().dom()),
        final(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !final(krnl).ctn_mp.spec_index(owner_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Pages),
        !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        cpu_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        container_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == final(lctx).thread_id(),
        thread_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).cpu_set_lock_map().dom() =~= set![set_ptr],
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == set_ptr,
        final(krnl).cpu_set_mp.dom().contains(set_ptr),
        final(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
        set_perm.state() is WriteLock,
        set_perm.thread_id() == final(lctx).thread_id(),
        set_perm.lock_id() == final(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id,
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).ctn_mp.spec_index(owner_ptr) == old(krnl).ctn_mp.spec_index(owner_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).cpu_set_mp.spec_index(set_ptr) == old(krnl).cpu_set_mp.spec_index(set_ptr),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
        },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    let ghost before = *krnl;
    let ghost before_lctx = *lctx;
    let ghost before_steps = steps.view();
    proof { thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(kill_container_progress(container_ptr, ContainerKillStage::Pages)), Tracked(&*lctx), Tracked(thread_perm));
    proof {
        let entered_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        kill_container_cpus_pre_from_k(&before, &before_lctx, cpu_id, process_ptr, thread_ptr, container_ptr, ContainerKillStage::Cpus);
        kernel_container_without_cpus_implies_u(&before, container_ptr);
        kernel_thread_syscall_progress_changed_implies_u_step(&before, &entered_k, thread_ptr);
        kill_container_pages_step_from_u(kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(entered_k), cpu_id, thread_ptr, container_ptr);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        kill_container_trace_push(&*steps, before_steps, start, pre, kernel_k_to_kernel_u(before), kernel_k_to_kernel_u(entered_k), cpu_id, ctx);
    }
}

/// Move the cpu `cpu_i` of the marked target `container_ptr`, which the held marked set `set_ptr` holds (closed when
/// `closed`), to the killer's container `owner_ptr` in one step, dropping the target's offline request for it.
fn kill_container_move_cpu(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, set_ptr: RwLockCpuSetPtr, cpu_i: CpuId, closed: bool,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(process_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(container_perm): Tracked<&LockPerm>,
    Tracked(set_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        ctx is Container,
        old(lctx).cpu_id() == cpu_id,
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*old(krnl), *old(lctx), process_ptr, thread_ptr, old(lctx).container_lock_map().dom()),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(owner_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Cpus),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        cpu_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        container_perm.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(lctx).cpu_set_lock_map().dom() =~= set![set_ptr],
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == set_ptr,
        old(krnl).cpu_set_mp.dom().contains(set_ptr),
        old(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
        set_perm.state() is WriteLock,
        set_perm.thread_id() == old(lctx).thread_id(),
        set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, cpu_i),
        old(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view().contains(cpu_i),
        closed == old(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.closed_view().contains(cpu_i),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == cpu_id,
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        killer_held_context(*final(krnl), *final(lctx), process_ptr, thread_ptr, final(lctx).container_lock_map().dom()),
        final(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        final(lctx).process_lock_map().dom() =~= set![process_ptr],
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).container_lock_map(), owner_ptr, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == owner_ptr,
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        !final(krnl).ctn_mp.spec_index(owner_ptr).being_killed(),
        final(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth < final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().depth,
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_container_progress(container_ptr, ContainerKillStage::Cpus),
        !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        cpu_perm.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_perm.lock_id() == final(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        container_perm.lock_id() == final(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == final(lctx).thread_id(),
        thread_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(lctx).cpu_set_lock_map().dom() =~= set![set_ptr],
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == set_ptr,
        final(krnl).cpu_set_mp.dom().contains(set_ptr),
        final(krnl).cpu_set_mp.spec_index(set_ptr).being_killed(),
        set_perm.state() is WriteLock,
        set_perm.thread_id() == final(lctx).thread_id(),
        set_perm.lock_id() == final(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id,
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).ctn_mp.spec_index(owner_ptr) == old(krnl).ctn_mp.spec_index(owner_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).cpu_set_mp.spec_index(set_ptr).killer_info() == old(krnl).cpu_set_mp.spec_index(set_ptr).killer_info(),
        final(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view() == old(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view().remove(cpu_i),
        forall|c: RwLockContainerPtr| #![trigger old(lctx).container_lock_map().dom().contains(c)] old(lctx).container_lock_map().dom().contains(c) ==> {
            &&& final(krnl).ctn_mp.dom().contains(c)
            &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
            &&& final(krnl).ctn_mp.spec_index(c).killer_info() == old(krnl).ctn_mp.spec_index(c).killer_info()
            &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq == old(krnl).ctn_mp.spec_index(c).view_ghost().uppertree_seq
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set == old(krnl).ctn_mp.spec_index(c).view_ghost().subtree_set
            &&& final(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes == old(krnl).ctn_mp.spec_index(c).view_ghost().owned_processes
        },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    let ghost base = *krnl;
    let ghost base_lctx = *lctx;
    let ghost base_steps = steps.view();
    proof {
        let owner_set = krnl.ctn_mp.spec_index(owner_ptr).view_rodata().view().cpu_set;
        container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, container_ptr, cpu_i); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_i);
        container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
        cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_i);
        thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_i); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id);
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, owner_ptr);
        container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, owner_ptr); container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr);
        cpu_set_kill_mark_wf_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, owner_set);
        container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr);
        container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr);
    }
    let owner_set = krnl.ctn_mp.borrow_rodata(owner_ptr).borrow().cpu_set;
    let depth = krnl.ctn_mp.borrow_rodata(owner_ptr).borrow().depth;
    let flags_ptr = container_ptr + 4096;
    let (Tracked(moved_perm), Tracked(flag_perm), Tracked(owner_set_perm)) = kill_container_move_cpu_lock(krnl, Tracked(&mut *lctx), process_ptr, thread_ptr, set_ptr,
        owner_set, flags_ptr, cpu_i, closed);
    kill_container_move_cpu_commit(krnl, Tracked(&mut *lctx), container_ptr, owner_ptr, set_ptr, owner_set, flags_ptr, cpu_i, depth, closed, Tracked(moved_perm), Tracked(flag_perm),
        Tracked(owner_set_perm), Tracked(set_perm), Ghost(base));
    proof {
        let moved_k = *krnl;
        assert(lctx.cpu_lock_map() =~= base_lctx.cpu_lock_map());
        assert(lctx.cpu_set_lock_map() =~= base_lctx.cpu_set_lock_map());
        assert(lctx.cpu_offline_flag_lock_map() =~= base_lctx.cpu_offline_flag_lock_map());
        kill_container_cpus_pre_from_k(&base, &base_lctx, cpu_id, process_ptr, thread_ptr, container_ptr, ContainerKillStage::Cpus);
        kill_container_move_cpu_pre_from_k(&base, cpu_i, container_ptr);
        kernel_cpu_moved_to_container_implies_u_step(&base, &moved_k, cpu_i, container_ptr, owner_ptr);
        kill_container_move_cpu_step_from_u(kernel_k_to_kernel_u(base), kernel_k_to_kernel_u(moved_k), cpu_id, container_ptr, owner_ptr, cpu_i);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
        kill_container_trace_push(&*steps, base_steps, start, pre, kernel_k_to_kernel_u(base), kernel_k_to_kernel_u(moved_k), cpu_id, ctx);
    }
}

/// Write-hold the cpu `cpu_i` of the target, which the target's held marked set `set_ptr` holds (closed when `closed`),
/// its request cell in the target's table `flags_ptr`, and the killer container's unmarked set `owner_set`: an Idle cpu
/// first, an Off cpu last.
fn kill_container_move_cpu_lock(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, set_ptr: RwLockCpuSetPtr,
    owner_set: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_i: CpuId, closed: bool,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        killer_held_context(*old(krnl), *old(lctx), process_ptr, thread_ptr, old(lctx).container_lock_map().dom()),
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !(old(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED),
        old(krnl).cpu_set_mp.dom().contains(set_ptr),
        old(lctx).cpu_set_lock_map().dom() =~= set![set_ptr],
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write),
        old(krnl).cpu_set_mp.dom().contains(owner_set),
        owner_set != set_ptr,
        !old(krnl).cpu_set_mp.spec_index(owner_set).being_killed(),
        old(krnl).cpu_offline_mp.dom().contains(flags_ptr),
        index_valid(NUM_CPUS, cpu_i),
        cpu_i != old(lctx).cpu_id(),
        !old(krnl).cpu_arr.spec_index(cpu_i).view().being_killed(),
        closed ==> old(krnl).cpu_arr.spec_index(cpu_i).view().view().view().state is Off && old(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.closed_view().contains(cpu_i),
        !closed ==> old(krnl).cpu_arr.spec_index(cpu_i).view().view().view().state is Idle,
        old(krnl).cpu_arr.spec_index(cpu_i).view().view().view().container_depth == old(krnl).cpu_offline_mp.spec_index(flags_ptr).container_depth.view(),
        old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().container_depth < old(krnl).cpu_offline_mp.spec_index(flags_ptr).container_depth.view(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_lock_map().remove(cpu_i) == old(lctx).cpu_lock_map(),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_i, TypedLockMode::Write),
        final(lctx).cpu_set_lock_map().remove(owner_set) == old(lctx).cpu_set_lock_map(),
        typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), owner_set, TypedLockMode::Write),
        final(lctx).cpu_offline_flag_lock_map().remove((flags_ptr, cpu_i)) == old(lctx).cpu_offline_flag_lock_map(),
        typed_lock_map_contains_mode(final(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_i), TypedLockMode::Write),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_set_mp: final(krnl).cpu_set_mp, cpu_offline_mp: final(krnl).cpu_offline_mp, ..*old(krnl) }),
        final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_i),
        old(krnl).cpu_arr.spec_index(cpu_i).view().locking_thread() is None,
        final(krnl).cpu_arr.spec_index(cpu_i).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_i).view().being_killed(),
        final(krnl).cpu_published[cpu_i as int].view() == (final(krnl).cpu_arr.spec_index(cpu_i).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(cpu_i).view().view().view().current_pcid),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_i).view().locking_thread()->Write_lock_id,
        final(krnl).cpu_set_mp.unchanged_except(&old(krnl).cpu_set_mp, owner_set),
        old(krnl).cpu_set_mp.spec_index(owner_set).locking_thread() is None,
        final(krnl).cpu_set_mp.spec_index(owner_set).view() == old(krnl).cpu_set_mp.spec_index(owner_set).view(),
        final(krnl).cpu_set_mp.spec_index(owner_set).being_killed() == old(krnl).cpu_set_mp.spec_index(owner_set).being_killed(),
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).cpu_set_mp.spec_index(owner_set).locking_thread()->Write_lock_id,
        final(krnl).cpu_offline_mp.unchanged_except(&old(krnl).cpu_offline_mp, flags_ptr),
        cpu_offline_requests_of(final(krnl).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(krnl).cpu_offline_mp.spec_index(flags_ptr)),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_i).view().locking_thread()->Write_lock_id,
{
    if closed {
        let Tracked(flag_perm) = krnl.wlock_cpu_offline_flag(flags_ptr, cpu_i, Tracked(&mut *lctx));
        let Tracked(set_perm) = krnl.wlock_cpu_set(owner_set, Tracked(&mut *lctx));
        let Tracked(cpu_perm) = krnl.wlock_off_cpu(cpu_i, set_ptr, Tracked(&mut *lctx));
        proof {
            assert(lctx.cpu_lock_map().remove(cpu_i) =~= old(lctx).cpu_lock_map());
            assert(lctx.cpu_set_lock_map().remove(owner_set) =~= old(lctx).cpu_set_lock_map());
            assert(lctx.cpu_offline_flag_lock_map().remove((flags_ptr, cpu_i)) =~= old(lctx).cpu_offline_flag_lock_map());
        }
        (Tracked(cpu_perm), Tracked(flag_perm), Tracked(set_perm))
    } else {
        let Tracked(cpu_perm) = krnl.wlock_cpu(cpu_i, Tracked(&mut *lctx)).unwrap();
        let Tracked(flag_perm) = krnl.wlock_cpu_offline_flag(flags_ptr, cpu_i, Tracked(&mut *lctx));
        let Tracked(set_perm) = krnl.wlock_cpu_set(owner_set, Tracked(&mut *lctx));
        proof {
            assert(lctx.cpu_lock_map().remove(cpu_i) =~= old(lctx).cpu_lock_map());
            assert(lctx.cpu_set_lock_map().remove(owner_set) =~= old(lctx).cpu_set_lock_map());
            assert(lctx.cpu_offline_flag_lock_map().remove((flags_ptr, cpu_i)) =~= old(lctx).cpu_offline_flag_lock_map());
        }
        (Tracked(cpu_perm), Tracked(flag_perm), Tracked(set_perm))
    }
}

/// With the cpu `cpu_i` of the target `container_ptr`, its request cell in the target's table `flags_ptr`, the target's
/// marked set `set_ptr`, and the set `owner_set` of the killer's container `owner_ptr` write-held, move the cpu to
/// `owner_ptr` at `depth`, clear the cell, and release the cpu, the cell, and `owner_set`. The state at the start of the
/// step is `base`.
fn kill_container_move_cpu_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, container_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr, set_ptr: RwLockCpuSetPtr,
    owner_set: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_i: CpuId, depth: usize, closed: bool, Tracked(moved_perm): Tracked<LockPerm>,
    Tracked(flag_perm): Tracked<LockPerm>, Tracked(owner_set_perm): Tracked<LockPerm>, Tracked(set_perm): Tracked<&LockPerm>, Ghost(base): Ghost<KernelK>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_i),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.dom().contains(owner_ptr),
        container_ptr != owner_ptr,
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == set_ptr,
        old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().cpu_set == owner_set,
        old(krnl).ctn_mp.spec_index(owner_ptr).view_rodata().view().depth == depth,
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().is_empty(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_threads.view().is_empty(),
        flags_ptr == cpu_offline_flags_ptr(container_ptr),
        old(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view().contains(cpu_i),
        closed == old(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.closed_view().contains(cpu_i),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_i, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), set_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), owner_set, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_i), TypedLockMode::Write),
        moved_perm.state() is WriteLock,
        moved_perm.thread_id() == old(lctx).thread_id(),
        moved_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_i).view().locking_thread()->Write_lock_id,
        flag_perm.state() is WriteLock,
        flag_perm.thread_id() == old(lctx).thread_id(),
        flag_perm.lock_id() == old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_i).view().locking_thread()->Write_lock_id,
        owner_set_perm.state() is WriteLock,
        owner_set_perm.thread_id() == old(lctx).thread_id(),
        owner_set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(owner_set).locking_thread()->Write_lock_id,
        set_perm.state() is WriteLock,
        set_perm.thread_id() == old(lctx).thread_id(),
        set_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_published[cpu_i as int].view() == (old(krnl).cpu_arr.spec_index(cpu_i).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_i).view().view().view().current_pcid),
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, cpu_set_mp: old(krnl).cpu_set_mp, cpu_offline_mp: old(krnl).cpu_offline_mp, ..base }),
        old(krnl).cpu_arr.unchanged_except(&base.cpu_arr, cpu_i),
        base.cpu_arr.spec_index(cpu_i).view().locking_thread() is None,
        old(krnl).cpu_arr.spec_index(cpu_i).view().being_killed() == base.cpu_arr.spec_index(cpu_i).view().being_killed(),
        old(krnl).cpu_set_mp.unchanged_except(&base.cpu_set_mp, owner_set),
        base.cpu_set_mp.spec_index(owner_set).locking_thread() is None,
        !base.cpu_set_mp.spec_index(owner_set).being_killed(),
        old(krnl).cpu_set_mp.spec_index(owner_set).being_killed() == base.cpu_set_mp.spec_index(owner_set).being_killed(),
        old(krnl).cpu_offline_mp.unchanged_except(&base.cpu_offline_mp, flags_ptr),
        cpu_offline_requests_of(old(krnl).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(base.cpu_offline_mp.spec_index(flags_ptr)),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map().remove(cpu_i),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map().remove(owner_set),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map().remove((flags_ptr, cpu_i)),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_set_mp: final(krnl).cpu_set_mp, cpu_offline_mp: final(krnl).cpu_offline_mp, ..base }),
        forall|j: CpuId| #![trigger final(krnl).cpu_arr.spec_index(j)] index_valid(NUM_CPUS, j) && j != cpu_i ==> final(krnl).cpu_arr.spec_index(j) == base.cpu_arr.spec_index(j),
        final(krnl).cpu_arr.spec_index(cpu_i).view().view().view() == (CpuView { owning_container: owner_ptr, container_depth: depth, ..base.cpu_arr.spec_index(cpu_i).view().view().view() }),
        final(krnl).cpu_arr.spec_index(cpu_i).view().lock_state_u() == base.cpu_arr.spec_index(cpu_i).view().lock_state_u(),
        final(krnl).cpu_arr.spec_index(cpu_i).view().being_killed() == base.cpu_arr.spec_index(cpu_i).view().being_killed(),
        final(krnl).cpu_set_mp.dom() == base.cpu_set_mp.dom(),
        forall|s: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.spec_index(s)] base.cpu_set_mp.dom().contains(s)
            ==> final(krnl).cpu_set_mp.spec_index(s).lock_state_u() == base.cpu_set_mp.spec_index(s).lock_state_u() && final(krnl).cpu_set_mp.spec_index(s).being_killed() == base.cpu_set_mp.spec_index(s).being_killed(),
        final(krnl).cpu_set_mp.spec_index(set_ptr).locking_thread() == base.cpu_set_mp.spec_index(set_ptr).locking_thread(),
        final(krnl).cpu_set_mp.spec_index(set_ptr).killer_info() == base.cpu_set_mp.spec_index(set_ptr).killer_info(),
        final(krnl).cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view() == base.cpu_set_mp.spec_index(set_ptr).view().owned_cpus.view().remove(cpu_i),
        final(krnl).cpu_offline_mp.unchanged_except(&base.cpu_offline_mp, flags_ptr),
        cpu_offline_requests_of(final(krnl).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(base.cpu_offline_mp.spec_index(flags_ptr)).update(cpu_i as int, false),
{
    proof {
        container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr); container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, owner_ptr);
        cpu_set_perms_wf_map(krnl.cpu_set_mp); cpu_set_perms_wf_at(krnl.cpu_set_mp, set_ptr); cpu_set_perms_wf_at(krnl.cpu_set_mp, owner_set);
        container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, container_ptr, cpu_i); container_cpu_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, owner_ptr, cpu_i);
        cpu_array_wf_map(krnl.cpu_arr, krnl.dflt_pt.view()); cpu_array_wf_at(krnl.cpu_arr, krnl.dflt_pt.view(), cpu_i);
        thread_cpu_wf_killed_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_i);
        container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr);
        cpu_offline_flags_wf_map(krnl.cpu_offline_mp, krnl.cpu_arr); cpu_offline_flags_wf_at(krnl.cpu_offline_mp, krnl.cpu_arr, flags_ptr);
        assert(lctx.lock_entry_contains(krnl.cpu_arr.lock_id_by_index(cpu_i), KernelObjId::Cpu(cpu_i))) by { reveal(LockedArray::typed_lock_map_aligned); };
        assert(krnl.cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_i).view().wlocked_by(&*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
    }
    let ghost locked = *krnl;
    let ghost locked_lctx = *lctx;
    {
        let source = krnl.cpu_set_mp.borrow_mut_typed(set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(set_perm));
        source.owned_cpus.remove(cpu_i);
        let target = krnl.cpu_set_mp.borrow_mut_typed(owner_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&owner_set_perm));
        if closed { target.owned_cpus.insert_closed(cpu_i); } else { target.owned_cpus.insert(cpu_i); }
    }
    krnl.cpu_offline_mp.set_flag(flags_ptr, cpu_i, false, Tracked(&*lctx), Tracked(&flag_perm));
    {
        let cpu = krnl.cpu_arr.borrow_mut_typed(cpu_i, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&moved_perm));
        if closed { cpu.transfer_off_cpu_to_container(owner_ptr, depth); } else { cpu.transfer_idle_cpu_to_container(owner_ptr, depth); }
    }
    proof {
        let entry = TypedHeldLock { lock_id: locked.cpu_arr.lock_id_by_index(cpu_i), mode: TypedLockMode::Write };
        lctx.update_lock_id(KernelObjId::Cpu(cpu_i), locked.cpu_arr.lock_id_by_index(cpu_i), krnl.cpu_arr.lock_id_by_index(cpu_i));
        map_insert_overwrite_lemma(locked_lctx.cpu_lock_map(), cpu_i, entry, TypedHeldLock { lock_id: krnl.cpu_arr.lock_id_by_index(cpu_i), mode: TypedLockMode::Write });
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); reveal(LockedArray::typed_lock_map_aligned); };
        assert(kill_container_cpus_eof_transition_framing(locked, *krnl, set_ptr, owner_set, flags_ptr, cpu_i, owner_ptr, depth, closed)) by {
            reveal(kill_container_cpus_eof_transition_framing);
        };
        kill_container_cpus_eof(locked, *krnl, container_ptr, owner_ptr, set_ptr, owner_set, flags_ptr, cpu_i, depth, closed);
    }
    krnl.wunlock_cpu_set(owner_set, Tracked(&mut *lctx), Tracked(owner_set_perm));
    krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_i, Tracked(&mut *lctx), Tracked(flag_perm));
    krnl.wunlock_cpu(cpu_i, Tracked(&mut *lctx), Tracked(moved_perm));
    proof {
        assert(lctx.cpu_lock_map() =~= old(lctx).cpu_lock_map().remove(cpu_i));
    }
}
}
