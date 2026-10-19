use vstd::prelude::*;
use crate::*;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::attach_endpoint_reference_and_unlock::attach_endpoint_reference_and_unlock;

verus! {
/// Release phase of the child's root-thread creation: unlocks the child process, both page tables, the new thread's page, and the
/// scheduler shard, clears the staging thread's progress, attaches the initial endpoint to the scheduled new thread, and unlocks
/// both threads, the parent process, both containers, and the cpu, leaving no lock held.
pub(super) fn release_new_container_root_thread_locks_and_attach_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, parent_container_ptr: RwLockContainerPtr, child_container_ptr: RwLockContainerPtr,
    parent_process_ptr: RwLockProcessPtr, child_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, new_thread_ptr: RwLockThreadPtr,
    source_pagetable_ptr: RwLockPageTableRoot, child_pagetable_ptr: RwLockPageTableRoot, scheduler_ptr: RwLockSchedulerPtr, endpoint: Option<RwLockEndpointPtr>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(parent_container_lock_perm): Tracked<LockPerm>, Tracked(child_container_lock_perm): Tracked<LockPerm>,
    Tracked(parent_process_lock_perm): Tracked<LockPerm>, Tracked(child_process_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
    Tracked(new_thread_lock_perm): Tracked<LockPerm>, Tracked(thread_page_lock_perm): Tracked<LockPerm>, Tracked(scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(endpoint_lock_perm): Tracked<Option<LockPerm>>, Tracked(source_pagetable_lock_perm): Tracked<LockPerm>, Tracked(child_pagetable_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(new_thread_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr, child_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, new_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        parent_container_ptr != child_container_ptr,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().owned_processes.view().contains(parent_process_ptr),
        parent_container_lock_perm.state() is WriteLock && parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost().owned_processes.view().contains(child_process_ptr),
        child_container_lock_perm.state() is WriteLock && child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        parent_process_ptr != child_process_ptr,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Zombie,
        parent_process_lock_perm.state() is WriteLock && parent_process_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(child_process_ptr).view().state.view() is Running,
        child_process_lock_perm.state() is WriteLock && child_process_lock_perm.thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(child_process_ptr).locking_thread()->Write_lock_id,
        current_thread_ptr != new_thread_ptr,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() != Some(SyscallProgress::ThreadExitZombie),
        current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(new_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), new_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(new_thread_ptr).is_init(),
        !old(krnl).thr_mp.spec_index(new_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == child_container_ptr,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) is None,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().syscall_progress.view() is None,
        new_thread_lock_perm.state() is WriteLock && new_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        new_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(new_thread_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(new_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(new_thread_ptr), TypedLockMode::Write),
        thread_page_lock_perm.state() is WriteLock && thread_page_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(new_thread_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock && scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        source_pagetable_ptr != child_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
        source_pagetable_lock_perm.state() is WriteLock && source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, child_pagetable_ptr, old(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().leaves_present(),
        child_pagetable_lock_perm.state() is WriteLock && child_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            let owner = old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container;
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& owner == child_container_ptr || old(krnl).ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(child_container_ptr)
            &&& endpoint_lock_perm is Some
            &&& endpoint_lock_perm->Some_0.state() is WriteLock && endpoint_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp, pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, sched_mp: final(krnl).sched_mp,
            thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, cpu_arr: final(krnl).cpu_arr, ..*old(krnl) }),
        forall|p: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(p)]
            old(krnl).ctn_mp.dom().contains(p) ==> if p == child_container_ptr || p == parent_container_ptr { final(krnl).ctn_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).ctn_mp.spec_index(p).locking_thread() == old(krnl).ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
            old(krnl).prc_mp.dom().contains(p) ==> if p == child_process_ptr || p == parent_process_ptr { final(krnl).prc_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(p)]
            old(krnl).thr_mp.dom().contains(p) ==> if p == current_thread_ptr || p == new_thread_ptr { final(krnl).thr_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).thr_mp.spec_index(p).locking_thread() == old(krnl).thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(p)]
            old(krnl).ep_mp.dom().contains(p) ==> if endpoint == Some(p) { final(krnl).ep_mp.spec_index(p).locking_thread() is None } else { final(krnl).ep_mp.spec_index(p).locking_thread() == old(krnl).ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)]
            old(krnl).pt_mp.dom().contains(p) ==> if p == child_pagetable_ptr || p == source_pagetable_ptr { final(krnl).pt_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).pt_mp.spec_index(p).locking_thread() == old(krnl).pt_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { final(krnl).cpu_arr.spec_index(i).value.locking_thread() is None } else { final(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(krnl).cpu_arr.spec_index(i).value.locking_thread() },
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            old(krnl).ctn_mp.dom().contains(c) ==> {
                &&& final(krnl).ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
                &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost() == old(krnl).ctn_mp.spec_index(c).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
            },
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)] old(krnl).pt_mp.dom().contains(p) ==> final(krnl).pt_mp.spec_index(p).view() == old(krnl).pt_mp.spec_index(p).view(),
        kernel_cpu_nonlock_fields_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr),
        kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, final(krnl).prc_mp),
        final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger scheduler_shards_of(final(krnl).sched_mp.spec_index(s))]
            old(krnl).sched_mp.dom().contains(s) ==> scheduler_shards_of(final(krnl).sched_mp.spec_index(s)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(s)),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            old(krnl).thr_mp.dom().contains(t) ==> {
                &&& final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed()
                &&& t != current_thread_ptr && t != new_thread_ptr ==> final(krnl).thr_mp.spec_index(t).view() == old(krnl).thr_mp.spec_index(t).view()
            },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(current_thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(new_thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() == if endpoint is Some {
            old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view().update(0, endpoint)
        } else { old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() },
        final(krnl).ep_mp.dom() == old(krnl).ep_mp.dom(),
        endpoint is Some ==> final(krnl).ep_mp.dom().contains(endpoint->Some_0),
        forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)]
            old(krnl).ep_mp.dom().contains(e) ==> {
                let a = old(krnl).ep_mp.spec_index(e);
                let b = final(krnl).ep_mp.spec_index(e);
                &&& b.view().queue.view() == a.view().queue.view()
                &&& b.view().queue_state == a.view().queue_state
                &&& b.view().owning_threads.view() == if endpoint == Some(e) { a.view().owning_threads.view().insert((new_thread_ptr, 0usize)) } else { a.view().owning_threads.view() }
                &&& b.view().owning_container == a.view().owning_container
                &&& b.being_killed() == a.being_killed()
            },
{
    release_new_container_child_side_locks_and_attach_endpoint(
        krnl, Tracked(&mut *lctx), cpu_id, parent_process_ptr, child_process_ptr, current_thread_ptr, new_thread_ptr, source_pagetable_ptr, child_pagetable_ptr,
        scheduler_ptr, endpoint, Tracked(child_process_lock_perm), Tracked(&current_thread_lock_perm), Tracked(new_thread_lock_perm), Tracked(thread_page_lock_perm),
        Tracked(scheduler_lock_perm), Tracked(endpoint_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(child_pagetable_lock_perm),
    );
    release_new_container_caller_side_locks(
        krnl, Tracked(&mut *lctx), cpu_id, parent_container_ptr, child_container_ptr, parent_process_ptr, current_thread_ptr, Tracked(cpu_lock_perm),
        Tracked(parent_container_lock_perm), Tracked(child_container_lock_perm), Tracked(parent_process_lock_perm), Tracked(current_thread_lock_perm),
    );
    proof {
        assert(kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, krnl.prc_mp)) by { broadcast use kernel_process_nonlock_fields_unchanged_transitive; };
    }
}

/// Releases the child process, both page tables, the new thread's page, and the scheduler shard, clears the staging thread's
/// progress, and attaches the initial endpoint to the scheduled new thread before unlocking it.
fn release_new_container_child_side_locks_and_attach_endpoint(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, parent_process_ptr: RwLockProcessPtr, child_process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, new_thread_ptr: RwLockThreadPtr, source_pagetable_ptr: RwLockPageTableRoot, child_pagetable_ptr: RwLockPageTableRoot,
    scheduler_ptr: RwLockSchedulerPtr, endpoint: Option<RwLockEndpointPtr>, Tracked(child_process_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(new_thread_lock_perm): Tracked<LockPerm>, Tracked(thread_page_lock_perm): Tracked<LockPerm>, Tracked(scheduler_lock_perm): Tracked<LockPerm>,
    Tracked(endpoint_lock_perm): Tracked<Option<LockPerm>>, Tracked(source_pagetable_lock_perm): Tracked<LockPerm>, Tracked(child_pagetable_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(new_thread_ptr)],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr, child_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, new_thread_ptr],
        endpoint is None ==> old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable_ptr, child_pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        parent_process_ptr != child_process_ptr,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.dom().contains(child_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(child_process_ptr).view().state.view() is Running,
        child_process_lock_perm.state() is WriteLock && child_process_lock_perm.thread_id() == old(lctx).thread_id(),
        child_process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(child_process_ptr).locking_thread()->Write_lock_id,
        current_thread_ptr != new_thread_ptr,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() != Some(SyscallProgress::ThreadExitZombie),
        current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(new_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), new_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(new_thread_ptr).is_init(),
        !old(krnl).thr_mp.spec_index(new_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) is None,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().syscall_progress.view() is None,
        new_thread_lock_perm.state() is WriteLock && new_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        new_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(new_thread_ptr).locking_thread()->Write_lock_id,
        page_ptr_valid(new_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(new_thread_ptr), TypedLockMode::Write),
        thread_page_lock_perm.state() is WriteLock && thread_page_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(new_thread_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock && scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        source_pagetable_ptr != child_pagetable_ptr,
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Write),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, source_pagetable_ptr, old(krnl).pt_mp.spec_index(source_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(source_pagetable_ptr).view().leaves_present(),
        source_pagetable_lock_perm.state() is WriteLock && source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(child_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), child_pagetable_ptr, TypedLockMode::Write),
        pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, child_pagetable_ptr, old(krnl).pt_mp.spec_index(child_pagetable_ptr).view()),
        old(krnl).pt_mp.spec_index(child_pagetable_ptr).view().leaves_present(),
        child_pagetable_lock_perm.state() is WriteLock && child_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        child_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(child_pagetable_ptr).locking_thread()->Write_lock_id,
        endpoint is Some ==> {
            let endpoint_ptr = endpoint->Some_0;
            let owner = old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container;
            let container_ptr = old(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container;
            &&& old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
            &&& old(krnl).ep_mp.dom().contains(endpoint_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
            &&& owner == container_ptr || old(krnl).ctn_mp.spec_index(owner).view_ghost().subtree_set.view().contains(container_ptr)
            &&& endpoint_lock_perm is Some
            &&& endpoint_lock_perm->Some_0.state() is WriteLock && endpoint_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
            &&& endpoint_lock_perm->Some_0.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map().dom() =~= set![parent_process_ptr],
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        final(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        final(lctx).endpoint_lock_map().dom().is_empty(),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).iommu_table_lock_map().dom().is_empty(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { prc_mp: final(krnl).prc_mp, pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, sched_mp: final(krnl).sched_mp, thr_mp: final(krnl).thr_mp,
            ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
            old(krnl).prc_mp.dom().contains(p) ==> if p == child_process_ptr { final(krnl).prc_mp.spec_index(p).locking_thread() is None } else { final(krnl).prc_mp.spec_index(p) == old(krnl).prc_mp.spec_index(p) },
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom(),
        kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, final(krnl).prc_mp),
        forall|p: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(p)]
            old(krnl).thr_mp.dom().contains(p) ==> if p == new_thread_ptr { final(krnl).thr_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).thr_mp.spec_index(p).locking_thread() == old(krnl).thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(p)]
            old(krnl).ep_mp.dom().contains(p) ==> if endpoint == Some(p) { final(krnl).ep_mp.spec_index(p).locking_thread() is None } else { final(krnl).ep_mp.spec_index(p).locking_thread() == old(krnl).ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)]
            old(krnl).pt_mp.dom().contains(p) ==> if p == child_pagetable_ptr || p == source_pagetable_ptr { final(krnl).pt_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).pt_mp.spec_index(p).locking_thread() == old(krnl).pt_mp.spec_index(p).locking_thread() },
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)] old(krnl).pt_mp.dom().contains(p) ==> final(krnl).pt_mp.spec_index(p).view() == old(krnl).pt_mp.spec_index(p).view(),
        final(krnl).sched_mp.dom() == old(krnl).sched_mp.dom(),
        forall|s: RwLockSchedulerPtr| #![trigger scheduler_shards_of(final(krnl).sched_mp.spec_index(s))]
            old(krnl).sched_mp.dom().contains(s) ==> scheduler_shards_of(final(krnl).sched_mp.spec_index(s)) == scheduler_shards_of(old(krnl).sched_mp.spec_index(s)),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            old(krnl).thr_mp.dom().contains(t) ==> {
                &&& final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed()
                &&& t != current_thread_ptr && t != new_thread_ptr ==> final(krnl).thr_mp.spec_index(t).view() == old(krnl).thr_mp.spec_index(t).view()
            },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(current_thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        final(krnl).thr_mp.spec_index(new_thread_ptr).view() == (Thread { endpoint_descriptors: final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors, ..old(krnl).thr_mp.spec_index(new_thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() == if endpoint is Some {
            old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view().update(0, endpoint)
        } else { old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view() },
        final(krnl).ep_mp.dom() == old(krnl).ep_mp.dom(),
        endpoint is Some ==> final(krnl).ep_mp.dom().contains(endpoint->Some_0),
        forall|e: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(e)]
            old(krnl).ep_mp.dom().contains(e) ==> {
                let a = old(krnl).ep_mp.spec_index(e);
                let b = final(krnl).ep_mp.spec_index(e);
                &&& b.view().queue.view() == a.view().queue.view()
                &&& b.view().queue_state == a.view().queue_state
                &&& b.view().owning_threads.view() == if endpoint == Some(e) { a.view().owning_threads.view().insert((new_thread_ptr, 0usize)) } else { a.view().owning_threads.view() }
                &&& b.view().owning_container == a.view().owning_container
                &&& b.being_killed() == a.being_killed()
            },
{
    krnl.wunlock_process(child_process_ptr, Tracked(&mut *lctx), Tracked(child_process_lock_perm));
    krnl.wunlock_pagetable(child_pagetable_ptr, Tracked(&mut *lctx), Tracked(child_pagetable_lock_perm));
    krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(new_thread_ptr), Tracked(&mut *lctx), Tracked(thread_page_lock_perm));
    krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    match endpoint {
        Some(endpoint_ptr) => {
            let tracked endpoint_lock_perm = endpoint_lock_perm.tracked_unwrap();
            attach_endpoint_reference_and_unlock(krnl, new_thread_ptr, endpoint_ptr, current_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm));
        },
        None => krnl.wunlock_thread(new_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm)),
    }
    proof {
        assert(kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, krnl.prc_mp)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    }
}

/// Releases the staging thread, the parent process, both containers, and the cpu, leaving no lock held.
fn release_new_container_caller_side_locks(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, cpu_id: CpuId, parent_container_ptr: RwLockContainerPtr, child_container_ptr: RwLockContainerPtr,
    parent_process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(parent_container_lock_perm): Tracked<LockPerm>,
    Tracked(child_container_lock_perm): Tracked<LockPerm>, Tracked(parent_process_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom() =~= set![parent_container_ptr, child_container_ptr],
        old(lctx).process_lock_map().dom() =~= set![parent_process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr],
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        parent_container_ptr != child_container_ptr,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), parent_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(parent_container_ptr).view_ghost().owned_processes.view().is_empty(),
        parent_container_lock_perm.state() is WriteLock && parent_container_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), child_container_ptr, TypedLockMode::Write),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).being_killed(),
        !old(krnl).ctn_mp.spec_index(child_container_ptr).view_ghost().owned_processes.view().is_empty(),
        child_container_lock_perm.state() is WriteLock && child_container_lock_perm.thread_id() == old(lctx).thread_id(),
        child_container_lock_perm.lock_id() == old(krnl).ctn_mp.spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(parent_process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(parent_process_ptr).view().state.view() is Zombie,
        parent_process_lock_perm.state() is WriteLock && parent_process_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp, cpu_arr: final(krnl).cpu_arr, ..*old(krnl) }),
        forall|p: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(p)]
            old(krnl).ctn_mp.dom().contains(p) ==> if p == child_container_ptr || p == parent_container_ptr { final(krnl).ctn_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).ctn_mp.spec_index(p).locking_thread() == old(krnl).ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
            old(krnl).prc_mp.dom().contains(p) ==> if p == parent_process_ptr { final(krnl).prc_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).prc_mp.spec_index(p).locking_thread() == old(krnl).prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(p)]
            old(krnl).thr_mp.dom().contains(p) ==> if p == current_thread_ptr { final(krnl).thr_mp.spec_index(p).locking_thread() is None }
                else { final(krnl).thr_mp.spec_index(p).locking_thread() == old(krnl).thr_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { final(krnl).cpu_arr.spec_index(i).value.locking_thread() is None } else { final(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(krnl).cpu_arr.spec_index(i).value.locking_thread() },
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            old(krnl).ctn_mp.dom().contains(c) ==> {
                &&& final(krnl).ctn_mp.spec_index(c).view() == old(krnl).ctn_mp.spec_index(c).view()
                &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost() == old(krnl).ctn_mp.spec_index(c).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
            },
        kernel_cpu_nonlock_fields_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr),
        kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, final(krnl).prc_mp),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            old(krnl).thr_mp.dom().contains(t) ==> final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed() && final(krnl).thr_mp.spec_index(t).view() == old(krnl).thr_mp.spec_index(t).view(),
{
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(parent_process_lock_perm));
    krnl.wunlock_container(child_container_ptr, Tracked(&mut *lctx), Tracked(child_container_lock_perm));
    krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(parent_container_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(kernel_cpu_nonlock_fields_unchanged(old(krnl).cpu_arr, krnl.cpu_arr) && kernel_process_nonlock_fields_unchanged(old(krnl).prc_mp, krnl.prc_mp)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); };
    }
}
}
