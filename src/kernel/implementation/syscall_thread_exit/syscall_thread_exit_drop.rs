use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;

verus! {
/// Release descriptor `index` of the exiting thread: clear it, record the position after it, drop the reference of its
/// write-held endpoint, and release the endpoint.
fn thread_exit_drop_descriptor(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, index: EndpointIdx,
    Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING,
        old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[index as int] == Some(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.state() is WriteLock,
        endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_removed(old(lctx), final(lctx), KernelObjId::Endpoint(endpoint_ptr)),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, ep_mp: final(krnl).ep_mp, ..*old(krnl) }),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
            endpoint_descriptors: final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
            syscall_progress: Ghost(Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx })), ..old(krnl).thr_mp.spec_index(thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view().update(index as int, None),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
        final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, endpoint_ptr),
        final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state == old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state,
        final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container,
        final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view() == old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().remove((thread_ptr, index)),
        final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread() is None,
        final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed() == old(krnl).ep_mp.spec_index(endpoint_ptr).being_killed(),
{
    proof {
        thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((thread_ptr, index))) by {
            reveal(thread_endpoint_ref_counter_wf);
        };
        endpoint_perms_wf_at(krnl.ep_mp, endpoint_ptr);
        vstd::set::lemma_set_remove_len(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view(), (thread_ptr, index));
    }
    {
        let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        thread_mut.endpoint_descriptors.set(index, None);
        thread_mut.syscall_progress = Ghost(Some(SyscallProgress::ThreadExit { next: (index + 1) as EndpointIdx }));
    } {
        let endpoint_mut = krnl.ep_mp.borrow_mut_typed(endpoint_ptr, Ghost(lctx.endpoint_lock_map()), Tracked(&*lctx), Tracked(&endpoint_lock_perm));
        endpoint_mut.rf_counter = endpoint_mut.rf_counter - 1;
        endpoint_mut.owning_threads = Ghost(endpoint_mut.owning_threads.view().remove((thread_ptr, index)));
    }
    proof {
        assert(typed_lock_maps_aligned(krnl, lctx) && krnl.thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr)) by {
            lock_id_fields_eq_imply_eq(); reveal(LockedMap::typed_lock_map_aligned);
        };
        assert(krnl.subsystems_inv()) by {
            assert(thread_perms_wf(krnl.thr_mp)) by {
                reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_syscall_progress_only_when_wlocked);
            };
            assert(endpoint_perms_wf(krnl.ep_mp)) by { reveal(endpoint_perms_wf); };
            reveal(KernelK::default_pagetable_wf);
        };
        assert(krnl.memory_management_inv()) by { memory_management_inv_preserved_for_thread_endpoint_memory_fields(*old(krnl), *krnl); };
        assert(krnl.process_management_inv()) by {
            assert(thread_caller_callee_wf(krnl.thr_mp)) by { thread_caller_callee_wf_preserved_for_call_link_eq(old(krnl).thr_mp, krnl.thr_mp); };
            assert(container_endpoint_wf(krnl.ctn_mp, krnl.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).ep_mp, krnl.ep_mp); };
            assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { reveal(thread_endpoint_ref_counter_wf); };
            assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_queue_fields(old(krnl).thr_mp, krnl.thr_mp, old(krnl).ep_mp, krnl.ep_mp); };
            assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { reveal(container_thread_endpoint_wf); reveal(thread_endpoint_ref_counter_wf); };
            assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.sched_mp); };
            assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp); };
            assert(process_thread_wf(krnl.prc_mp, krnl.thr_mp)) by { process_thread_wf_preserved_for_process_thread_link_eq(old(krnl).prc_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp); reveal(process_empty_lists_wlocked); };
            assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { thread_cpu_wf_preserved_for_running_thread_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).cpu_arr, krnl.cpu_arr); };
        };
    }
    krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
}

/// Release every descriptor of the running exiting thread, one step per descriptor holding an endpoint. The cpu, the
/// container, the process, and the thread stay write-held; the thread ends without descriptors and records the position
/// after the last released one.
pub(super) fn thread_exit_drop_descriptors(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, container_ptr: RwLockContainerPtr,
    process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, Tracked(thread_lock_perm): Tracked<&LockPerm>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        thread_exit_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom() =~= set![container_ptr],
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
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
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExit { next: 0 }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        thread_exit_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
            endpoint_descriptors: final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
            syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() matches Some(SyscallProgress::ThreadExit { .. }),
        forall|j: int| #![trigger final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
            0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
{
    let ghost mut recorded: EndpointIdx = 0;
    let mut index: EndpointIdx = 0;
    proof { thread_perms_wf_at(krnl.thr_mp, thread_ptr); }
    while index < MAX_NUM_ENDPOINT_DESCRIPTORS
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom() =~= set![container_ptr],
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
            old(lctx).page_lock_map().dom().is_empty(),
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
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == container_ptr,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().inv(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            steps.snapshot_k() == *krnl,
            0 <= start <= old(steps).view().len() <= steps.view().len(),
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, steps.view()),
            recorded <= index <= MAX_NUM_ENDPOINT_DESCRIPTORS,
            thread_exit_partial_trace(steps.view().subrange(start, steps.view().len() as int), pre, cpu_id),
            krnl.cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
            krnl.prc_mp.dom().contains(process_ptr),
            krnl.prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                endpoint_descriptors: krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
                syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view()
            }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::ThreadExit { next: recorded }),
            forall|j: int| #![trigger krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j]]
                0 <= j < index ==> krnl.thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.view()[j] is None,
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        decreases MAX_NUM_ENDPOINT_DESCRIPTORS - index,
    {
        proof { thread_perms_wf_at(krnl.thr_mp, thread_ptr); }
        let descriptor = *krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm)).endpoint_descriptors.get(index);
        if let Some(endpoint_ptr) = descriptor {
            proof { assert(krnl.ep_mp.dom().contains(endpoint_ptr)) by { reveal(thread_endpoint_ref_counter_wf); }; }
            let ghost drop_pre = *krnl;
            let ghost drop_lctx = *lctx;
            let ghost drop_before = steps.view();
            let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));
            thread_exit_drop_descriptor(krnl, Tracked(&mut *lctx), thread_ptr, endpoint_ptr, index, Tracked(thread_lock_perm), Tracked(endpoint_lock_perm));
            proof {
                let drop_post = *krnl;
                use_type_invariant(&*steps);
                assert(thread_exit_drop_step_pre(kernel_k_to_kernel_u(drop_pre), cpu_id) && thread_exit_drop_step(kernel_k_to_kernel_u(drop_pre), kernel_k_to_kernel_u(drop_post), cpu_id)) by {
                    kernel_write_held_context_projection(&drop_pre, &drop_lctx, cpu_id, process_ptr, thread_ptr, None);
                    kernel_cpu_thread_projection_at(&drop_pre, cpu_id, process_ptr, thread_ptr, Some(endpoint_ptr));
                    kernel_thread_exit_descriptor_dropped_implies_u_step(&drop_pre, &drop_post, thread_ptr, endpoint_ptr, index);
                    thread_exit_drop_step_from_u(kernel_k_to_kernel_u(drop_pre), kernel_k_to_kernel_u(drop_post), cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_ptr, recorded, index);
                };
                assert(lctx.endpoint_lock_map() =~= old(lctx).endpoint_lock_map());
                krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
                thread_exit_trace_push(&*steps, drop_before, start, pre, kernel_k_to_kernel_u(drop_pre), kernel_k_to_kernel_u(drop_post), cpu_id);
                recorded = (index + 1) as EndpointIdx;
            }
        }
        index = index + 1;
    }
}

} // verus!
