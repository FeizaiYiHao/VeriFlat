use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_dispatch::running_thread_not_in_endpoint_queue;
use super::syscall_ipc_transition::ipc_schedule_waiting_peer_and_finish;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
/// Runs the pages checks under both write-locked page tables in the implementation's order without recording
/// a step.
#[verifier::spinoff_prover]
fn ipc_check_pages_locked(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr, held_process: RwLockProcessPtr,
    held_endpoint: RwLockEndpointPtr, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(target_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>, caller_thread: RwLockThreadPtr, Ghost(peer_thread): Ghost<RwLockThreadPtr>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        source_thread == caller_thread && target_thread == peer_thread || source_thread == peer_thread && target_thread == caller_thread,
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
            old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)]
            old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
        source_thread != target_thread,
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(caller_thread).view().syscall_progress.view() == Some(SyscallProgress::IpcPages {
            source_range: *source_range, target_range: *target_range, peer: peer_thread, locked: true, released: None,
        }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(held_process),
        old(krnl).thr_mp.spec_index(peer_thread).view().blocking_endpoint_ptr == Some(held_endpoint),
        old(krnl).thr_mp.spec_index(peer_thread).view().syscall_progress.view() is None,
        (source_thread == caller_thread) == (old(krnl).thr_mp.spec_index(peer_thread).view().state is RECEIVING),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        old(krnl).pt_mp.spec_index(source_pagetable).view().leaves_present(),
        old(krnl).pt_mp.spec_index(target_pagetable).view().leaves_present(),
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(held_process),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), held_process, TypedLockMode::Write),
        old(krnl).ep_mp.dom().contains(held_endpoint),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), held_endpoint, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).process_lock_map().dom() =~= set![held_process],
        old(lctx).endpoint_lock_map().dom() =~= set![held_endpoint],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len(),
        ret is Success || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        ({
            let u = final(steps).snapshot_u();
            &&& u.cpu_array[cpu_id as int].current_thread == Some(caller_thread)
            &&& u.thread_map[caller_thread].syscall_progress == final(krnl).thr_mp.spec_index(caller_thread).view().syscall_progress.view()
            &&& ret == ipc_pages_check_result(u, cpu_id)
            &&& ipc_pages_check_step_pre(u, cpu_id)
        }),
        ret is Success ==> {
            &&& share_mapping_4k_source_range_present(final(krnl), source_pagetable, source_range)
            &&& share_mapping_4k_range_owner_compatible(final(krnl), source_pagetable, target_container, source_range)
            &&& thread_effective_quota_4k(final(krnl).thr_mp.spec_index(target_thread)) >= 3 * target_range.len
            &&& final(krnl).pt_mp.spec_index(target_pagetable).view().kernel_l4_end <= spec_v2l4index(target_range.start)
            &&& final(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_empty(target_range.start, target_range.view().spec_index((target_range.len - 1) as int))
            &&& final(krnl).pt_mp.spec_index(target_pagetable).view().spec_mapping_4k_va_range_buildable(target_range)
        },
        final(krnl).thr_mp.spec_index(source_thread).view() == old(krnl).thr_mp.spec_index(source_thread).view(),
        final(krnl).thr_mp.spec_index(target_thread).view() == old(krnl).thr_mp.spec_index(target_thread).view(),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.spec_index(caller_thread).view().syscall_progress.view() == Some(SyscallProgress::IpcPages {
            source_range: *source_range, target_range: *target_range, peer: peer_thread, locked: true, released: None,
        }),
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), held_process, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), held_endpoint, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).prc_mp.spec_index(held_process) == old(krnl).prc_mp.spec_index(held_process),
        final(krnl).ep_mp.spec_index(held_endpoint) == old(krnl).ep_mp.spec_index(held_endpoint),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
{
    proof { use_type_invariant(&*steps); }
    let source_start_indices = va2index(source_range.start);
    proof {
        assert({
            &&& krnl.pt_mp.perms_wf()
            &&& krnl.pt_mp.spec_index(source_pagetable).inv()
            &&& krnl.pt_mp.spec_index(target_pagetable).inv()
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(target_thread).inv()
        }) by { reveal(pagetable_perms_wf); reveal(thread_perms_wf); };
    }
    let source_pt = krnl.pt_mp.borrow_typed(source_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(source_pagetable_lock_perm));
    let range_len = target_range.len;
    let target_thread_ref = krnl.thr_mp.borrow_typed(target_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(target_thread_lock_perm));
    let target_start = target_range.start;
    let target_start_indices = va2index(target_start);
    let target_pt = krnl.pt_mp.borrow_typed(target_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(target_pagetable_lock_perm));
    let target_end_index = range_len - 1;
    let target_end = target_range.index(target_end_index);
    proof {
        assert(target_end == spec_va_add_range(target_start, target_end_index)) by { target_range.va_range_lemma(); };
        assert(target_start <= target_end) by { target_range.va_range_lemma(); };
    }
    let result = if source_start_indices.0 < source_pt.kernel_l4_end {
        RetValueType::Error
    } else if !share_mapping_4k_source_precheck(krnl, source_range, source_pagetable, Tracked(&*lctx), Tracked(source_pagetable_lock_perm)) {
        RetValueType::ErrorIpcSourceUnmapped
    } else if target_thread_ref.quota_4k < 3usize * range_len {
        RetValueType::ErrorNoQuota
    } else if target_start_indices.0 < target_pt.kernel_l4_end {
        RetValueType::Error
    } else if !target_pt.mapping_4k_va_range_empty(target_start, target_end) || !target_pt.mapping_4k_va_range_buildable(target_range) {
        RetValueType::ErrorVaInUse
    } else {
        proof {
            assert({
                &&& krnl.ctn_mp.dom().contains(source_container)
                &&& krnl.ctn_mp.dom().contains(target_container)
                &&& container_perms_wf(krnl.ctn_mp)
                &&& container_tree_wf(krnl.rt_ctn, krnl.ctn_mp)
            }) by { reveal(container_thread_wf); };
        }
        let containers_compatible = if source_container == target_container {
            true
        } else {
            container_tree_check_is_ancestor(krnl.rt_ctn, &krnl.ctn_mp, source_container, target_container)
        };
        let owners_compatible = if containers_compatible {
            proof {
                assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range)) by {
                    source_range.va_range_lemma();
                    reveal(mapped_4k_page_pagetable_wf); reveal(container_process_page_pagetable_wf); reveal(container_page_owner_wf);
                    reveal(container_thread_wf); reveal(process_thread_wf); reveal(process_pagetable_match);
                    reveal(container_perms_wf); reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive);
                };
            }
            true
        } else {
            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl) && kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)
                    && kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by {
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, group_kernel_endpoint_nonlock_fields_unchanged_transitive;
                    reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
                };
            }
            share_mapping_4k_source_owner_precheck(
                krnl, source_range, source_thread, target_thread, target_process, target_container, source_pagetable, target_pagetable, cpu_id,
                Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm),
            )
        };
        if owners_compatible { RetValueType::Success } else { RetValueType::ErrorIpcPageOwnerMismatch }
    };
    let ghost source_process = krnl.thr_mp.spec_index(source_thread).view().owning_proc;
    proof {
        use_type_invariant(&*steps);
        assert({
            &&& held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))
            &&& held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))
            &&& held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))
        }) by { broadcast use group_held_objects_unchanged_transitive; };
        assert({
            &&& krnl.prc_mp.dom().contains(source_process)
            &&& !krnl.prc_mp.spec_index(source_process).view().zombie
            &&& !krnl.prc_mp.spec_index(target_process).view().zombie
            &&& krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable
            &&& krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable
            &&& krnl.ctn_mp.dom().contains(target_container)
        }) by { reveal(process_pagetable_match); reveal(container_thread_wf); };
        assert({
            let u = steps.snapshot_u();
            &&& u.cpu_array[cpu_id as int].current_thread == Some(caller_thread)
            &&& u.thread_map[caller_thread].syscall_progress == krnl.thr_mp.spec_index(caller_thread).view().syscall_progress.view()
            &&& result == ipc_pages_check_result(u, cpu_id)
            &&& ipc_pages_check_step_pre(u, cpu_id)
        }) by {
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, held_process, source_thread, Some(held_endpoint));
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, held_process, target_thread, None);
            kernel_cpu_thread_projection_at(&*krnl, cpu_id, held_process, source_thread, None);
            kernel_cpu_thread_projection_at(&*krnl, cpu_id, held_process, target_thread, None);
            kernel_pagetable_mappings_projection_at(&*krnl, source_process);
            kernel_pagetable_mappings_projection_at(&*krnl, target_process);
            kernel_l4_end_projection_at(&*krnl, source_pagetable);
            kernel_l4_end_projection_at(&*krnl, target_pagetable);
            kernel_container_ancestry_projection_at(&*krnl, target_container);
            ipc_pages_check_step_pre_from_u(steps.snapshot_u(), cpu_id);
        };
    }
    result
}

/// Checks the pages under both write-locked page tables. A passed check records the check step and shares
/// every page; a failed check returns its result without recording a step.
#[verifier::spinoff_prover]
fn ipc_share_pages_locked(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    target_process: RwLockProcessPtr, source_container: RwLockContainerPtr, target_container: RwLockContainerPtr, held_process: RwLockProcessPtr,
    held_endpoint: RwLockEndpointPtr, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, cpu_id: CpuId,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_thread_lock_perm): Tracked<&LockPerm>,
    Tracked(target_thread_lock_perm): Tracked<&LockPerm>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>, caller_thread: RwLockThreadPtr, Ghost(peer_thread): Ghost<RwLockThreadPtr>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        source_thread == caller_thread && target_thread == peer_thread || source_thread == peer_thread && target_thread == caller_thread,
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![source_thread, target_thread],
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread) ==> !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
        source_thread != target_thread,
        source_pagetable != target_pagetable,
        old(krnl).thr_mp.dom().contains(source_thread),
        old(krnl).thr_mp.dom().contains(target_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(caller_thread).view().syscall_progress.view() == Some(SyscallProgress::IpcPages {
            source_range: *source_range, target_range: *target_range, peer: peer_thread, locked: true, released: None,
        }),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(held_process),
        old(krnl).thr_mp.spec_index(peer_thread).view().blocking_endpoint_ptr == Some(held_endpoint),
        old(krnl).thr_mp.spec_index(peer_thread).view().syscall_progress.view() is None,
        (source_thread == caller_thread) == (old(krnl).thr_mp.spec_index(peer_thread).view().state is RECEIVING),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(caller_thread),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).prc_mp.dom().contains(target_process),
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        old(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.state() is WriteLock,
        source_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.state() is WriteLock,
        target_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        old(krnl).pt_mp.spec_index(source_pagetable).view().leaves_present(),
        old(krnl).pt_mp.spec_index(target_pagetable).view().leaves_present(),
        source_pagetable_lock_perm.state() is WriteLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.state() is WriteLock,
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(held_process),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), held_process, TypedLockMode::Write),
        old(krnl).ep_mp.dom().contains(held_endpoint),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), held_endpoint, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).process_lock_map().dom() =~= set![held_process],
        old(lctx).endpoint_lock_map().dom() =~= set![held_endpoint],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).snapshot_k() == *final(krnl),
        ret is Success || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        !(ret is Success) ==> {
            &&& final(steps).view() == old(steps).view()
            &&& ret == ipc_pages_check_result(final(steps).snapshot_u(), cpu_id)
            &&& ipc_pages_check_step_pre(final(steps).snapshot_u(), cpu_id)
        },
        ret is Success ==> {
            let check = final(steps).view()[old(steps).view().len() as int];
            &&& old(steps).view().len() + source_range.len + 1 <= final(steps).view().len() <= old(steps).view().len() + 4 * source_range.len + 1
            &&& forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j]
            &&& ipc_pages_check_result(check.old_u, cpu_id) is Success
            &&& ipc_pages_check_step_pre(check.old_u, cpu_id)
            &&& ipc_pages_check_step(check.old_u, check.new_u, cpu_id)
            &&& forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() < j < final(steps).view().len() ==> share_4k_range_step(final(steps).view()[j], cpu_id)
        },
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), held_process, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), source_thread, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), target_thread, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), held_endpoint, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).prc_mp.spec_index(held_process) == old(krnl).prc_mp.spec_index(held_process),
        final(krnl).ep_mp.spec_index(held_endpoint) == old(krnl).ep_mp.spec_index(held_endpoint),
        final(krnl).thr_mp.spec_index(source_thread).being_killed() == old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().state == old(krnl).thr_mp.spec_index(source_thread).view().state,
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc == old(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(source_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(source_thread).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).being_killed() == old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(target_thread).view().state == old(krnl).thr_mp.spec_index(target_thread).view().state,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == old(krnl).thr_mp.spec_index(target_thread).view().owning_proc,
        final(krnl).thr_mp.spec_index(target_thread).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(target_thread).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(caller_thread).view().syscall_progress.view() == if ret is Success {
            Some(SyscallProgress::Share4k { source_range: *source_range, target_range: *target_range, shared: source_range.len, origin: Share4kOrigin::IpcPages { peer: peer_thread } })
        } else { Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread, locked: true, released: None }) },
        final(krnl).thr_mp.spec_index(peer_thread).view().syscall_progress.view() is None,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        ret is Success ==> old(steps).nonlock_view().len() + source_range.len + 1 <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * source_range.len + 1,
        !(ret is Success) ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len(),
        final(lctx).page_lock_map().dom().is_empty(),
        final(lctx).thread_lock_map().dom() == set![source_thread, target_thread],
        final(lctx).pagetable_lock_map().dom() == set![source_pagetable, target_pagetable],
        final(krnl).thr_mp.dom().contains(source_thread),
        final(krnl).thr_mp.dom().contains(target_thread),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc != target_process,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).prc_mp.dom().contains(target_process),
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container,
        final(krnl).prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable,
        ((final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process && final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), target_process, TypedLockMode::Write)),
        source_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        source_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(source_thread).locking_thread()->Write_lock_id,
        target_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        target_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(target_thread).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, TypedLockMode::Write),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == final(krnl).thr_mp.spec_index(source_thread).view().owning_proc,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        final(krnl).pt_mp.spec_index(source_pagetable).view().leaves_present(),
        final(krnl).pt_mp.spec_index(target_pagetable).view().leaves_present(),
        source_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        source_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id,
        target_pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
        target_pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
{
    let result = ipc_check_pages_locked(
        krnl, source_range, target_range, source_thread, target_thread, target_process, source_container, target_container, held_process, held_endpoint,
        source_pagetable, target_pagetable, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm),
        Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), caller_thread, Ghost(peer_thread),
    );
    match result {
        RetValueType::Success => {},
        _ => { return result; },
    }

    krnl.set_thread_syscall_progress(caller_thread, Ghost(Some(SyscallProgress::Share4k {
        source_range: *source_range, target_range: *target_range, shared: 0, origin: Share4kOrigin::IpcPages { peer: peer_thread },
    })), Tracked(&*lctx), Tracked(if source_thread == caller_thread { source_thread_lock_perm } else { target_thread_lock_perm }));
    proof {
        use_type_invariant(&*steps);
        assert(ipc_pages_check_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id)) by {
            kernel_thread_syscall_progress_changed_implies_u_step(&steps.snapshot_k(), &*krnl, caller_thread);
            ipc_pages_passed_check_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, caller_thread, *source_range, *target_range, peer_thread);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, caller_thread);
        assert(share_mapping_4k_source_range_present(krnl, source_pagetable, source_range)) by { reveal(mapped_4k_page_pagetable_wf); };
        assert(share_mapping_4k_range_owner_compatible(krnl, source_pagetable, target_container, source_range)) by { reveal(container_thread_wf); };
        assert({
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable
            &&& krnl.ctn_mp.dom().contains(target_container)
            &&& krnl.ctn_mp.view().spec_index(target_container).is_init()
            &&& krnl.ctn_mp.view().spec_index(target_container).addr() == target_container
        }) by { reveal(process_pagetable_match); reveal(container_thread_wf); reveal(container_perms_wf); };
    }
    let target_allocator = krnl.ctn_mp.borrow_rodata(target_container).borrow().allocator_ptr_4k;
    proof {
        assert(krnl.allc_4k_mp.dom().contains(target_allocator)) by { reveal(container_allocator_wf); };
        assert({
            &&& share_4k_objects_k(*krnl, cpu_id).source_thread == source_thread && share_4k_objects_k(*krnl, cpu_id).quota_thread == target_thread
            &&& share_4k_objects_k(*krnl, cpu_id).target == target_process && share_4k_objects_k(*krnl, cpu_id).target_container == target_container
            &&& share_4k_objects_k(*krnl, cpu_id).transfer_source is None
        }) by { reveal(share_4k_objects_k); };
    }
    share_mapping_4k_build_and_share(
        krnl, source_range, target_range, target_allocator, source_thread, target_thread, caller_thread, target_process, target_container, cpu_id, source_pagetable,
        target_pagetable, None, Ghost(Share4kOrigin::IpcPages { peer: peer_thread }), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(source_thread_lock_perm), Tracked(target_thread_lock_perm),
        Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(None), Tracked(None),
    );
    proof {
        assert({
            &&& held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx))
            &&& held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx))
            &&& held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx))
        }) by { broadcast use group_held_objects_unchanged_transitive; };
    }
    RetValueType::Success
}

/// Enters a pages rendezvous, locks both page tables, checks and shares the pages, and releases both page
/// tables with the check result.
#[verifier::spinoff_prover]
fn ipc_map_pages_and_release_tables(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, current_thread_lock_perm: Tracked<&LockPerm>, peer_thread_lock_perm: Tracked<&LockPerm>,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot,
    target_process: RwLockProcessPtr, target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot,
    Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
            old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
            old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
            old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
            old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
            } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        current_thread_ptr != peer_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        (source_thread == current_thread_ptr) == (old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        source_process != target_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        (waiting_state is SENDING) == (source_thread == current_thread_ptr),
        ({
            let pre = old(steps).snapshot_u();
            &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
            &&& pre.thread_map[current_thread_ptr].endpoint_descriptors[channel_index as int] == Some(endpoint_ptr)
            &&& pre.endpoint_map[endpoint_ptr].queue[0] == peer_thread_ptr
            &&& pre.thread_map[peer_thread_ptr].ipc_payload == (IPCPayLoad::Pages { va_range: if waiting_state is SENDING { *target_range } else { *source_range } })
            &&& ipc_pages_enter_step_pre(pre, cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range })
        }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() < final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ret is Success || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        ret is Success ==> old(steps).nonlock_view().len() + source_range.len + 4 <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * source_range.len + 4,
        !(ret is Success) ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 3,
        ipc_pages_mapping_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), old(steps).snapshot_u(), cpu_id,
            channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }, ret),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        current_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        peer_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)] t == source_thread || t == target_thread ==> {
            &&& final(krnl).thr_mp.dom().contains(t)
            &&& final(krnl).thr_mp.spec_index(t).being_killed() == old(krnl).thr_mp.spec_index(t).being_killed()
            &&& final(krnl).thr_mp.spec_index(t).view().state == old(krnl).thr_mp.spec_index(t).view().state
            &&& final(krnl).thr_mp.spec_index(t).view().owning_proc == old(krnl).thr_mp.spec_index(t).view().owning_proc
            &&& final(krnl).thr_mp.spec_index(t).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(t).view().blocking_endpoint_ptr
            &&& final(krnl).thr_mp.spec_index(t).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(t).view().temp_alloc_clean()
        },
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages {
            source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, locked: false, released: Some(ret),
        }),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
{
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();
    let ghost range = if waiting_state is SENDING { *source_range } else { *target_range };
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::IpcPages {
        source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, locked: false, released: None,
    })), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        use_type_invariant(&*steps);
        assert({
            &&& steps.snapshot_k().thr_mp.dom().contains(current_thread_ptr)
            &&& steps.snapshot_k().thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None
            &&& ipc_pages_enter_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state, range)
        }) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
            reveal(kernel_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
            kernel_cpu_and_two_threads_lock_modes_changed_implies_u_step(&steps.snapshot_k(), old(krnl), old(lctx), cpu_id, process_ptr, current_thread_ptr, peer_thread_ptr, endpoint_ptr, None);
            kernel_thread_syscall_progress_changed_implies_u_step(old(krnl), &*krnl, current_thread_ptr);
            ipc_pages_enter_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
                channel_index, waiting_state, *source_range, *target_range);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        let ghost entered_k = *krnl;
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
        assert(ipc_pages_trace_after_enter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), old(steps).snapshot_u(), cpu_id, channel_index, waiting_state, range)) by {
            ipc_pages_trace_enter_step(&*steps, old(steps).view(), old(steps).snapshot_u(), kernel_k_to_kernel_u(entered_k), cpu_id, channel_index, waiting_state, range);
        };
        assert({
            &&& krnl.prc_mp.dom().contains(source_process)
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& !krnl.prc_mp.spec_index(source_process).view().zombie
            &&& !krnl.prc_mp.spec_index(target_process).view().zombie
            &&& krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable
            &&& krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable
            &&& krnl.pt_mp.dom().contains(source_pagetable)
            &&& krnl.pt_mp.dom().contains(target_pagetable)
            &&& krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process
            &&& krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process
            &&& source_pagetable != target_pagetable
        }) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
        assert({
            let u = steps.snapshot_u();
            &&& ipc_pages_held(u, cpu_id)
            &&& u.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
            &&& u.thread_map[current_thread_ptr].syscall_progress == Some(SyscallProgress::IpcPages {
                source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, locked: false, released: None,
            })
            &&& u.thread_map[ipc_pages_sender(u, cpu_id)].owning_proc == source_process
            &&& u.thread_map[ipc_pages_receiver(u, cpu_id)].owning_proc == target_process
        }) by {
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, current_thread_ptr, Some(endpoint_ptr));
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, peer_thread_ptr, None);
            kernel_cpu_thread_projection_at(&*krnl, cpu_id, process_ptr, peer_thread_ptr, None);
        };
    }

    let (Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm)) = krnl.wlock_pagetable_pair(source_pagetable, target_pagetable, Tracked(&mut *lctx));
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::IpcPages {
        source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, locked: true, released: None,
    })), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        use_type_invariant(&*steps);
        assert(ipc_pages_lock_tables_step_pre(steps.snapshot_u(), cpu_id) && ipc_pages_lock_tables_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged);
            kernel_pagetable_mappings_projection_at(&steps.snapshot_k(), source_process);
            kernel_pagetable_mappings_projection_at(&steps.snapshot_k(), target_process);
            kernel_pagetable_pair_lock_states_and_progress_changed_implies_u_step(&steps.snapshot_k(), &*krnl, &*lctx, source_process, target_process, source_pagetable, target_pagetable,
                current_thread_ptr, true);
            ipc_pages_lock_tables_step_pre_from_u(steps.snapshot_u(), cpu_id);
            ipc_pages_lock_tables_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, *source_range, *target_range, peer_thread_ptr, source_process, target_process);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        let ghost lock_before = steps.view();
        let ghost lock_pre_u = steps.snapshot_u();
        let ghost locked_k = *krnl;
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
        assert(ipc_pages_trace_after_lock(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), old(steps).snapshot_u(), cpu_id, channel_index, waiting_state, range)) by {
            ipc_pages_trace_lock_step(&*steps, lock_before, old(steps).view().len() as int, old(steps).snapshot_u(), lock_pre_u, kernel_k_to_kernel_u(locked_k), cpu_id, channel_index, waiting_state, range);
        };
        assert({
            &&& krnl.thr_mp.dom().contains(source_thread)
            &&& krnl.thr_mp.dom().contains(target_thread)
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), source_thread, TypedLockMode::Write)
            &&& !krnl.thr_mp.spec_index(source_thread).being_killed()
            &&& typed_lock_map_contains_mode(lctx.thread_lock_map(), target_thread, TypedLockMode::Write)
            &&& !krnl.thr_mp.spec_index(target_thread).being_killed()
            &&& krnl.thr_mp.spec_index(source_thread).view().owning_proc != target_process
            &&& krnl.thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable
            &&& krnl.thr_mp.spec_index(target_thread).view().owning_container == target_container
        }) by { reveal(process_thread_wf); };
        assert({
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().owning_container == target_container
            &&& krnl.prc_mp.spec_index(target_process).view_rodata().view().pagetable == target_pagetable
            &&& {
                ||| {
                    &&& krnl.thr_mp.spec_index(target_thread).view().owning_proc == target_process
                    &&& krnl.thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable
                }
                ||| typed_lock_map_contains_mode(lctx.process_lock_map(), target_process, TypedLockMode::Write)
            }
            &&& krnl.pt_mp.spec_index(source_pagetable).view().proc_ptr == krnl.thr_mp.spec_index(source_thread).view().owning_proc
            &&& krnl.pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process
        }) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread); reveal(process_pagetable_match); };
        assert({
            &&& krnl.pt_mp.dom().contains(source_pagetable)
            &&& krnl.pt_mp.dom().contains(target_pagetable)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), source_pagetable, TypedLockMode::Write)
            &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Write)
            &&& (&source_pagetable_lock_perm).state() is WriteLock
            &&& (&source_pagetable_lock_perm).thread_id() == lctx.thread_id()
            &&& (&source_pagetable_lock_perm).lock_id() == krnl.pt_mp.spec_index(source_pagetable).locking_thread()->Write_lock_id
            &&& (&target_pagetable_lock_perm).state() is WriteLock
            &&& (&target_pagetable_lock_perm).thread_id() == lctx.thread_id()
            &&& (&target_pagetable_lock_perm).lock_id() == krnl.pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id
        }) by { reveal(process_pagetable_match); };
    }
    let ghost share_before = steps.view();
    let result = ipc_share_pages_locked(
        krnl, source_range, target_range, source_thread, target_thread, target_process,
        source_container, target_container, process_ptr, endpoint_ptr,
        source_pagetable, target_pagetable, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(if source_thread == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm }),
        Tracked(if target_thread == current_thread_ptr { current_thread_lock_perm } else { peer_thread_lock_perm }),
        Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm),
        current_thread_ptr, Ghost(peer_thread_ptr),
    );
    proof {
        use_type_invariant(&*steps);
        assert({
            &&& krnl.prc_mp.dom().contains(source_process)
            &&& krnl.prc_mp.dom().contains(target_process)
            &&& !krnl.prc_mp.spec_index(source_process).view().zombie
            &&& !krnl.prc_mp.spec_index(target_process).view().zombie
            &&& krnl.prc_mp.spec_index(source_process).view().pagetable == source_pagetable
            &&& krnl.prc_mp.spec_index(target_process).view().pagetable == target_pagetable
            &&& krnl.ctn_mp.dom().contains(target_container)
        }) by { reveal(process_thread_wf); reveal(process_pagetable_match); reveal(container_thread_wf); };
        assert({
            let u = steps.snapshot_u();
            &&& u.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
            &&& u.thread_map[current_thread_ptr].syscall_progress == krnl.thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            &&& !(result is Success) ==> {
                &&& u.thread_map[ipc_pages_sender(u, cpu_id)].owning_proc == source_process
                &&& u.thread_map[ipc_pages_receiver(u, cpu_id)].owning_proc == target_process
            }
            &&& result is Success ==> {
                &&& ipc_pages_unlock_tables_step_pre(u, cpu_id)
                &&& share_4k_objects(u, cpu_id).target == target_process
                &&& u.thread_map[share_4k_objects(u, cpu_id).source_thread].owning_proc == source_process
            }
        }) by {
            reveal(share_4k_objects_k);
            kernel_cpu_thread_projection_at(&*krnl, cpu_id, process_ptr, current_thread_ptr, None);
            kernel_cpu_thread_projection_at(&*krnl, cpu_id, process_ptr, peer_thread_ptr, None);
            if result is Success { kernel_share_4k_objects_projection(&*krnl, &*lctx, cpu_id); }
            kernel_pagetable_mappings_projection_at(&*krnl, source_process);
            kernel_pagetable_mappings_projection_at(&*krnl, target_process);
            kernel_write_held_pagetable_mode(&*krnl, &*lctx, source_pagetable);
            kernel_write_held_pagetable_mode(&*krnl, &*lctx, target_pagetable);
            if result is Success { ipc_pages_unlock_tables_step_pre_from_u(steps.snapshot_u(), cpu_id); }
        };
        assert(result is Success ==> ipc_pages_trace_after_share(steps.view(), old(steps).view().len() as int, old(steps).snapshot_u(), cpu_id, channel_index, waiting_state, range)) by {
            if result is Success {
                ipc_pages_trace_share_steps(&*steps, share_before, old(steps).view().len() as int, old(steps).snapshot_u(), cpu_id, channel_index, waiting_state, range);
            }
        };
    }
    if source_pagetable < target_pagetable {
        krnl.wunlock_pagetable(target_pagetable, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
        krnl.wunlock_pagetable(source_pagetable, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    } else {
        krnl.wunlock_pagetable(source_pagetable, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_pagetable(target_pagetable, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    }
    proof { vstd::assert_maps_equal!(lctx.pagetable_lock_map(), old(lctx).pagetable_lock_map(), p => {}); }
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::IpcPages {
        source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, locked: false, released: Some(result),
    })), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        use_type_invariant(&*steps);
        let ghost unlock_before = steps.view();
        let ghost unlock_pre_u = steps.snapshot_u();
        let ghost unlocked_k = *krnl;
        assert(if result is Success {
            ipc_pages_unlock_tables_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id)
        } else { ipc_pages_check_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id) }) by {
            kernel_pagetable_pair_lock_states_and_progress_changed_implies_u_step(&steps.snapshot_k(), &*krnl, &*lctx, source_process, target_process, source_pagetable, target_pagetable,
                current_thread_ptr, false);
            if result is Success {
                ipc_pages_unlock_tables_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, *source_range, *target_range, peer_thread_ptr, source_process, target_process);
            } else {
                ipc_pages_failed_check_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, *source_range, *target_range, peer_thread_ptr, result, source_process, target_process);
            }
        };
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
        assert(ipc_pages_mapping_trace(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), old(steps).snapshot_u(), cpu_id, channel_index, waiting_state, range, result)) by {
            if result is Success {
                ipc_pages_trace_unlock_step(&*steps, unlock_before, old(steps).view().len() as int, old(steps).snapshot_u(), unlock_pre_u, kernel_k_to_kernel_u(unlocked_k), cpu_id, channel_index, waiting_state, range);
            } else {
                ipc_pages_trace_failed_check_step(&*steps, unlock_before, old(steps).view().len() as int, old(steps).snapshot_u(), unlock_pre_u, kernel_k_to_kernel_u(unlocked_k), cpu_id, channel_index,
                    waiting_state, range, result);
            }
        };
    }
    result
}

pub(super) fn ipc_rendezvous_pages(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_lock_perm: Tracked<LockPerm>,
    process_lock_perm: Tracked<LockPerm>, current_thread_lock_perm: Tracked<LockPerm>, endpoint_lock_perm: Tracked<LockPerm>,
    peer_thread_lock_perm: Tracked<LockPerm>, Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>,
) -> (ret: RetValueType)
    requires
        old(krnl).inv(),
        edp_idx_valid(channel_index),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()[channel_index as int] == Some(endpoint_ptr),
        waiting_state is SENDING || waiting_state is RECEIVING,
        (old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue_state is SEND) != (waiting_state is SENDING),
        forall|p: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ctn_mp.spec_index(p)]
            old(steps).snapshot_k().ctn_mp.dom().contains(p) && old(krnl).ctn_mp.dom().contains(p) ==> if old(lctx).container_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ctn_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(p).locking_thread() },
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] #![trigger old(steps).snapshot_k().prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) && old(krnl).prc_mp.dom().contains(p) ==> if old(lctx).process_lock_map().dom().contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(p)] #![trigger old(steps).snapshot_k().thr_mp.spec_index(p)]
            old(steps).snapshot_k().thr_mp.dom().contains(p) && old(krnl).thr_mp.dom().contains(p) ==> if old(lctx).thread_lock_map().dom().contains(p) {
                old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger old(krnl).ep_mp.spec_index(p)] #![trigger old(steps).snapshot_k().ep_mp.spec_index(p)]
            old(steps).snapshot_k().ep_mp.dom().contains(p) && old(krnl).ep_mp.dom().contains(p) ==> if old(lctx).endpoint_lock_map().dom().contains(p) {
                old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).ep_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().ep_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] #![trigger old(steps).snapshot_k().pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && old(krnl).pt_mp.dom().contains(p) ==> if old(lctx).pagetable_lock_map().dom().contains(p) {
                old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).pt_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(p).locking_thread() },
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] #![trigger old(steps).snapshot_k().it_mp.spec_index(p)]
            old(steps).snapshot_k().it_mp.dom().contains(p) && old(krnl).it_mp.dom().contains(p) ==> if old(lctx).iommu_table_lock_map().dom().contains(p) {
                old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).it_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().it_mp.spec_index(p).locking_thread() },
        forall|i: CpuId| #![trigger old(krnl).cpu_arr.spec_index(i)] #![trigger old(steps).snapshot_k().cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if old(lctx).cpu_lock_map().dom().contains(i) {
                old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() is None
            } else { old(krnl).cpu_arr.spec_index(i).value.locking_thread() == old(steps).snapshot_k().cpu_arr.spec_index(i).value.locking_thread() },
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        current_thread_ptr != peer_thread_ptr,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
        process_lock_perm.view().state() is WriteLock,
        process_lock_perm.view().thread_id() == old(lctx).thread_id(),
        process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == false,
        current_thread_lock_perm.view().state() is WriteLock,
        current_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.view().state() is WriteLock,
        endpoint_lock_perm.view().thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.view().lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).being_killed() == false,
        peer_thread_lock_perm.view().state() is WriteLock,
        peer_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        (source_thread == current_thread_ptr) == (old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
        (source_thread == current_thread_ptr) == (waiting_state is SENDING),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().ipc_payload == (IPCPayLoad::Pages { va_range: if source_thread == current_thread_ptr { *target_range } else { *source_range } }),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.len() != 0,
        old(krnl).ep_mp.spec_index(endpoint_ptr).view().queue.view().spec_index(0) == peer_thread_ptr,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).cpu_set_mp == old(steps).snapshot_k().cpu_set_mp,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        source_thread != target_thread,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
    ensures
        old(steps).view().len() < final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ipc_pages_rendezvous_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            old(steps).snapshot_u(), kernel_k_to_kernel_u(*final(krnl)), cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Success || ret is ErrorIpcSameProcess || ret is ErrorIpcSourceUnmapped || ret is ErrorIpcPageOwnerMismatch || ret is ErrorNoQuota || ret is ErrorVaInUse || ret is Error,
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        ret is Success ==> old(steps).nonlock_view().len() + source_range.len + 5 <= final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 4 * source_range.len + 5,
        ret is ErrorIpcSameProcess ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        !(ret is Success) && !(ret is ErrorIpcSameProcess) ==> final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 4,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
{
    proof { use_type_invariant(&*steps); }
    assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };

    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked process_lock_perm = process_lock_perm.get();
    let tracked current_thread_lock_perm = current_thread_lock_perm.get();
    let tracked endpoint_lock_perm = endpoint_lock_perm.get();
    let tracked peer_thread_lock_perm = peer_thread_lock_perm.get();

    proof {
        assert({
            &&& krnl.thr_mp.perms_wf()
            &&& krnl.thr_mp.spec_index(current_thread_ptr).is_init()
            &&& krnl.thr_mp.spec_index(peer_thread_ptr).is_init()
        }) by { reveal(thread_perms_wf); };
    }
    let source_process;
    let source_container;
    let source_pagetable;
    if source_thread == current_thread_ptr {
        let source_thread_ref = krnl.thr_mp.borrow_typed(source_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
        source_process = source_thread_ref.owning_proc;
        source_container = source_thread_ref.owning_container;
        source_pagetable = source_thread_ref.proc_pagetable_ptr;
    } else {
        let source_thread_ref = krnl.thr_mp.borrow_typed(source_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        source_process = source_thread_ref.owning_proc;
        source_container = source_thread_ref.owning_container;
        source_pagetable = source_thread_ref.proc_pagetable_ptr;
    }
    let target_process;
    let target_container;
    let target_pagetable;
    if target_thread == current_thread_ptr {
        let target_thread_ref = krnl.thr_mp.borrow_typed(target_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
        target_process = target_thread_ref.owning_proc;
        target_container = target_thread_ref.owning_container;
        target_pagetable = target_thread_ref.proc_pagetable_ptr;
    } else {
        let target_thread_ref = krnl.thr_mp.borrow_typed(target_thread, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&peer_thread_lock_perm));
        target_process = target_thread_ref.owning_proc;
        target_container = target_thread_ref.owning_container;
        target_pagetable = target_thread_ref.proc_pagetable_ptr;
    }

    if source_process == target_process {
        let ghost payload = IPCPayLoad::Pages { va_range: if waiting_state is SENDING { *source_range } else { *target_range } };
        proof {
            use_type_invariant(&*steps);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(RetValueType::ErrorIpcSameProcess == ipc_rendezvous_result(kernel_k_to_kernel_u(steps.snapshot_k()), cpu_id, channel_index, waiting_state, payload)) by {
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
                reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged);
                kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, current_thread_ptr, Some(endpoint_ptr));
                kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, peer_thread_ptr, None);
            };
        }
        let ret = ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(Some((channel_index, waiting_state, payload))), peer_thread_ptr,
            RetValueType::ErrorIpcSameProcess, Tracked(cpu_lock_perm), Tracked(process_lock_perm),
            Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm), Tracked(peer_thread_lock_perm),
        );
        proof { ipc_rendezvous_trace_error_step(&*steps, old(steps).view(), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state, payload, ret); }
        ret
    } else {
        proof {
            assert({
                let pre = steps.snapshot_u();
                &&& pre.cpu_array[cpu_id as int].current_process == Some(process_ptr)
                &&& pre.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
                &&& pre.thread_map[current_thread_ptr].endpoint_descriptors[channel_index as int] == Some(endpoint_ptr)
                &&& pre.endpoint_map[endpoint_ptr].queue[0] == peer_thread_ptr
                &&& pre.thread_map[peer_thread_ptr].ipc_payload == (IPCPayLoad::Pages { va_range: if waiting_state is SENDING { *target_range } else { *source_range } })
                &&& ipc_pages_enter_step_pre(pre, cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range })
            }) by {
                running_thread_not_in_endpoint_queue(&*krnl, endpoint_ptr, current_thread_ptr); container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, peer_thread_ptr);
                container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, current_thread_ptr);
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
                reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_endpoint_nonlock_fields_unchanged); reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
                kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, current_thread_ptr, Some(endpoint_ptr));
                kernel_cpu_thread_projection_at(&steps.snapshot_k(), cpu_id, process_ptr, peer_thread_ptr, None);
                ipc_pages_enter_step_pre_from_u(steps.snapshot_u(), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, channel_index, waiting_state,
                    if waiting_state is SENDING { *source_range } else { *target_range }, if waiting_state is SENDING { *target_range } else { *source_range });
            };
        }
        let result = ipc_map_pages_and_release_tables(
            krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr,
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(&current_thread_lock_perm), Tracked(&peer_thread_lock_perm),
            source_process, source_container, source_pagetable, target_process, target_container, target_pagetable, Ghost(channel_index), Ghost(waiting_state),
        );
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let ghost finish_before = steps.view();
        let ghost finish_pre_u = kernel_k_to_kernel_u(*krnl);
        let ret = ipc_schedule_waiting_peer_and_finish(
            krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, Ghost(None), peer_thread_ptr,
            result, Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(current_thread_lock_perm), Tracked(endpoint_lock_perm),
            Tracked(peer_thread_lock_perm),
        );
        proof {
            ipc_pages_rendezvous_trace_finish_step(&*steps, finish_before, old(steps).view().len() as int, old(steps).snapshot_u(), finish_pre_u, kernel_k_to_kernel_u(*krnl), cpu_id, channel_index, waiting_state,
                if waiting_state is SENDING { *source_range } else { *target_range }, result);
        }
        ret
    }
}
} // verus!
