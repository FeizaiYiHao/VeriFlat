use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_commit::commit_new_container;
use super::syscall_new_container_spec::*;
use super::syscall_new_container_trace::*;

verus! {
/// Relocking one cpu set back to its original lock mode keeps every container field, quota, and cpu-set lock mode.
proof fn container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock(pre: &KernelK, post: &KernelK, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        container_cpu_set_wf(pre.ctn_mp, pre.cpu_set_mp),
        *post == (KernelK { cpu_set_mp: post.cpu_set_mp, ..*pre }),
        post.cpu_set_mp.unchanged_except(&pre.cpu_set_mp, cpu_set_ptr),
        post.cpu_set_mp.spec_index(cpu_set_ptr).lock_state_u() == pre.cpu_set_mp.spec_index(cpu_set_ptr).lock_state_u(),
    ensures kernel_container_nonlock_fields_and_quotas_unchanged(pre, post),
{
    reveal(kernel_container_nonlock_fields_and_quotas_unchanged); reveal(container_cpu_set_wf);
}

/// Exec state handed from the lock-and-check prefix of `syscall_new_container` to its commit.
pub(super) struct NewContainerEntryLocked {
    pub parent_container_ptr: RwLockContainerPtr, pub parent_process_ptr: RwLockProcessPtr, pub current_thread_ptr: RwLockThreadPtr,
    pub source_pagetable_ptr: RwLockPageTableRoot, pub parent_cpu_set: RwLockCpuSetPtr, pub source_range: VaRange4K,
    pub cpu_lock_perm: Tracked<LockPerm>, pub container_lock_perm: Tracked<LockPerm>, pub process_lock_perm: Tracked<LockPerm>,
    pub thread_lock_perm: Tracked<LockPerm>, pub source_pagetable_lock_perm: Tracked<LockPerm>, pub cpu_set_lock_perm: Tracked<LockPerm>,
}

/// Validates the arguments and locks the cpu, its container, process, thread, source pagetable, and cpu set, rejecting
/// every failing check with all locks released and a stutter trace; otherwise the six locks are returned held with
/// exactly the state `commit_new_container` requires, and the syscall result is pinned to Success.
#[verifier::spinoff_prover]
fn new_container_lock_entry(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, initial_regs: &Registers,
) -> (ret: Result<NewContainerEntryLocked, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        ret is Err ==> ({
            let r = ret->Err_0;
            &&& new_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, r)
            &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& final(lctx).no_locks_held()
            &&& final(steps).nonlock_view().len() == 0
            &&& !(r is SuccessThreeUsize)
            &&& !(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is Success)
            &&& r == new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id)
        }),
        ret is Ok ==> ({
            let e = ret->Ok_0;
            &&& *final(steps) == *old(steps)
            &&& e.source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })
            &&& new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is Success
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, ctn_mp: final(krnl).ctn_mp, prc_mp: final(krnl).prc_mp,
                thr_mp: final(krnl).thr_mp, pt_mp: final(krnl).pt_mp, cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) })
            &&& final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).ctn_mp.unchanged_except(&old(krnl).ctn_mp, e.parent_container_ptr)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, e.parent_process_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, e.current_thread_ptr)
            &&& final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, e.source_pagetable_ptr)
            &&& old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None
            &&& old(krnl).ctn_mp.spec_index(e.parent_container_ptr).locking_thread() is None
            &&& old(krnl).prc_mp.spec_index(e.parent_process_ptr).locking_thread() is None
            &&& old(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread() is None
            &&& old(krnl).pt_mp.spec_index(e.source_pagetable_ptr).locking_thread() is None
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(e.current_thread_ptr)
            &&& pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, e.source_pagetable_ptr, final(krnl).pt_mp.spec_index(e.source_pagetable_ptr).view())
            &&& final(krnl).pt_mp.spec_index(e.source_pagetable_ptr).view().leaves_present()
            &&& final(krnl).inv()
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &KernelK { cpu_set_mp: old(krnl).cpu_set_mp, ..*final(krnl) })
            &&& final(krnl).cpu_set_mp.unchanged_except(&old(krnl).cpu_set_mp, e.parent_cpu_set)
            &&& old(krnl).cpu_set_mp.spec_index(e.parent_cpu_set).locking_thread() is None
            &&& cpu_id == final(lctx).cpu_id()
            &&& final(krnl).cpu_published[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)
            &&& process_quota_4k <= funding_page_count
            &&& funding_page_count <= usize::MAX - 9 - 3 * e.source_range.len
            &&& e.source_range.wf()
            &&& e.source_range.len > 0
            &&& e.source_range.len <= (usize::MAX - 9) / 3
            &&& index_valid(NUM_CPUS, transfer_cpu_id)
            &&& final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == e.parent_container_ptr
            &&& transfer_cpu_id != cpu_id
            &&& final(krnl).cpu_set_mp.dom().contains(e.parent_cpu_set)
            &&& final(krnl).cpu_set_mp.spec_index(e.parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id)
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata().view().cpu_set == e.parent_cpu_set
            &&& typed_lock_map_contains_mode(final(lctx).cpu_set_lock_map(), e.parent_cpu_set, TypedLockMode::Write)
            &&& e.cpu_set_lock_perm@.state() is WriteLock
            &&& e.cpu_set_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& e.cpu_set_lock_perm@.lock_id() == final(krnl).cpu_set_mp.spec_index(e.parent_cpu_set).locking_thread()->Write_lock_id
            &&& final(krnl).pt_mp.spec_index(e.source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(e.source_range.start)
            &&& share_mapping_4k_source_range_present(final(krnl), e.source_pagetable_ptr, &e.source_range)
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom() =~= set![e.parent_container_ptr]
            &&& final(lctx).process_lock_map().dom() =~= set![e.parent_process_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![e.current_thread_ptr]
            &&& final(lctx).endpoint_lock_map().dom().is_empty()
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom().is_empty()
            &&& final(lctx).cpu_set_lock_map().dom() =~= set![e.parent_cpu_set]
            &&& final(lctx).pagetable_lock_map().dom() =~= set![e.source_pagetable_ptr]
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_MAJOR)
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& !final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == e.parent_container_ptr
            &&& e.cpu_lock_perm@.state() is WriteLock
            &&& e.cpu_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& e.cpu_lock_perm@.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& final(krnl).ctn_mp.dom().contains(e.parent_container_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).container_lock_map(), e.parent_container_ptr, TypedLockMode::Write)
            &&& !final(krnl).ctn_mp.spec_index(e.parent_container_ptr).being_killed()
            &&& final(krnl).ctn_mp.spec_index(e.parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH
            &&& e.container_lock_perm@.state() is WriteLock
            &&& e.container_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& e.container_lock_perm@.lock_id() == final(krnl).ctn_mp.spec_index(e.parent_container_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).prc_mp.dom().contains(e.parent_process_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), e.parent_process_ptr, TypedLockMode::Write)
            &&& !final(krnl).prc_mp.spec_index(e.parent_process_ptr).being_killed()
            &&& final(krnl).prc_mp.spec_index(e.parent_process_ptr).view_rodata().view().owning_container == e.parent_container_ptr
            &&& e.process_lock_perm@.state() is WriteLock
            &&& e.process_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& e.process_lock_perm@.lock_id() == final(krnl).prc_mp.spec_index(e.parent_process_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).thr_mp.dom().contains(e.current_thread_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), e.current_thread_ptr, TypedLockMode::Write)
            &&& !final(krnl).thr_mp.spec_index(e.current_thread_ptr).being_killed()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().owning_container == e.parent_container_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().owning_proc == e.parent_process_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().proc_pagetable_ptr == e.source_pagetable_ptr
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id: cpu_id })
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().syscall_progress.view() is None
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().free_quota_pending_clean()
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().quota_4k >= 9 + funding_page_count + 3 * e.source_range.len
            &&& final(krnl).thr_mp.spec_index(e.current_thread_ptr).view().quota_2m >= 2
            &&& e.thread_lock_perm@.state() is WriteLock
            &&& e.thread_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& e.thread_lock_perm@.lock_id() == final(krnl).thr_mp.spec_index(e.current_thread_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).pt_mp.dom().contains(e.source_pagetable_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), e.source_pagetable_ptr, TypedLockMode::Write)
            &&& e.source_pagetable_lock_perm@.state() is WriteLock
            &&& e.source_pagetable_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& e.source_pagetable_lock_perm@.lock_id() == final(krnl).pt_mp.spec_index(e.source_pagetable_ptr).locking_thread()->Write_lock_id
        }),
{
    proof { use_type_invariant(&*steps); }
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if range == 0 || range > usize::MAX / 4096usize || range > (usize::MAX - 9usize) / 3usize || !va_4k_valid(va) || transfer_cpu_id >= NUM_CPUS {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }
    let source_range = VaRange4K::new(va, range);
    if process_quota_4k > funding_page_count || funding_page_count > usize::MAX - 9 - 3 * range {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }

    proof {
        assert({
            &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some
            &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread is Some
        }) by { reveal(cpu_array_wf); };
    }
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_container_ptr = cpu.owning_container();
    let parent_process_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    proof {
        assert(krnl.ctn_mp.dom().contains(parent_container_ptr)) by { reveal(container_cpu_wf); };
        assert({
            &&& krnl.prc_mp.dom().contains(parent_process_ptr)
            &&& krnl.prc_mp.spec_index(parent_process_ptr).view_rodata().view().owning_container == parent_container_ptr
            &&& !krnl.prc_mp.spec_index(parent_process_ptr).view().zombie
        }) by { reveal(process_cpu_wf); };
        assert({
            &&& krnl.thr_mp.dom().contains(current_thread_ptr)
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == parent_container_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_process_ptr
        }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
    }
    let container_res = krnl.wlock_container_unless_killed(parent_container_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::ErrorContainerKilled);
            assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is ErrorContainerKilled) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); kernel_container_projection_at(old(krnl), parent_container_ptr);
            };
        }
        return Err(RetValueType::ErrorContainerKilled);
    }
    let Tracked(container_lock_perm) = container_res.unwrap();
    proof { assert(!krnl.ctn_mp.spec_index(parent_container_ptr).view_ghost().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
    let parent_depth = krnl.ctn_mp.borrow_rodata(parent_container_ptr).borrow().depth;
    if parent_depth >= MAX_CONTAINER_TREE_DEPTH {
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::Error);
            assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is Error) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); kernel_container_projection_at(old(krnl), parent_container_ptr);
            };
        }
        return Err(RetValueType::Error);
    }

    let process_res = krnl.wlock_process_unless_killed(parent_process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::ErrorProcessKilled);
            assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is ErrorProcessKilled) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); kernel_container_projection_at(old(krnl), parent_container_ptr);
            };
        }
        return Err(RetValueType::ErrorProcessKilled);
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    proof { assert(krnl.prc_mp.spec_index(parent_process_ptr).view().owned_threads.view().len() != 0) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread_ptr); }; }
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::ErrorThreadKilled);
            assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is ErrorThreadKilled) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); kernel_container_projection_at(old(krnl), parent_container_ptr);
            };
        }
        return Err(RetValueType::ErrorThreadKilled);
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    let thread = krnl.thr_mp.borrow_typed(
        current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let quota_4k = thread.quota_4k;
    let quota_2m = thread.quota_2m;
    let source_pagetable_ptr = thread.proc_pagetable_ptr;
    let required_4k = 9usize + funding_page_count + 3 * range;
    let quota_available = quota_4k >= required_4k && quota_2m >= 2;
    if !quota_available {
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::ErrorNoQuota);
            assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is ErrorNoQuota) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); kernel_container_projection_at(old(krnl), parent_container_ptr);
            };
        }
        return Err(RetValueType::ErrorNoQuota);
    }

    proof {
        assert({
            &&& krnl.pt_mp.dom().contains(source_pagetable_ptr)
            &&& !lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr)
            &&& krnl.prc_mp.spec_index(parent_process_ptr).view().pagetable == source_pagetable_ptr
        }) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
    }
    let Tracked(source_pagetable_lock_perm) = krnl.wlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx));
    let source_start_indices = va2index(va);
    proof { assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); }; }
    let source_pt = krnl.pt_mp.borrow_typed(source_pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(&source_pagetable_lock_perm));
    let source_ready = if source_start_indices.0 < source_pt.kernel_l4_end {
        false
    } else {
        share_mapping_4k_source_precheck(krnl, &source_range, source_pagetable_ptr, Tracked(&*lctx), Tracked(&source_pagetable_lock_perm))
    };
    if !source_ready {
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                RetValueType::Error);
            assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is Error) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); kernel_container_projection_at(old(krnl), parent_container_ptr);
                kernel_l4_end_projection_at(old(krnl), source_pagetable_ptr); kernel_pagetable_mappings_projection_at(old(krnl), parent_process_ptr);
            };
        }
        return Err(RetValueType::Error);
    }
    let parent_cpu_set = krnl.ctn_mp.borrow_rodata(parent_container_ptr).borrow().cpu_set;
    proof {
        assert(krnl.cpu_set_mp.dom().contains(parent_cpu_set)) by { reveal(container_cpu_set_wf); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    let ghost cpu_set_unlocked_k = *krnl;
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(parent_cpu_set, Tracked(&mut *lctx));
    let parent_set = krnl.cpu_set_mp.borrow_typed(parent_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let transfer_cpu_owned = parent_set.owned_cpus.contains(transfer_cpu_id);
    let transfer_cpu_off = parent_set.owned_cpus.is_closed(transfer_cpu_id);
    if !transfer_cpu_owned || !transfer_cpu_off {
        proof {
            assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id)
                == if !transfer_cpu_owned { RetValueType::ErrorIpcCpuOwnerMismatch } else { RetValueType::ErrorIpcCpuNotOff }) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); kernel_container_projection_at(old(krnl), parent_container_ptr);
                kernel_l4_end_projection_at(old(krnl), source_pagetable_ptr); kernel_pagetable_mappings_projection_at(old(krnl), parent_process_ptr);
                kernel_cpu_projection_at(old(krnl), transfer_cpu_id); reveal(container_cpu_wf);
            };
        }
        krnl.wunlock_cpu_set(parent_cpu_set, Tracked(&mut *lctx), Tracked(cpu_set_lock_perm));
        proof { container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock(&cpu_set_unlocked_k, &*krnl, parent_cpu_set); }
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_unchanged(&*krnl, &*lctx);
            new_container_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs,
                if !transfer_cpu_owned { RetValueType::ErrorIpcCpuOwnerMismatch } else { RetValueType::ErrorIpcCpuNotOff });
        }
        return Err(if !transfer_cpu_owned { RetValueType::ErrorIpcCpuOwnerMismatch } else { RetValueType::ErrorIpcCpuNotOff });
    }
    proof {
        assert(krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            && krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_container_ptr) by { reveal(container_cpu_wf); reveal(cpu_array_wf); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert({
            &&& kernel_k_to_kernel_u(*old(krnl)).cpu_array[cpu_id as int].owning_container == parent_container_ptr
            &&& kernel_k_to_kernel_u(*old(krnl)).cpu_array[cpu_id as int].current_process == Some(parent_process_ptr)
            &&& kernel_k_to_kernel_u(*old(krnl)).cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
        }) by { kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); };
        assert(source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })) by { source_range.va_range_lemma(); };
        assert(new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is Success) by {
            kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_process_ptr, current_thread_ptr, None); kernel_container_projection_at(old(krnl), parent_container_ptr);
            kernel_l4_end_projection_at(old(krnl), source_pagetable_ptr); kernel_pagetable_mappings_projection_at(old(krnl), parent_process_ptr);
            kernel_cpu_projection_at(old(krnl), transfer_cpu_id);
        };
    }
    Ok(NewContainerEntryLocked {
        parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr, parent_cpu_set, source_range,
        cpu_lock_perm: Tracked(cpu_lock_perm), container_lock_perm: Tracked(container_lock_perm), process_lock_perm: Tracked(process_lock_perm),
        thread_lock_perm: Tracked(thread_lock_perm), source_pagetable_lock_perm: Tracked(source_pagetable_lock_perm), cpu_set_lock_perm: Tracked(cpu_set_lock_perm),
    })
}

pub fn syscall_new_container(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_container_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range,
            funding_page_count, process_quota_4k, transfer_cpu_id, *initial_regs, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessThreeUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessThreeUsize ==> range as int + 3 <= final(steps).nonlock_view().len() as int <= 4 * range as int + 3,
        (ret is SuccessThreeUsize) == (new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id) is Success),
        !(ret is SuccessThreeUsize) ==> ret == new_container_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id),
{
    proof { use_type_invariant(&*steps); }
    let entry = match new_container_lock_entry(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, funding_page_count, process_quota_4k, transfer_cpu_id, initial_regs) {
        Ok(entry) => entry,
        Err(ret) => return ret,
    };
    let NewContainerEntryLocked {
        parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr, parent_cpu_set, source_range, cpu_lock_perm, container_lock_perm,
        process_lock_perm, thread_lock_perm, source_pagetable_lock_perm, cpu_set_lock_perm,
    } = entry;
    let (child_container_ptr, child_process_ptr, new_thread_ptr) = commit_new_container(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, parent_container_ptr, parent_process_ptr, current_thread_ptr, source_pagetable_ptr,
        &source_range, funding_page_count, process_quota_4k, transfer_cpu_id, parent_cpu_set, cpu_lock_perm, container_lock_perm,
        process_lock_perm, thread_lock_perm, source_pagetable_lock_perm, cpu_set_lock_perm, initial_regs,
    );
    let ret = RetValueType::SuccessThreeUsize { value1: child_container_ptr, value2: child_process_ptr, value3: new_thread_ptr };
    proof {
        new_container_syscall_trace_from_commit(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, va, range, funding_page_count,
            process_quota_4k, transfer_cpu_id, *initial_regs, ret);
    }
    ret
}
}
