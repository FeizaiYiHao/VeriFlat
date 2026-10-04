use vstd::prelude::*;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::kernel_u_new_thread_changed;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::create_thread_from_staged_page::kernel_u_new_thread_changed;
use super::syscall_new_process_helpers::commit_new_process;
use super::syscall_new_process_with_iommu_helpers::commit_new_process_with_iommu_and_endpoint;
use super::syscall_new_process_spec::*;
use super::syscall_new_process_trace::*;

verus! {
/// Exec state handed from the lock-and-check prefix of `syscall_new_process_common` to its commit.
pub(super) struct NewProcessEntryLocked {
    pub container_ptr: RwLockContainerPtr, pub parent_ptr: RwLockProcessPtr, pub current_thread_ptr: RwLockThreadPtr, pub scheduler_ptr: RwLockSchedulerPtr,
    pub allocator_ptr: RwLockPageAllocatorPtr, pub pcid_allocator_ptr: RwLockPcidAllocatorPtr, pub source_pagetable_ptr: RwLockPageTableRoot,
    pub endpoint: Option<RwLockEndpointPtr>, pub endpoint_slot: EndpointIdx, pub pcid: Pcid, pub source_range: VaRange4K,
    pub cpu_lock_perm: Tracked<LockPerm>, pub pcid_allocator_lock_perm: Tracked<LockPerm>, pub parent_lock_perm: Tracked<LockPerm>,
    pub current_thread_lock_perm: Tracked<LockPerm>, pub source_pagetable_lock_perm: Tracked<LockPerm>, pub endpoint_lock_perm: Tracked<Option<LockPerm>>,
}

/// Validates the arguments and locks the cpu, pcid allocator, process, thread, optional endpoint, and source pagetable,
/// rejecting every failing check with all locks released and a stutter trace; otherwise the locks are returned held with
/// exactly the state both commits require, and the syscall result is pinned to Success.
#[verifier::spinoff_prover]
fn new_process_lock_entry(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr,
    range: usize, endpoint_index: Option<EndpointIdx>, with_iommu: bool, initial_regs: &Registers,
) -> (ret: Result<NewProcessEntryLocked, RetValueType>)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0),
        with_iommu ==> endpoint_index is Some,
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
            &&& new_process_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
                kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, r)
            &&& final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& final(steps).snapshot_k() == *final(krnl)
            &&& final(krnl).all_objects_unlocked(final(lctx))
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
            &&& final(lctx).no_locks_held()
            &&& final(steps).nonlock_view().len() == 0
            &&& !(r is SuccessPairUsize || r is SuccessThreeUsize)
            &&& !(new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is Success)
            &&& r == new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu)
        }),
        ret is Ok ==> ({
            let x = ret->Ok_0;
            let pre = kernel_k_to_kernel_u(*old(krnl));
            &&& *final(steps) == *old(steps)
            &&& x.source_range == (VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) })
            &&& new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is Success
            &&& with_iommu ==> x.endpoint is Some
            &&& (x.endpoint is Some) == (endpoint_index is Some)
            &&& endpoint_index is Some ==> x.endpoint_slot == endpoint_index->Some_0
            &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(x.current_thread_ptr)
            &&& old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container == x.container_ptr
            &&& endpoint_index is Some ==> old(krnl).thr_mp.spec_index(x.current_thread_ptr).view().endpoint_descriptors.wf()
            &&& endpoint_index is Some ==> x.endpoint == old(krnl).thr_mp.spec_index(x.current_thread_ptr).view().endpoint_descriptors.spec_index(endpoint_index->Some_0)
            &&& pre.cpu_array[cpu_id as int].current_process == Some(x.parent_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(x.current_thread_ptr)
            &&& pre.cpu_array[cpu_id as int].owning_container == x.container_ptr
            &&& pre.thread_map[x.current_thread_ptr].endpoint_descriptors == old(krnl).thr_mp.spec_index(x.current_thread_ptr).view().endpoint_descriptors.view()
            &&& *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, prc_mp: final(krnl).prc_mp, thr_mp: final(krnl).thr_mp,
                ep_mp: final(krnl).ep_mp, pt_mp: final(krnl).pt_mp, pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl) })
            &&& final(krnl).cpu_arr.unchanged_except(&old(krnl).cpu_arr, cpu_id)
            &&& final(krnl).prc_mp.unchanged_except(&old(krnl).prc_mp, x.parent_ptr)
            &&& final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, x.current_thread_ptr)
            &&& final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, x.source_pagetable_ptr)
            &&& old(krnl).cpu_arr.spec_index(cpu_id).value.locking_thread() is None
            &&& old(krnl).prc_mp.spec_index(x.parent_ptr).locking_thread() is None
            &&& old(krnl).thr_mp.spec_index(x.current_thread_ptr).locking_thread() is None
            &&& old(krnl).pt_mp.spec_index(x.source_pagetable_ptr).locking_thread() is None
            &&& x.endpoint is Some ==> old(krnl).ep_mp.spec_index(x.endpoint->Some_0).locking_thread() is None
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(x.current_thread_ptr)
            &&& match x.endpoint { Some(e) => final(krnl).ep_mp.unchanged_except(&old(krnl).ep_mp, e), None => final(krnl).ep_mp == old(krnl).ep_mp }
            &&& index_valid(NUM_CPUS, cpu_id)
            &&& cpu_id == final(lctx).cpu_id()
            &&& final(krnl).cpu_published[cpu_id as int].view() == (final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)
            &&& x.source_range.wf()
            &&& x.source_range.len > 0
            &&& x.source_range.len <= (usize::MAX - if with_iommu { 6int } else { 4int }) / 3
            &&& final(krnl).inv()
            &&& final(lctx).kernel_view_locking_state() is Acquire
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl))
            &&& kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp)
            &&& final(krnl).irt.owners() == old(krnl).irt.owners()
            &&& final(krnl).irt.iommu_roots() == old(krnl).irt.iommu_roots()
            &&& final(krnl).cpu_tlb.view() == old(krnl).cpu_tlb.view()
            &&& final(krnl).iommu_tlb.view() == old(krnl).iommu_tlb.view()
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl))
            &&& typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
            &&& x.cpu_lock_perm@.state() is WriteLock
            &&& x.cpu_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& x.cpu_lock_perm@.lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id
            &&& final(krnl).ctn_mp.dom().contains(x.container_ptr)
            &&& final(krnl).ctn_mp.spec_index(x.container_ptr).view_rodata().view().scheduler == x.scheduler_ptr
            &&& final(krnl).ctn_mp.spec_index(x.container_ptr).view_rodata().view().allocator_ptr_4k == x.allocator_ptr
            &&& final(krnl).ctn_mp.spec_index(x.container_ptr).view_rodata().view().pcid_allocator == x.pcid_allocator_ptr
            &&& final(krnl).pcid_allc_mp.dom().contains(x.pcid_allocator_ptr)
            &&& typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), x.pcid_allocator_ptr, TypedLockMode::Write)
            &&& final(krnl).pcid_allc_mp.spec_index(x.pcid_allocator_ptr).view().pcid_is_free(x.pcid)
            &&& x.pcid_allocator_lock_perm@.state() is WriteLock
            &&& x.pcid_allocator_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& x.pcid_allocator_lock_perm@.lock_id() == final(krnl).pcid_allc_mp.spec_index(x.pcid_allocator_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).prc_mp.dom().contains(x.parent_ptr)
            &&& final(krnl).prc_mp.spec_index(x.parent_ptr).view_rodata().view().owning_container == x.container_ptr
            &&& typed_lock_map_contains_mode(final(lctx).process_lock_map(), x.parent_ptr, TypedLockMode::Write)
            &&& !final(krnl).prc_mp.spec_index(x.parent_ptr).being_killed()
            &&& x.parent_lock_perm@.state() is WriteLock
            &&& x.parent_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& x.parent_lock_perm@.lock_id() == final(krnl).prc_mp.spec_index(x.parent_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).thr_mp.dom().contains(x.current_thread_ptr)
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().owning_proc == x.parent_ptr
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().owning_container == x.container_ptr
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().proc_pagetable_ptr == x.source_pagetable_ptr
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().quota_4k >= (if with_iommu { 6int } else { 4int }) + 3 * x.source_range.len
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().temp_alloc_clean()
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().syscall_progress.view() is None
            &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().free_quota_pending_clean()
            &&& typed_lock_map_contains_mode(final(lctx).thread_lock_map(), x.current_thread_ptr, TypedLockMode::Write)
            &&& !final(krnl).thr_mp.spec_index(x.current_thread_ptr).being_killed()
            &&& x.current_thread_lock_perm@.state() is WriteLock
            &&& x.current_thread_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& x.current_thread_lock_perm@.lock_id() == final(krnl).thr_mp.spec_index(x.current_thread_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).pt_mp.dom().contains(x.source_pagetable_ptr)
            &&& pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, x.source_pagetable_ptr, final(krnl).pt_mp.spec_index(x.source_pagetable_ptr).view())
            &&& final(krnl).pt_mp.spec_index(x.source_pagetable_ptr).view().leaves_present()
            &&& final(krnl).pt_mp.spec_index(x.source_pagetable_ptr).view().wf()
            &&& typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), x.source_pagetable_ptr, TypedLockMode::Write)
            &&& x.source_pagetable_lock_perm@.state() is WriteLock
            &&& x.source_pagetable_lock_perm@.thread_id() == final(lctx).thread_id()
            &&& x.source_pagetable_lock_perm@.lock_id() == final(krnl).pt_mp.spec_index(x.source_pagetable_ptr).locking_thread()->Write_lock_id
            &&& final(krnl).pt_mp.spec_index(x.source_pagetable_ptr).view().kernel_l4_end <= spec_v2l4index(x.source_range.start)
            &&& share_mapping_4k_source_range_present(final(krnl), x.source_pagetable_ptr, &x.source_range)
            &&& final(lctx).page_lock_map().dom().is_empty()
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ4k)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ2m)
            &&& final(lctx).holds_no_allocator_locks(PageSize::SZ1g)
            &&& forall|held_cpu_id: CpuId| #![trigger final(lctx).cpu_lock_map().dom().contains(held_cpu_id)] final(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(final(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off)
            &&& final(lctx).cpu_lock_map().dom() =~= set![cpu_id]
            &&& final(lctx).container_lock_map().dom().is_empty()
            &&& final(lctx).process_lock_map().dom() =~= set![x.parent_ptr]
            &&& final(lctx).thread_lock_map().dom() =~= set![x.current_thread_ptr]
            &&& x.endpoint is None ==> final(lctx).endpoint_lock_map().dom().is_empty()
            &&& x.endpoint is Some ==> {
                let endpoint_ptr = x.endpoint->Some_0;
                let endpoint_owner = final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container;
                &&& edp_idx_valid(x.endpoint_slot)
                &&& final(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr]
                &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().endpoint_descriptors.wf()
                &&& final(krnl).thr_mp.spec_index(x.current_thread_ptr).view().endpoint_descriptors.spec_index(x.endpoint_slot) == x.endpoint
                &&& final(krnl).ep_mp.dom().contains(endpoint_ptr)
                &&& final(krnl).ep_mp.spec_index(endpoint_ptr).is_init()
                &&& typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write)
                &&& !final(krnl).ep_mp.spec_index(endpoint_ptr).being_killed()
                &&& final(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((x.current_thread_ptr, x.endpoint_slot))
                &&& final(krnl).ctn_mp.dom().contains(endpoint_owner)
                &&& endpoint_owner == x.container_ptr || final(krnl).ctn_mp.spec_index(endpoint_owner).view_ghost().subtree_set.view().contains(x.container_ptr)
                &&& x.endpoint_lock_perm@ is Some
                &&& x.endpoint_lock_perm@->Some_0.state() is WriteLock
                &&& x.endpoint_lock_perm@->Some_0.thread_id() == final(lctx).thread_id()
                &&& x.endpoint_lock_perm@->Some_0.lock_id() == final(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id
            }
            &&& final(lctx).scheduler_lock_map().dom().is_empty()
            &&& final(lctx).pcid_allocator_lock_map().dom() =~= set![x.pcid_allocator_ptr]
            &&& final(lctx).cpu_set_lock_map().dom().is_empty()
            &&& final(lctx).pagetable_lock_map().dom() =~= set![x.source_pagetable_ptr]
            &&& final(lctx).iommu_table_lock_map().dom().is_empty()
            &&& final(lctx).pcid_needflush_lock_map().dom().is_empty()
            &&& final(lctx).cpu_offline_flag_lock_map().dom().is_empty()
            &&& typed_lock_maps_aligned(final(krnl), final(lctx))
        }),
{
    proof { use_type_invariant(&*steps); }
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let base_quota: usize = if with_iommu { 6usize } else { 4usize };
    if range == 0
        || range > usize::MAX / 4096usize
        || range > (usize::MAX - base_quota) / 3usize
        || !va_4k_valid(va)
    {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, None);
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, None);
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::Error);
        }
        return Err(RetValueType::Error);
    }
    let source_range = VaRange4K::new(va, range);
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));

    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    proof {
        assert(krnl.prc_mp.dom().contains(parent_ptr) && krnl.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr && !krnl.prc_mp.spec_index(parent_ptr).view().zombie) by {
            reveal(process_cpu_wf);
        };
        assert({
            &&& krnl.thr_mp.dom().contains(current_thread_ptr)
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr
            &&& krnl.prc_mp.spec_index(parent_ptr).view().owned_threads.view().len() != 0
        }) by { reveal(thread_cpu_wf); reveal(process_thread_wf); };
        assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.ctn_mp.view().spec_index(container_ptr).is_init() && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr) by { reveal(container_process_wf); reveal(container_perms_wf); };
    }
    let container_rodata = krnl.ctn_mp.borrow_rodata(container_ptr);
    let pcid_allocator_ptr = container_rodata.borrow().pcid_allocator;
    let scheduler_ptr = container_rodata.borrow().scheduler;
    let allocator_ptr = container_rodata.borrow().allocator_ptr_4k;
    proof { assert(krnl.pcid_allc_mp.dom().contains(pcid_allocator_ptr) && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().wf() && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().owning_container.view() == container_ptr) by { reveal(container_pcid_allocator_wf); reveal(pcid_allocator_perms_wf); }; }
    let Tracked(pcid_allocator_lock_perm) = krnl.wlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx));

    let pcid_allocator = krnl.pcid_allc_mp.borrow_typed(pcid_allocator_ptr, Ghost(lctx.pcid_allocator_lock_map()), Tracked(&*lctx), Tracked(&pcid_allocator_lock_perm));
    let pcid = match pcid_allocator.find_lowest_free_nonzero() {
        Some(pcid) => pcid,
        None => {
            krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
            krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
            proof {
                steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, None, None, None, None, Some(pcid_allocator_ptr));
                new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::ErrorNoPcid);
                assert(new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is ErrorNoPcid) by {
                    kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None);
                };
            }
            return Err(RetValueType::ErrorNoPcid);
        },
    };
    proof { assert(kernel_k_to_kernel_u(*old(krnl)).container_map[container_ptr].free_pcids.contains(pcid)) by { kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None); }; }
    let process_res = krnl.wlock_process_unless_killed(parent_ptr, Ghost(cpu_id), Tracked(&mut *lctx));

    if process_res.is_none() {
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), None, None, None, Some(pcid_allocator_ptr));
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::ErrorProcessKilled);
            assert(new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is ErrorProcessKilled) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None);
            };
        }
        return Err(RetValueType::ErrorProcessKilled);
    }
    let Tracked(parent_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));

    if thread_res.is_none() {
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), Some(current_thread_ptr), None, None, Some(pcid_allocator_ptr));
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::ErrorThreadKilled);
            assert(new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is ErrorThreadKilled) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None);
            };
        }
        return Err(RetValueType::ErrorThreadKilled);
    }
    let Tracked(current_thread_lock_perm) = thread_res.unwrap();
    let thread_ref = krnl.thr_mp.borrow_typed(current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    let endpoint_option = match endpoint_index { Some(index) => *thread_ref.endpoint_descriptors.get(index), None => None };
    let source_pagetable_ptr = thread_ref.proc_pagetable_ptr;
    let endpoint_missing = endpoint_index.is_some() && endpoint_option.is_none();
    if endpoint_missing || thread_ref.quota_4k < base_quota + 3 * range {
        let error = if endpoint_missing { RetValueType::Error } else { RetValueType::ErrorNoQuota };
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), Some(current_thread_ptr), None, None, Some(pcid_allocator_ptr));
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, error);
            assert(new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) == error) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None);
            };
        }
        return Err(error);
    }
    let endpoint_ptr = match endpoint_option { Some(ptr) => ptr, None => 0 };
    let tracked mut endpoint_lock_perm_opt: Option<LockPerm> = None;
    if endpoint_index.is_some() {
        proof {
            assert(krnl.ep_mp.dom().contains(endpoint_ptr) && krnl.ep_mp.spec_index(endpoint_ptr).view().owning_threads.view().contains((current_thread_ptr, endpoint_index->Some_0))) by { reveal(thread_endpoint_ref_counter_wf); };
            assert(krnl.ctn_mp.dom().contains(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container)) by { container_endpoint_wf_at(krnl.ctn_mp, krnl.ep_mp, endpoint_ptr); };
            assert({
                ||| krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
                ||| krnl.ctn_mp.spec_index(krnl.ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
            }) by { reveal(container_thread_endpoint_wf); };
        }
        let Tracked(endpoint_lock_perm) = krnl.wlock_endpoint(endpoint_ptr, Tracked(&mut *lctx));
        proof { endpoint_lock_perm_opt = Some(endpoint_lock_perm); }
    }
    proof {
        assert(krnl.pt_mp.dom().contains(source_pagetable_ptr) && !lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr) && krnl.prc_mp.spec_index(parent_ptr).view().pagetable == source_pagetable_ptr) by {
            reveal(process_thread_wf); reveal(process_pagetable_match);
        };
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
        if endpoint_index.is_some() {
            let tracked endpoint_lock_perm = endpoint_lock_perm_opt.tracked_unwrap();
            krnl.wunlock_endpoint(endpoint_ptr, Tracked(&mut *lctx), Tracked(endpoint_lock_perm));
        }
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
        krnl.wunlock_process(parent_ptr, Tracked(&mut *lctx), Tracked(parent_lock_perm));
        krnl.wunlock_pcid_allocator(pcid_allocator_ptr, Tracked(&mut *lctx), Tracked(pcid_allocator_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, None, Some(parent_ptr), Some(current_thread_ptr), endpoint_option, Some(source_pagetable_ptr), Some(pcid_allocator_ptr));
            new_process_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, RetValueType::Error);
            assert(new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is Error) by {
                kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None); kernel_l4_end_projection_at(old(krnl), source_pagetable_ptr); kernel_pagetable_mappings_projection_at(old(krnl), parent_ptr);
            };
        }
        return Err(RetValueType::Error);
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    proof {
        assert({
            let pre = kernel_k_to_kernel_u(*old(krnl));
            &&& pre.cpu_array[cpu_id as int].current_process == Some(parent_ptr)
            &&& pre.cpu_array[cpu_id as int].current_thread == Some(current_thread_ptr)
            &&& pre.cpu_array[cpu_id as int].owning_container == container_ptr
            &&& pre.thread_map[current_thread_ptr].endpoint_descriptors == old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors.view()
        }) by { kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None); };
    }
    proof {
        assert(new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is Success) by {
            kernel_cpu_thread_projection_at(old(krnl), cpu_id, parent_ptr, current_thread_ptr, None); kernel_l4_end_projection_at(old(krnl), source_pagetable_ptr); kernel_pagetable_mappings_projection_at(old(krnl), parent_ptr);
        };
    }
    let (endpoint, endpoint_slot) = match endpoint_index { Some(index) => (Some(endpoint_ptr), index), None => (None, 0) };
    Ok(NewProcessEntryLocked {
        container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, endpoint, endpoint_slot, pcid,
        source_range, cpu_lock_perm: Tracked(cpu_lock_perm), pcid_allocator_lock_perm: Tracked(pcid_allocator_lock_perm), parent_lock_perm: Tracked(parent_lock_perm),
        current_thread_lock_perm: Tracked(current_thread_lock_perm), source_pagetable_lock_perm: Tracked(source_pagetable_lock_perm),
        endpoint_lock_perm: Tracked(endpoint_lock_perm_opt),
    })
}

/// Shared body of the new-process syscalls: `endpoint_index` seeds the child thread, `with_iommu` adds an empty IOMMU table.
#[verifier::spinoff_prover]
pub(super) fn syscall_new_process_common(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr,
    range: usize, endpoint_index: Option<EndpointIdx>, with_iommu: bool, initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        endpoint_index is Some ==> edp_idx_valid(endpoint_index->Some_0),
        with_iommu ==> endpoint_index is Some,
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
        new_process_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int),
            kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, ret),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessPairUsize || ret is SuccessThreeUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessPairUsize ==> !with_iommu,
        ret is SuccessThreeUsize ==> with_iommu,
        ret is SuccessPairUsize || ret is SuccessThreeUsize ==> {
            let current_thread_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread->Some_0;
            let container_ptr = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container;
            let child_ptr = if with_iommu { ret->SuccessThreeUsize_value1 } else { ret->SuccessPairUsize_value1 };
            let thread_ptr = if with_iommu { ret->SuccessThreeUsize_value3 } else { ret->SuccessPairUsize_value2 };
            let descriptors = old(krnl).thr_mp.spec_index(current_thread_ptr).view().endpoint_descriptors;
            let endpoint = if endpoint_index is Some { descriptors.spec_index(endpoint_index->Some_0) } else { None };
            let source_range = VaRange4K { start: va, len: range, view: Ghost(Seq::new(range as nat, |i: int| spec_va_add_range(va, i as usize))) };
            &&& range > 0
            &&& range as int + 3 <= final(steps).nonlock_view().len() as int
            &&& final(steps).nonlock_view().len() as int <= 4 * range as int + 3
            &&& final(steps).nonlock_view().last().new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& source_range.wf()
            &&& endpoint_index is Some ==> descriptors.wf() && endpoint is Some
            &&& kernel_u_new_thread_changed(
                final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, child_ptr, current_thread_ptr, container_ptr,
                thread_ptr, *initial_regs, endpoint, None,
            )
            &&& with_iommu ==> final(krnl).prc_mp.dom().contains(child_ptr) && final(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == Some(ret->SuccessThreeUsize_value2)
            &&& with_iommu ==> final(krnl).it_mp.dom().contains(ret->SuccessThreeUsize_value2) && final(krnl).it_mp.spec_index(ret->SuccessThreeUsize_value2).view().is_empty()
            &&& final(krnl).thr_mp.dom().contains(thread_ptr)
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().state is SCHEDULED
            &&& final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == child_ptr
            &&& endpoint_index is Some ==> final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.wf()
            &&& endpoint_index is Some ==> final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors.spec_index(0) == endpoint
        },
        (ret is SuccessPairUsize || ret is SuccessThreeUsize) == (new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu) is Success),
        !(ret is SuccessPairUsize || ret is SuccessThreeUsize) ==> ret == new_process_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, va, range, endpoint_index, with_iommu),
{
    proof { use_type_invariant(&*steps); }
    let entry = match new_process_lock_entry(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va, range, endpoint_index, with_iommu, initial_regs) {
        Ok(entry) => entry,
        Err(ret) => return ret,
    };
    let NewProcessEntryLocked {
        container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr, allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, endpoint, endpoint_slot, pcid,
        source_range, cpu_lock_perm, pcid_allocator_lock_perm, parent_lock_perm, current_thread_lock_perm, source_pagetable_lock_perm, endpoint_lock_perm,
    } = entry;
    if with_iommu {
        let Tracked(endpoint_lock_perm_opt) = endpoint_lock_perm;
        let tracked endpoint_lock_perm = endpoint_lock_perm_opt.tracked_unwrap();
        let (child_ptr, iommu_table_ptr, thread_ptr) = commit_new_process_with_iommu_and_endpoint(
            krnl, &source_range, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr,
            allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, endpoint.unwrap(), endpoint_slot, pcid, cpu_lock_perm, pcid_allocator_lock_perm,
            parent_lock_perm, current_thread_lock_perm, source_pagetable_lock_perm, Tracked(endpoint_lock_perm), initial_regs,
        );
        let ret = RetValueType::SuccessThreeUsize { value1: child_ptr, value2: iommu_table_ptr, value3: thread_ptr };
        proof { new_process_syscall_trace_from_commit(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, ret); }
        ret
    } else {
        let (child_ptr, thread_ptr) = commit_new_process(
            krnl, &source_range, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, parent_ptr, current_thread_ptr, scheduler_ptr,
            allocator_ptr, pcid_allocator_ptr, source_pagetable_ptr, endpoint, endpoint_slot, pcid, cpu_lock_perm, pcid_allocator_lock_perm,
            parent_lock_perm, current_thread_lock_perm, source_pagetable_lock_perm, endpoint_lock_perm, initial_regs,
        );
        let ret = RetValueType::SuccessPairUsize { value1: child_ptr, value2: thread_ptr };
        proof { new_process_syscall_trace_from_commit(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), cpu_id, va, range, *initial_regs, endpoint_index, with_iommu, ret); }
        ret
    }
}
}
