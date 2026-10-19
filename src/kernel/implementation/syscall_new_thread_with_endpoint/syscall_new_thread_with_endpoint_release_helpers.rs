use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
#[cfg(feature = "split-crates")]
use veriflat_kernel_core::attach_endpoint_reference_and_unlock;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::attach_endpoint_reference_and_unlock::attach_endpoint_reference_and_unlock;

verus! {
/// Release phase of the endpoint-sharing thread creation: binds descriptor 0 of the scheduled new thread to the endpoint, unlocks the
/// new thread's page and the scheduler shard, clears the staging thread's progress, and unlocks the staging thread, the process, and the
/// cpu, leaving no lock held. The whole finish step from `finish_k` is the new-thread transition with the initial endpoint attached.
pub(super) fn attach_endpoint_and_release_new_thread_locks(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Ghost(finish_k): Ghost<KernelK>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    current_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, new_thread_ptr: RwLockThreadPtr,
    endpoint_ptr: RwLockEndpointPtr, Ghost(endpoint_index): Ghost<EndpointIdx>, Ghost(regs): Ghost<Registers>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
    Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(new_thread_lock_perm): Tracked<LockPerm>,
    Tracked(page_lock_perm): Tracked<LockPerm>, Tracked(scheduler_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(new_thread_ptr),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(new_thread_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![process_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, new_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom() =~= set![(scheduler_ptr, cpu_id)],
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
        old(krnl).prc_mp.dom().contains(process_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running,
        process_lock_perm.state() is WriteLock && process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        current_thread_ptr != new_thread_ptr,
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::NewThread { regs, endpoint_index: Some(endpoint_index) }),
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(new_thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), new_thread_ptr, TypedLockMode::Write),
        old(krnl).thr_mp.spec_index(new_thread_ptr).is_init(),
        !old(krnl).thr_mp.spec_index(new_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().state is SCHEDULED,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.spec_index(0) is None,
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(new_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(new_thread_ptr).view_ghost().exited,
        new_thread_lock_perm.state() is WriteLock && new_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        new_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(new_thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(new_thread_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock && page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(new_thread_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (scheduler_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock && scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        endpoint_lock_perm.state() is WriteLock && endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(endpoint_ptr).locking_thread()->Write_lock_id,
        {
            ||| old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container == container_ptr
            ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(endpoint_ptr).view().owning_container).view_ghost().subtree_set.view().contains(container_ptr)
        },
        kernel_new_thread_fields(&finish_k, old(krnl), process_ptr, current_thread_ptr, container_ptr, cpu_id, new_thread_ptr, regs, None,
            Some(SyscallProgress::NewThread { regs, endpoint_index: Some(endpoint_index) })),
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, ctn_mp: old(krnl).ctn_mp, sched_mp: old(krnl).sched_mp, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ..finish_k }),
        forall|c: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(c).locking_thread()]
            finish_k.ctn_mp.dom().contains(c) ==> old(krnl).ctn_mp.spec_index(c).locking_thread() == finish_k.ctn_mp.spec_index(c).locking_thread(),
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p).locking_thread()]
            finish_k.prc_mp.dom().contains(p) && p != process_ptr ==> old(krnl).prc_mp.spec_index(p).locking_thread() == finish_k.prc_mp.spec_index(p).locking_thread(),
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(t)]
            finish_k.thr_mp.dom().contains(t) && t != current_thread_ptr ==> old(krnl).thr_mp.spec_index(t) == finish_k.thr_mp.spec_index(t),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_new_thread_fields(&finish_k, final(krnl), process_ptr, current_thread_ptr, container_ptr, cpu_id, new_thread_ptr, regs, Some(endpoint_ptr), None),
        forall|p: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(p)]
            finish_k.ctn_mp.dom().contains(p) ==> final(krnl).ctn_mp.spec_index(p).locking_thread() == finish_k.ctn_mp.spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
            finish_k.prc_mp.dom().contains(p) ==> if p == process_ptr { final(krnl).prc_mp.spec_index(p).locking_thread() is None } else { final(krnl).prc_mp.spec_index(p).locking_thread() == finish_k.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(p)]
            finish_k.thr_mp.dom().contains(p) ==> if p == current_thread_ptr { final(krnl).thr_mp.spec_index(p).locking_thread() is None } else { final(krnl).thr_mp.spec_index(p).locking_thread() == finish_k.thr_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(p)]
            finish_k.ep_mp.dom().contains(p) ==> if Some(endpoint_ptr) == Some(p) { final(krnl).ep_mp.spec_index(p).locking_thread() is None } else { final(krnl).ep_mp.spec_index(p).locking_thread() == finish_k.ep_mp.spec_index(p).locking_thread() },
        final(krnl).pt_mp == finish_k.pt_mp,
        final(krnl).it_mp == finish_k.it_mp,
        forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { final(krnl).cpu_arr.spec_index(i).value.locking_thread() is None } else { final(krnl).cpu_arr.spec_index(i).value.locking_thread() == finish_k.cpu_arr.spec_index(i).value.locking_thread() },
        final(krnl).thr_mp.spec_index(new_thread_ptr).locking_thread() is None,
{
    proof { assert(old(krnl).prc_mp.dom() == finish_k.prc_mp.dom() && old(krnl).thr_mp.dom() == finish_k.thr_mp.dom().insert(new_thread_ptr) && !finish_k.thr_mp.dom().contains(new_thread_ptr)) by { reveal(kernel_new_thread_fields); }; }
    attach_endpoint_reference_and_unlock(krnl, new_thread_ptr, endpoint_ptr, current_thread_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(new_thread_ptr), Tracked(&mut *lctx), Tracked(page_lock_perm));
    krnl.wunlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(kernel_new_thread_fields(&finish_k, krnl, process_ptr, current_thread_ptr, container_ptr, cpu_id, new_thread_ptr, regs, Some(endpoint_ptr), None)) by {
            let descriptors = krnl.thr_mp.spec_index(new_thread_ptr).view().endpoint_descriptors.view();
            reveal(kernel_new_thread_fields);
            assert_seqs_equal!(descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { Some(endpoint_ptr) } else { None }), i => {});
        };
    }
}
} // verus!
