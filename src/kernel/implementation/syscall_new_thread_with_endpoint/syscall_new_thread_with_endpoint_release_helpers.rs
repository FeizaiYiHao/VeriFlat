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
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Ghost(finish_k): Ghost<KernelK>, cpu_id: CpuId, prc_ptr: RwLockProcessPtr,
    current_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, sched_ptr: RwLockSchedulerPtr, new_thrd_ptr: RwLockThreadPtr,
    ep_ptr: RwLockEndpointPtr, Ghost(ep_idx): Ghost<EndpointIdx>, Ghost(regs): Ghost<Registers>, Tracked(cpu_lock_perm): Tracked<LockPerm>,
    Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(current_thread_lock_perm): Tracked<LockPerm>, Tracked(new_thread_lock_perm): Tracked<LockPerm>,
    Tracked(page_lock_perm): Tracked<LockPerm>, Tracked(scheduler_lock_perm): Tracked<LockPerm>, Tracked(endpoint_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        page_ptr_valid(new_thrd_ptr),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).page_lock_map().dom() =~= set![page_ptr2page_index(new_thrd_ptr)],
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= set![prc_ptr],
        old(lctx).thread_lock_map().dom() =~= set![current_thrd_ptr, new_thrd_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![ep_ptr],
        old(lctx).scheduler_lock_map().dom() =~= set![(sched_ptr, cpu_id)],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).prc_mp.dom().contains(prc_ptr),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), prc_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(prc_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Running,
        process_lock_perm.state() is WriteLock && process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(prc_ptr).locking_thread()->Write_lock_id,
        current_thrd_ptr != new_thrd_ptr,
        old(krnl).thrd_mp.dom().contains(current_thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thrd_ptr, TypedLockMode::Write),
        !old(krnl).thrd_mp.spec_index(current_thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(current_thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::NewThread { regs, endpoint_index: Some(ep_idx) }),
        !old(krnl).thrd_mp.spec_index(current_thrd_ptr).view_ghost().exited,
        current_thread_lock_perm.state() is WriteLock && current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(current_thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.dom().contains(new_thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), new_thrd_ptr, TypedLockMode::Write),
        old(krnl).thrd_mp.spec_index(new_thrd_ptr).is_init(),
        !old(krnl).thrd_mp.spec_index(new_thrd_ptr).being_killed(),
        old(krnl).thrd_mp.spec_index(new_thrd_ptr).view().state is SCHEDULED,
        old(krnl).thrd_mp.spec_index(new_thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(new_thrd_ptr).view().endpoint_descriptors.wf(),
        old(krnl).thrd_mp.spec_index(new_thrd_ptr).view().endpoint_descriptors.spec_index(0) is None,
        old(krnl).thrd_mp.spec_index(new_thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(new_thrd_ptr).view().temp_alloc_clean(),
        old(krnl).thrd_mp.spec_index(new_thrd_ptr).view().syscall_progress.view() is None,
        !old(krnl).thrd_mp.spec_index(new_thrd_ptr).view_ghost().exited,
        new_thread_lock_perm.state() is WriteLock && new_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        new_thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(new_thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(new_thrd_ptr), TypedLockMode::Write),
        page_lock_perm.state() is WriteLock && page_lock_perm.thread_id() == old(lctx).thread_id(),
        page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(new_thrd_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).sched_mp.dom().contains(sched_ptr),
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), (sched_ptr, cpu_id), TypedLockMode::Write),
        scheduler_lock_perm.state() is WriteLock && scheduler_lock_perm.thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.lock_id() == old(krnl).sched_mp.spec_index(sched_ptr).shards.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).ep_mp.dom().contains(ep_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), ep_ptr, TypedLockMode::Write),
        endpoint_lock_perm.state() is WriteLock && endpoint_lock_perm.thread_id() == old(lctx).thread_id(),
        endpoint_lock_perm.lock_id() == old(krnl).ep_mp.spec_index(ep_ptr).locking_thread()->Write_lock_id,
        {
            ||| old(krnl).ep_mp.spec_index(ep_ptr).view().owning_container == ctn_ptr
            ||| old(krnl).ctn_mp.spec_index(old(krnl).ep_mp.spec_index(ep_ptr).view().owning_container).view_ghost().subtree_set.view().contains(ctn_ptr)
        },
        kernel_new_thread_fields(&finish_k, old(krnl), prc_ptr, current_thrd_ptr, ctn_ptr, cpu_id, new_thrd_ptr, regs, None,
            Some(SyscallProgress::NewThread { regs, endpoint_index: Some(ep_idx) })),
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, ctn_mp: old(krnl).ctn_mp, sched_mp: old(krnl).sched_mp, prc_mp: old(krnl).prc_mp, thrd_mp: old(krnl).thrd_mp, ..finish_k }),
        forall|c: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(c).locking_thread()]
            finish_k.ctn_mp.dom().contains(c) ==> old(krnl).ctn_mp.spec_index(c).locking_thread() == finish_k.ctn_mp.spec_index(c).locking_thread() && old(krnl).ctn_mp.spec_index(c).control() == finish_k.ctn_mp.spec_index(c).control(),
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p).locking_thread()]
            finish_k.prc_mp.dom().contains(p) && p != prc_ptr ==> old(krnl).prc_mp.spec_index(p).locking_thread() == finish_k.prc_mp.spec_index(p).locking_thread(),
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thrd_mp.spec_index(t)]
            finish_k.thrd_mp.dom().contains(t) && t != current_thrd_ptr ==> old(krnl).thrd_mp.spec_index(t) == finish_k.thrd_mp.spec_index(t),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_new_thread_fields(&finish_k, final(krnl), prc_ptr, current_thrd_ptr, ctn_ptr, cpu_id, new_thrd_ptr, regs, Some(ep_ptr), None),
        forall|p: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(p)]
            finish_k.ctn_mp.dom().contains(p) ==> final(krnl).ctn_mp.spec_index(p).locking_thread() == finish_k.ctn_mp.spec_index(p).locking_thread() && final(krnl).ctn_mp.spec_index(p).lock_process_owner_u() == finish_k.ctn_mp.spec_index(p).lock_process_owner_u(),
        forall|p: RwLockProcessPtr| #![trigger final(krnl).prc_mp.spec_index(p)]
            finish_k.prc_mp.dom().contains(p) ==> if p == prc_ptr { final(krnl).prc_mp.spec_index(p).locking_thread() is None } else { final(krnl).prc_mp.spec_index(p).locking_thread() == finish_k.prc_mp.spec_index(p).locking_thread() },
        forall|p: RwLockThreadPtr| #![trigger final(krnl).thrd_mp.spec_index(p)]
            finish_k.thrd_mp.dom().contains(p) ==> if p == current_thrd_ptr { final(krnl).thrd_mp.spec_index(p).locking_thread() is None } else { final(krnl).thrd_mp.spec_index(p).locking_thread() == finish_k.thrd_mp.spec_index(p).locking_thread() },
        forall|p: RwLockEndpointPtr| #![trigger final(krnl).ep_mp.spec_index(p)]
            finish_k.ep_mp.dom().contains(p) ==> if Some(ep_ptr) == Some(p) { final(krnl).ep_mp.spec_index(p).locking_thread() is None } else { final(krnl).ep_mp.spec_index(p).locking_thread() == finish_k.ep_mp.spec_index(p).locking_thread() },
        final(krnl).pt_mp == finish_k.pt_mp,
        final(krnl).it_mp == finish_k.it_mp,
        forall|i: CpuId| #![trigger final(krnl).cpu_arr.spec_index(i)]
            index_valid(NUM_CPUS, i) ==> if i == cpu_id { final(krnl).cpu_arr.spec_index(i).value.locking_thread() is None } else { final(krnl).cpu_arr.spec_index(i).value.locking_thread() == finish_k.cpu_arr.spec_index(i).value.locking_thread() },
        final(krnl).thrd_mp.spec_index(new_thrd_ptr).locking_thread() is None,
        final(krnl).cpu_op.view().view() == finish_k.cpu_op.view().view().update(cpu_id as int, cpu_op_after_step(finish_k.cpu_arr.spec_index(cpu_id).view().view().view().state)),
{
    proof { assert(old(krnl).prc_mp.dom() == finish_k.prc_mp.dom() && old(krnl).thrd_mp.dom() == finish_k.thrd_mp.dom().insert(new_thrd_ptr) && !finish_k.thrd_mp.dom().contains(new_thrd_ptr)) by { reveal(kernel_new_thread_fields); }; }
    attach_endpoint_reference_and_unlock(krnl, new_thrd_ptr, ep_ptr, current_thrd_ptr, Tracked(&mut *lctx), Tracked(new_thread_lock_perm), Tracked(endpoint_lock_perm));
    krnl.wunlock_page(page_ptr2page_index(new_thrd_ptr), Tracked(&mut *lctx), Tracked(page_lock_perm));
    krnl.wunlock_scheduler_shard(sched_ptr, cpu_id, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.set_thread_syscall_progress(current_thrd_ptr, Ghost(None), Tracked(&*lctx), Tracked(&current_thread_lock_perm));
    krnl.wunlock_thread(current_thrd_ptr, Tracked(&mut *lctx), Tracked(current_thread_lock_perm));
    krnl.wunlock_process(prc_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        assert(kernel_new_thread_fields(&finish_k, krnl, prc_ptr, current_thrd_ptr, ctn_ptr, cpu_id, new_thrd_ptr, regs, Some(ep_ptr), None)) by {
            let descriptors = krnl.thrd_mp.spec_index(new_thrd_ptr).view().endpoint_descriptors.view();
            reveal(kernel_new_thread_fields);
            assert_seqs_equal!(descriptors == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| if i == 0 { Some(ep_ptr) } else { None }), i => {});
        };
    }
}
} // verus!
