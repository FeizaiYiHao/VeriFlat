use vstd::prelude::*;
use crate::*;
use super::cpu_offline_check_spec::*;
use super::cpu_offline_check_trace::*;
use super::cpu_offline_check_eof::cpu_went_off_eof;

verus! {
pub enum OfflineCheckResult {
    Continue,
    Off,
}

/// Commits the offline of `cpu_id` under every lock the check acquired: the running thread, if any, is
/// requeued at the tail, the cpu publishes the default page table and goes Off, its TLB entries are
/// flushed, its slot in the container cpu set is closed, and the request bit is cleared.
#[verifier::spinoff_prover]
fn cpu_offline_commit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    container_ptr: RwLockContainerPtr, scheduler_ptr: RwLockSchedulerPtr, cpu_set_ptr: RwLockCpuSetPtr, flags_ptr: RwLockCpuOfflineFlagsPtr,
    current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>, process_lock_perm: Option<Tracked<LockPerm>>,
    thread_lock_perm: Option<Tracked<LockPerm>>, cpu_lock_perm: Tracked<LockPerm>, flag_lock_perm: Tracked<LockPerm>,
    cpu_set_lock_perm: Tracked<LockPerm>, scheduler_lock_perm: Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        *old(krnl) == (KernelK {
            cpu_arr: old(krnl).cpu_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, sched_mp: old(krnl).sched_mp,
            cpu_set_mp: old(krnl).cpu_set_mp, cpu_offline_mp: old(krnl).cpu_offline_mp, ..old(steps).snapshot_k()
        }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.locking_thread() is None,
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)]
            old(steps).snapshot_k().prc_mp.dom().contains(p) ==> if current_process == Some(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() is None
            } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() },
        forall|t: RwLockThreadPtr| #![trigger old(krnl).thr_mp.spec_index(t)]
            old(steps).snapshot_k().thr_mp.dom().contains(t) ==> if current_thread == Some(t) {
                old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() is None
            } else { old(krnl).thr_mp.spec_index(t).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(t).locking_thread() },
        old(krnl).sched_mp.unchanged_except(&old(steps).snapshot_k().sched_mp, scheduler_ptr),
        old(steps).snapshot_k().sched_mp.spec_index(scheduler_ptr).locking_thread() is None,
        old(krnl).cpu_set_mp.unchanged_except(&old(steps).snapshot_k().cpu_set_mp, cpu_set_ptr),
        old(steps).snapshot_k().cpu_set_mp.spec_index(cpu_set_ptr).locking_thread() is None,
        old(krnl).cpu_offline_mp.unchanged_except(&old(steps).snapshot_k().cpu_offline_mp, flags_ptr),
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.entries_unchanged_except(&old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr).flags, cpu_id),
        old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread() is None,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        old(krnl).sched_mp.spec_index(scheduler_ptr).view().queue.view() == old(steps).snapshot_k().sched_mp.spec_index(scheduler_ptr).view().queue.view(),
        cpu_offline_requests_of(old(krnl).cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(old(steps).snapshot_k().cpu_offline_mp.spec_index(flags_ptr)),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom() =~= match current_process {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).thread_lock_map().dom() =~= match current_thread {
            Some(ptr) => set![ptr],
            None => Set::empty(),
        },
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom() =~= set![scheduler_ptr],
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom() =~= set![cpu_set_ptr],
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
        old(lctx).cpu_offline_flag_lock_map().dom() =~= set![(flags_ptr, cpu_id)],
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        cpu_lock_perm.view().state() is WriteLock,
        cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& cpu.owning_container == container_ptr
            &&& old(krnl).ctn_mp.dom().contains(container_ptr)
            &&& old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().scheduler == scheduler_ptr
            &&& old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().cpu_set == cpu_set_ptr
            &&& flags_ptr == cpu_offline_flags_ptr(container_ptr)
            &&& old(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
        },
        current_process is Some == current_thread is Some,
        current_process is Some == process_lock_perm is Some,
        current_thread is Some == thread_lock_perm is Some,
        old(krnl).sched_mp.dom().contains(scheduler_ptr),
        old(krnl).cpu_set_mp.dom().contains(cpu_set_ptr),
        old(krnl).cpu_offline_mp.dom().contains(flags_ptr),
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view().requested,
        old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().wlocked_by(old(lctx)),
        current_process is Some ==> {
            let process_ptr = current_process.unwrap();
            let perm = process_lock_perm.unwrap().view();
            &&& old(krnl).prc_mp.dom().contains(process_ptr)
            &&& !old(krnl).prc_mp.spec_index(process_ptr).being_killed()
            &&& typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id
        },
        current_thread is Some ==> {
            let thread_ptr = current_thread.unwrap();
            let perm = thread_lock_perm.unwrap().view();
            &&& old(krnl).thr_mp.dom().contains(thread_ptr)
            &&& !old(krnl).thr_mp.spec_index(thread_ptr).being_killed()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id })
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == current_process.unwrap()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean()
            &&& old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is None
            &&& !old(krnl).sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(thread_ptr)
            &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write)
            &&& perm.state() is WriteLock
            &&& perm.thread_id() == old(lctx).thread_id()
            &&& perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id
        },
        typed_lock_map_contains_mode(old(lctx).scheduler_lock_map(), scheduler_ptr, TypedLockMode::Write),
        scheduler_lock_perm.view().state() is WriteLock,
        scheduler_lock_perm.view().thread_id() == old(lctx).thread_id(),
        scheduler_lock_perm.view().lock_id() == old(krnl).sched_mp.spec_index(scheduler_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), cpu_set_ptr, TypedLockMode::Write),
        cpu_set_lock_perm.view().state() is WriteLock,
        cpu_set_lock_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_set_lock_perm.view().lock_id() == old(krnl).cpu_set_mp.spec_index(cpu_set_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).cpu_offline_flag_lock_map(), (flags_ptr, cpu_id), TypedLockMode::Write),
        flag_lock_perm.view().state() is WriteLock,
        flag_lock_perm.view().thread_id() == old(lctx).thread_id(),
        flag_lock_perm.view().lock_id() == old(krnl).cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view().push(KernelStep { old_u: kernel_k_to_kernel_u(old(steps).snapshot_k()), new_u: kernel_k_to_kernel_u(*final(krnl)) }),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs, true, cpu_offline_check_flushed_default_pcid(*old(krnl), cpu_id),
        ),
        final(steps).nonlock_view() == old(steps).nonlock_view().push(KernelStep { old_u: old(steps).nonlock_snapshot_u(), new_u: kernel_k_to_nonlock_kernel_u(*final(krnl)) }),
        cpu_offline_check_step_pre(final(steps).nonlock_view().last().old_u, cpu_id),
        cpu_offline_check_step(final(steps).nonlock_view().last().old_u, final(steps).nonlock_view().last().new_u, cpu_id, *pt_regs, cpu_offline_check_flushed_default_pcid(*old(krnl), cpu_id)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(krnl).cpu_arr.spec_index(other_cpu).view().view().view(),
{
    let tracked cpu_lock_perm = cpu_lock_perm.get();
    let tracked flag_lock_perm = flag_lock_perm.get();
    let tracked cpu_set_lock_perm = cpu_set_lock_perm.get();
    let tracked scheduler_lock_perm = scheduler_lock_perm.get();
    proof {
        assert({
            &&& krnl.sched_mp.perms_wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).inv()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).view().queue.wf()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view().len() == krnl.sched_mp.spec_index(scheduler_ptr).view().queue.len()
            &&& krnl.sched_mp.spec_index(scheduler_ptr).view().queue.length <= NUM_PAGES
            &&& krnl.cpu_set_mp.perms_wf()
            &&& krnl.cpu_set_mp.spec_index(cpu_set_ptr).inv()
            &&& krnl.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.view().contains(cpu_id)
            &&& !krnl.cpu_set_mp.spec_index(cpu_set_ptr).view().owned_cpus.closed_view().contains(cpu_id)
            &&& krnl.cpu_offline_mp.perms_wf()
            &&& krnl.cpu_offline_mp.spec_index(flags_ptr).inv()
            &&& krnl.cpu_arr.inv()
            &&& krnl.cpu_arr.spec_index(cpu_id).view().is_init()
            &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
        }) by {
            reveal(scheduler_perms_wf); reveal(LinkedList::wf_value_list); reveal(cpu_set_perms_wf); reveal(container_cpu_wf); reveal(cpu_offline_flags_wf); reveal(cpu_array_wf);
            scheduler_queue_len_bounded(&*krnl, scheduler_ptr);
        };
        if current_thread is Some { thread_perms_wf_at(krnl.thr_mp, current_thread.unwrap()); }
    }
    let Tracked(needflush_perm) = krnl.wlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx));
    let ghost before = *krnl;
    let default_cr3 = krnl.dflt_pt.borrow().cr3;
    assert(page_ptr_valid(default_cr3)) by { reveal(KernelK::default_pagetable_wf); reveal(PageTable::table_pages_wf); };
    let ghost old_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
    if let Some(prev) = current_thread {
        let ghost old_prev_lock_id = krnl.thr_mp.lock_id_by_key(prev);
        let prev_perm = thread_lock_perm.as_ref().unwrap();
        let previous = krnl.thr_mp.borrow_mut_typed(prev, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(prev_perm.borrow()));
        let (addr, perm) = previous.running_to_scheduled(prev, pt_regs);
        let scheduler = krnl.sched_mp.borrow_mut_typed(scheduler_ptr, Ghost(lctx.scheduler_lock_map()), Tracked(&*lctx), Tracked(&scheduler_lock_perm));
        scheduler.enqueue_scheduled_thread(prev, addr, perm);
        krnl.cpu_arr.block_current(cpu_id, default_cr3, &mut krnl.cpu_tlb, &mut krnl.pcid_needflush, &mut krnl.cpu_published, Tracked(&needflush_perm), Tracked(&mut *lctx), Tracked(&cpu_lock_perm));
        proof {
            lctx.update_lock_id(KernelObjId::Cpu(cpu_id), old_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id));
            lctx.update_lock_id(KernelObjId::Thread(prev), old_prev_lock_id, krnl.thr_mp.lock_id_by_key(prev));
        }
    } else {
        proof {
            lctx.enter_kernel_view_release();
            assert({
                &&& krnl.cpu_published[cpu_id as int].inv()
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == default_cr3
                &&& krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == KERNEL_DEFAULT_PCID
            }) by { reveal(cpu_published_wf); reveal(cpu_array_wf); };
        }
    }
    let ghost idle_cpu_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
    let cpu = krnl.cpu_arr.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    cpu.publish_off_from_idle();
    krnl.cpu_tlb.flush_all_local_pcids(cpu_id, Tracked(&*lctx));
    let cpu_set = krnl.cpu_set_mp.borrow_mut_typed(cpu_set_ptr, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    cpu_set.owned_cpus.mark_closed(cpu_id);
    krnl.cpu_offline_mp.set_flag(flags_ptr, cpu_id, false, Tracked(&*lctx), Tracked(&flag_lock_perm));
    proof {
        lctx.update_lock_id(KernelObjId::Cpu(cpu_id), idle_cpu_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id));
        assert(cpu_went_off_transition(before, *krnl, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, *pt_regs)) by {
            reveal(cpu_went_off_transition); reveal(thread_perms_wf); reveal(scheduler_perms_wf); reveal(cpu_set_perms_wf); reveal(pcid_needflush_wf); reveal(cpu_array_wf);
            assert(krnl.cpu_tlb.view() == cpu_tlb_after_cpu_went_off(before.cpu_tlb.view(), cpu_id, cpu_offline_check_flushed_default_pcid(before, cpu_id))) by {
                vstd::assert_maps_equal!(krnl.cpu_tlb.view(), cpu_tlb_after_cpu_went_off(before.cpu_tlb.view(), cpu_id, cpu_offline_check_flushed_default_pcid(before, cpu_id)), key => {});
            };
        };
        cpu_went_off_eof(before, *krnl, cpu_id, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, *pt_regs);
        assert(typed_lock_maps_aligned(&*krnl, &*lctx)) by { reveal(UnLockedMap::typed_flag_lock_map_aligned); };
        if current_thread is Some { process_thread_wf_at(before.prc_mp, before.thr_mp, current_thread.unwrap()); }
    }
    krnl.wunlock_pcid_needflush(cpu_id, KERNEL_DEFAULT_PCID, Tracked(&mut *lctx), Tracked(needflush_perm));
    krnl.wunlock_scheduler(scheduler_ptr, Tracked(&mut *lctx), Tracked(scheduler_lock_perm));
    krnl.wunlock_cpu_set(cpu_set_ptr, Tracked(&mut *lctx), Tracked(cpu_set_lock_perm));
    if let Some(perm) = thread_lock_perm {
        krnl.wunlock_thread(current_thread.unwrap(), Tracked(&mut *lctx), perm);
    }
    if let Some(perm) = process_lock_perm {
        krnl.wunlock_process(current_process.unwrap(), Tracked(&mut *lctx), perm);
    }
    krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), Tracked(flag_lock_perm));
    krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    proof {
        let ghost flushed = cpu_offline_check_flushed_default_pcid(*old(krnl), cpu_id);
        let ghost commit_before = steps.view();
        assert(kernel_cpu_went_off_fields(&steps.snapshot_k(), &*krnl, cpu_id, *pt_regs, flushed)) by {
            reveal(kernel_cpu_went_off_fields); reveal(cpu_went_off_transition); reveal(container_scheduler_wf); reveal(container_cpu_offline_flags_wf); reveal(cpu_offline_requests_of);
            broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        };
        steps.end_kernel_step_cpu_went_off(&*krnl, &*lctx, cpu_id, *pt_regs, flushed);
        no_locks_held_imply_all_objects_unlocked(krnl, lctx);
        assert({
            &&& cpu_offline_check_entry_trace(
                steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl),
                cpu_id, *pt_regs, true, flushed,
            )
            &&& cpu_offline_check_step_pre(steps.nonlock_view().last().old_u, cpu_id)
            &&& cpu_offline_check_step(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, *pt_regs, flushed)
        }) by {
            cpu_offline_check_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, *pt_regs, flushed);
            cpu_offline_check_step_from_u(steps.nonlock_view().last().old_u, steps.nonlock_view().last().new_u, cpu_id, *pt_regs, flushed);
            cpu_offline_check_trace_step(&*steps, commit_before, kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(*krnl), cpu_id, *pt_regs, flushed);
        };
    }
}

/// Entry run by a cpu before each schedule: when its container has requested it Off and its running
/// thread, if any, is live, the cpu requeues that thread and goes Off; the trap layer then halts it.
/// Otherwise the caller continues to `syscall_schedule`.
#[verifier::spinoff_prover]
pub fn cpu_offline_check(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
) -> (ret: OfflineCheckResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        cpu_offline_check_entry_trace(
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*final(krnl)),
            cpu_id, *pt_regs, ret is Off, if ret is Off { cpu_offline_check_flushed_default_pcid(*old(krnl), cpu_id) } else { false },
        ),
        final(steps).nonlock_view().len() == if ret is Off { 1nat } else { 0nat },
        ret == cpu_offline_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id),
        ret is Off ==> {
            let step = final(steps).nonlock_view()[0];
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(*old(krnl))
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_offline_check_step_pre(step.old_u, cpu_id)
            &&& cpu_offline_check_step(step.old_u, step.new_u, cpu_id, *pt_regs, cpu_offline_check_flushed_default_pcid(*old(krnl), cpu_id))
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off
        },
        ret is Continue ==> kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(krnl).cpu_arr.spec_index(other_cpu).view().view().view(),
{
    proof {
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        steps.rebase_snapshot_k_if_unchanged(&*krnl);
    }
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let state = cpu.state();
    let container_ptr = cpu.owning_container();
    let current_process = cpu.current_process();
    let current_thread = cpu.current_thread();
    if let CpuState::Off = state {
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl); };
            cpu_offline_check_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *pt_regs);
            assert(cpu_offline_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id) is Continue) by { kernel_cpu_projection_at(old(krnl), cpu_id); };
        }
        return OfflineCheckResult::Continue;
    }
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
            &&& page_ptr_2m_valid(container_ptr)
            &&& krnl.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(container_ptr))
            &&& (current_process is Some ==> krnl.prc_mp.dom().contains(current_process.unwrap()))
            &&& (current_process is Some == current_thread is Some)
            &&& (current_process is Some ==> krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().owning_container == container_ptr)
            &&& (current_thread is Some ==> {
                let ptr = current_thread.unwrap();
                &&& krnl.thr_mp.dom().contains(ptr)
                &&& krnl.thr_mp.spec_index(ptr).view().state == (ThreadState::RUNNING { cpu_id })
                &&& krnl.thr_mp.spec_index(ptr).view().owning_proc == current_process.unwrap()
                &&& krnl.thr_mp.spec_index(ptr).view().owning_container == container_ptr
            })
            &&& old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)
        }) by {
            assert(krnl.cpu_arr.spec_index(cpu_id).view().inv()) by { reveal(cpu_array_wf); };
            reveal(container_cpu_wf); reveal(container_perms_wf); reveal(thread_cpu_wf); reveal(process_cpu_wf); reveal(process_thread_wf);
            reveal(container_pages_wf); reveal(container_cpu_offline_flags_wf); reveal(cpu_published_wf);
        };
        assert(lctx.held_lock_majors_lt(CPU_OFFLINE_FLAG_LOCK_MAJOR)) by { reveal(LockedArray::typed_lock_map_aligned); };
    }
    let flags_ptr = container_ptr + 4096;
    let Tracked(flag_lock_perm) = krnl.wlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx));
    let requested = krnl.cpu_offline_mp.read_flag(flags_ptr, cpu_id, Tracked(&flag_lock_perm));
    if !requested {
        krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), Tracked(flag_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        }
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
                broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_transitive;
                kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
            };
            cpu_offline_check_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *pt_regs);
            assert(cpu_offline_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id) is Continue) by {
                reveal(cpu_offline_requests_of); kernel_cpu_projection_at(old(krnl), cpu_id); kernel_container_projection_at(old(krnl), container_ptr);
            };
        }
        return OfflineCheckResult::Continue;
    }
    let mut process_lock_perm: Option<Tracked<LockPerm>> = None;
    let mut thread_lock_perm: Option<Tracked<LockPerm>> = None;
    if let Some(process_ptr) = current_process {
        let res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
        if res.is_none() {
            krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), Tracked(flag_lock_perm));
            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            }
            release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
            proof {
                assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
                    broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_transitive;
                    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
                };
                cpu_offline_check_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *pt_regs);
                assert(cpu_offline_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id) is Continue) by { kernel_cpu_projection_at(old(krnl), cpu_id); kernel_process_projection_at(old(krnl), process_ptr); };
            }
            return OfflineCheckResult::Continue;
        }
        process_lock_perm = res;
        let thread_ptr = current_thread.unwrap();
        let res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
        if res.is_none() {
            krnl.wunlock_cpu_offline_flag(flags_ptr, cpu_id, Tracked(&mut *lctx), Tracked(flag_lock_perm));
            proof {
                assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
                assert(krnl.prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
            }
            release_cpu_and_process_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, process_ptr, process_lock_perm.unwrap(), Tracked(cpu_lock_perm));
            proof {
                assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
                    broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_transitive;
                    kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
                };
                cpu_offline_check_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, *pt_regs);
                assert(cpu_offline_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id) is Continue) by {
                    kernel_cpu_projection_at(old(krnl), cpu_id); kernel_process_projection_at(old(krnl), process_ptr); kernel_thread_projection_at(old(krnl), thread_ptr);
                };
            }
            return OfflineCheckResult::Continue;
        }
        thread_lock_perm = res;
    }
    let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr).borrow();
    let scheduler_ptr = container_ro.scheduler;
    let cpu_set_ptr = container_ro.cpu_set;
    proof {
        container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr);
        assert(krnl.cpu_set_mp.dom().contains(cpu_set_ptr)) by { reveal(container_cpu_set_wf); };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert({
            &&& krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view() == steps.snapshot_k().sched_mp.spec_index(scheduler_ptr).view().queue.view()
            &&& cpu_offline_requests_of(krnl.cpu_offline_mp.spec_index(flags_ptr)) == cpu_offline_requests_of(steps.snapshot_k().cpu_offline_mp.spec_index(flags_ptr))
        }) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
    }
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(cpu_set_ptr, Tracked(&mut *lctx));
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler(scheduler_ptr, Tracked(&mut *lctx));
    proof {
        assert(current_thread is Some ==> !krnl.sched_mp.spec_index(scheduler_ptr).view().queue.view().contains(current_thread.unwrap())) by {
            reveal(container_scheduler_wf); reveal(container_thread_scheduler_wf);
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
    }
    cpu_offline_commit(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, current_process, current_thread,
        process_lock_perm, thread_lock_perm, Tracked(cpu_lock_perm), Tracked(flag_lock_perm), Tracked(cpu_set_lock_perm), Tracked(scheduler_lock_perm),
    );
    proof {
        assert(cpu_offline_check_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id) is Off) by {
            reveal(cpu_offline_requests_of); kernel_cpu_projection_at(old(krnl), cpu_id); kernel_container_projection_at(old(krnl), container_ptr);
            if current_process is Some { kernel_process_projection_at(old(krnl), current_process->Some_0); kernel_thread_projection_at(old(krnl), current_thread->Some_0); }
        };
    }
    OfflineCheckResult::Off
}
}
