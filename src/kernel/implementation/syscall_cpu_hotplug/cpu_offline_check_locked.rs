use vstd::prelude::*;
use crate::*;
use super::cpu_offline_check_spec::*;
use super::cpu_offline_check_trace::*;
use super::cpu_offline_check::{OfflineCheckResult, cpu_offline_commit};

verus! {
/// With `cpu_id` write-held and not Off, owned by `container_ptr` and running `current_thread` of `current_process`, if
/// any: when the container has requested the cpu Off and that process and thread are live, write-locks them, the
/// container's cpu set and scheduler shard of the cpu, and commits the offline; otherwise releases every lock and continues.
pub(super) fn cpu_offline_check_locked(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, pt_regs: &Registers,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, container_ptr: RwLockContainerPtr, current_process: Option<RwLockProcessPtr>, current_thread: Option<RwLockThreadPtr>,
) -> (ret: OfflineCheckResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).nonlock_view().len() == 0,
        *old(krnl) == (KernelK { cpu_arr: old(krnl).cpu_arr, ..old(steps).snapshot_k() }),
        old(krnl).cpu_arr.unchanged_except(&old(steps).snapshot_k().cpu_arr, cpu_id),
        wlock_ensures(old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).view(), old(krnl).cpu_arr.spec_index(cpu_id).view(), old(steps).snapshot_k().cpu_arr.lock_id_by_index(cpu_id), old(lctx), cpu_lock_perm),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).held_lock_majors_lt(CPU_OFFLINE_FLAG_LOCK_MAJOR),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom().is_empty(),
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
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        {
            let cpu = old(krnl).cpu_arr.spec_index(cpu_id).view().view().view();
            &&& !(cpu.state is Off)
            &&& cpu.owning_container == container_ptr
            &&& cpu.current_process == current_process
            &&& cpu.current_thread == current_thread
            &&& old(krnl).cpu_published[cpu_id as int].view() == (cpu.current_cr3, cpu.current_pcid)
        },
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
            final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, *pt_regs, ret is Off, if ret is Off { cpu_offline_check_flushed_default_pcid(old(steps).snapshot_k(), cpu_id) } else { false },
        ),
        final(steps).nonlock_view().len() == if ret is Off { 1nat } else { 0nat },
        ret == cpu_offline_check_result(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id),
        ret is Off ==> {
            let step = final(steps).nonlock_view()[0];
            &&& step.old_u == kernel_k_to_nonlock_kernel_u(old(steps).snapshot_k())
            &&& step.new_u == kernel_k_to_nonlock_kernel_u(*final(krnl))
            &&& cpu_offline_check_step_pre(step.old_u, cpu_id)
            &&& cpu_offline_check_step(step.old_u, step.new_u, cpu_id, *pt_regs, cpu_offline_check_flushed_default_pcid(old(steps).snapshot_k(), cpu_id))
            &&& final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off
        },
        ret is Continue ==> kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(old(steps).snapshot_k()),
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(steps).snapshot_k().cpu_arr.spec_index(other_cpu).view().view().view(),
{
    proof {
        assert({
            &&& krnl.ctn_mp.dom().contains(container_ptr)
            &&& krnl.ctn_mp.spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr
            &&& krnl.cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(container_ptr))
        }) by { container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id); container_perms_wf_at(krnl.ctn_mp, container_ptr); container_cpu_offline_flags_wf_container_at(krnl.ctn_mp, krnl.cpu_offline_mp, container_ptr); };
        assert(page_ptr_2m_valid(container_ptr)) by { container_pages_backward_at(krnl.pg_arr, krnl.ctn_mp, container_ptr); };
        assert({
            &&& (current_process is Some ==> krnl.prc_mp.dom().contains(current_process.unwrap()))
            &&& (current_process is Some == current_thread is Some)
            &&& (current_process is Some ==> krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().owning_container == container_ptr)
            &&& (current_process is Some ==> {
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                &&& krnl.prc_mp.spec_index(current_process.unwrap()).view_rodata().view().depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
            })
            &&& (current_thread is Some ==> {
                let ptr = current_thread.unwrap();
                &&& krnl.thr_mp.dom().contains(ptr)
                &&& krnl.thr_mp.spec_index(ptr).view().container_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().container_depth
                &&& krnl.thr_mp.spec_index(ptr).view().process_depth == krnl.cpu_arr.spec_index(cpu_id).view().view().view().process_depth
                &&& krnl.thr_mp.spec_index(ptr).view().state == (ThreadState::RUNNING { cpu_id })
                &&& krnl.thr_mp.spec_index(ptr).view().owning_proc == current_process.unwrap()
                &&& krnl.thr_mp.spec_index(ptr).view().owning_container == container_ptr
            })
        }) by {
            thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); container_cpu_wf_cpu_at(krnl.ctn_mp, krnl.cpu_set_mp, krnl.cpu_arr, cpu_id);
            if current_thread is Some { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, current_thread.unwrap()); }
            if current_process is Some { container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, current_process.unwrap()); }
        };
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
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(old(steps).snapshot_k())) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl); };
            cpu_offline_check_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, *pt_regs);
            cpu_offline_check_result_from_k(&old(steps).snapshot_k(), cpu_id, OfflineCheckResult::Continue);
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
                assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(old(steps).snapshot_k())) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl); };
                cpu_offline_check_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, *pt_regs);
                cpu_offline_check_result_from_k(&old(steps).snapshot_k(), cpu_id, OfflineCheckResult::Continue);
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
                assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(old(steps).snapshot_k())) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&old(steps).snapshot_k(), &*krnl); };
                cpu_offline_check_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id, *pt_regs);
                cpu_offline_check_result_from_k(&old(steps).snapshot_k(), cpu_id, OfflineCheckResult::Continue);
            }
            return OfflineCheckResult::Continue;
        }
        thread_lock_perm = res;
    }
    let container_ro = krnl.ctn_mp.borrow_rodata(container_ptr).borrow();
    let scheduler_ptr = container_ro.scheduler;
    let cpu_set_ptr = container_ro.cpu_set;
    proof { container_scheduler_wf_at(krnl.ctn_mp, krnl.sched_mp, container_ptr); assert(krnl.cpu_set_mp.dom().contains(cpu_set_ptr)) by { container_cpu_set_wf_container_at(krnl.ctn_mp, krnl.cpu_set_mp, container_ptr); }; }
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(cpu_set_ptr, Tracked(&mut *lctx));
    let Tracked(scheduler_lock_perm) = krnl.wlock_scheduler_shard(scheduler_ptr, cpu_id, Tracked(&mut *lctx));
    proof {
        assert(current_thread is Some ==> !krnl.sched_mp.spec_index(scheduler_ptr).shard(cpu_id).queue.view().contains(current_thread.unwrap())) by { container_thread_scheduler_wf_at(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp, scheduler_ptr, cpu_id, current_thread.unwrap()); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
    }
    cpu_offline_commit(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, pt_regs, container_ptr, scheduler_ptr, cpu_set_ptr, flags_ptr, current_process, current_thread,
        process_lock_perm, thread_lock_perm, Tracked(cpu_lock_perm), Tracked(flag_lock_perm), Tracked(cpu_set_lock_perm), Tracked(scheduler_lock_perm),
    );
    proof { cpu_offline_check_result_from_k(&old(steps).snapshot_k(), cpu_id, OfflineCheckResult::Off); }
    OfflineCheckResult::Off
}
} // verus!
