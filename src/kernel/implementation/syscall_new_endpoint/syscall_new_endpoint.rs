use vstd::prelude::*;
use crate::*;
use super::syscall_new_endpoint_spec::*;
use super::syscall_new_endpoint_trace::*;
use super::syscall_new_endpoint_helpers::commit_new_endpoint;

verus! {
/// Create an empty receive endpoint of the running thread's container at the caller's empty
/// descriptor `endpoint_index`, funded by one 4K quota of the caller. Success records an entering
/// step that write-locks the cpu, container, process, and thread, and a finishing step that publishes
/// the endpoint and unlocks all four. Failure records no step. The result is
/// `new_endpoint_syscall_result` of the state at entry.
pub fn syscall_new_endpoint(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, endpoint_index: EndpointIdx) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        edp_idx_valid(endpoint_index),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state == CpuState::Running,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        new_endpoint_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, endpoint_index, ret is Success),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is Success) ==> final(steps).nonlock_view().len() == 0,
        ret is Success ==> final(steps).nonlock_view().len() == 2,
        ret == new_endpoint_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index),
{
    proof { use_type_invariant(&*steps); kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    assert({
        let cpu = krnl.cpu_arr.spec_index(cpu_id).view().view();
        &&& cpu.current_process() is Some
        &&& cpu.current_thread() is Some
        &&& krnl.ctn_mp.dom().contains(cpu.owning_container())
        &&& krnl.prc_mp.dom().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.dom().contains(cpu.current_thread().unwrap())
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view_rodata().view().owning_container == cpu.owning_container()
        &&& krnl.ctn_mp.spec_index(cpu.owning_container()).view_ghost().owned_processes.view().contains(cpu.current_process().unwrap())
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_proc == cpu.current_process().unwrap()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().owning_container == cpu.owning_container()
        &&& krnl.thr_mp.spec_index(cpu.current_thread().unwrap()).view().state == (ThreadState::RUNNING { cpu_id })
        &&& krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().owned_threads.view().len() != 0
        &&& !krnl.prc_mp.spec_index(cpu.current_process().unwrap()).view().zombie
    }) by { reveal(container_process_wf); reveal(thread_cpu_wf); reveal(process_thread_wf); reveal(process_cpu_wf); };
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let process_ptr = cpu.current_process().unwrap();
    let thread_ptr = cpu.current_thread().unwrap();
    let container_ptr = cpu.owning_container();
    let container_res = krnl.wlock_container_unless_killed(container_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
            new_endpoint_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index);
            assert(new_endpoint_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index) is ErrorContainerKilled) by {
                kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_container_projection_at(&*old(krnl), container_ptr);
            };
        }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_lock_perm) = container_res.unwrap();
    let container = krnl.ctn_mp.borrow_typed(container_ptr, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(&container_lock_perm));
    if container.zombie {
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), None, None, None, None, None);
            new_endpoint_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index);
            assert(new_endpoint_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index) is ErrorContainerZombie) by {
                kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_container_projection_at(&*old(krnl), container_ptr);
            };
        }
        return RetValueType::ErrorContainerZombie;
    }
    let process_res = krnl.wlock_process_unless_killed(process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), None, None, None, None);
            new_endpoint_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index);
            assert(new_endpoint_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index) is ErrorProcessKilled) by {
                kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_container_projection_at(&*old(krnl), container_ptr);
            };
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    let thread_res = krnl.wlock_thread_unless_killed(thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            new_endpoint_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index);
            assert(new_endpoint_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index) is ErrorThreadKilled) by {
                kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_container_projection_at(&*old(krnl), container_ptr);
            };
        }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    let thread_ref = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let target_in_use = thread_ref.endpoint_descriptors.get(endpoint_index).is_some();
    let no_quota = thread_ref.quota_4k == 0;
    if target_in_use || no_quota {
        krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            steps.end_kernel_step_restored_locks(&*krnl, &*lctx, cpu_id, Some(container_ptr), Some(process_ptr), Some(thread_ptr), None, None, None);
            new_endpoint_trace_stutter(steps.view().subrange(old(steps).view().len() as int, steps.view().len() as int), kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index);
            assert(new_endpoint_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index) == if target_in_use { RetValueType::ErrorIpcEndpointTargetInUse } else { RetValueType::ErrorNoQuota }) by {
                kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_container_projection_at(&*old(krnl), container_ptr);
            };
        }
        if target_in_use { return RetValueType::ErrorIpcEndpointTargetInUse; }
        return RetValueType::ErrorNoQuota;
    }
    proof {
        assert(new_endpoint_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id, endpoint_index) is Success) by {
            kernel_cpu_thread_projection_at(&*old(krnl), cpu_id, process_ptr, thread_ptr, None); kernel_container_projection_at(&*old(krnl), container_ptr);
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    commit_new_endpoint(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, endpoint_index,
        Tracked(container_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(cpu_lock_perm),
    );
    RetValueType::Success
}
}
