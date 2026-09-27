use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_commit::commit_new_container;

verus! {
pub fn syscall_new_container(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    va: usize, range: usize, funding_page_count: usize, process_quota_4k: usize, transfer_cpu_id: CpuId, initial_regs: &Registers,
) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state
            == CpuState::Running,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        old(steps).nonlock_view().len() == 0,
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).no_locks_held(),
        !(ret is SuccessThreeUsize) ==> final(steps).nonlock_view().len() == 0,
        ret is SuccessThreeUsize ==> range as int + 2 <= final(steps).nonlock_view().len() as int <= 4 * range as int + 2,
        ret is SuccessThreeUsize || ret is Error || ret is ErrorContainerKilled || ret is ErrorProcessKilled || ret is ErrorThreadKilled
            || ret is ErrorNoQuota || ret is ErrorIpcCpuOwnerMismatch || ret is ErrorIpcCpuNotOff,
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    if range == 0 || range > usize::MAX / 4096usize || range > (usize::MAX - 9usize) / 3usize || !va_4k_valid(va) || transfer_cpu_id >= NUM_CPUS {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::Error;
    }
    let span = range * 4096usize;
    if va >= usize::MAX - span || !va_4k_range_valid(va, range) {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::Error;
    }
    let source_range = VaRange4K::new(va, range);
    if process_quota_4k > funding_page_count || funding_page_count > usize::MAX - 9 - 3 * range {
        proof {
            enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::Error;
    }

    proof {
        assert({
            &&& krnl.cpu_arr.spec_index(cpu_id)
                .view().view().view().current_process is Some
            &&& krnl.cpu_arr.spec_index(cpu_id)
                .view().view().view().current_thread is Some
        }) by {
            reveal(cpu_array_wf);
        };
    }
    let Tracked(cpu_lock_perm) =
        krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let parent_container_ptr = cpu.owning_container();
    let parent_process_ptr = cpu.current_process().unwrap();
    let current_thread_ptr = cpu.current_thread().unwrap();
    proof {
        assert(krnl.ctn_mp.dom().contains(parent_container_ptr)) by { reveal(container_cpu_wf); };
        assert({
            &&& krnl.prc_mp.dom().contains(parent_process_ptr)
            &&& krnl.prc_mp.spec_index(parent_process_ptr)
                .view_rodata().view().owning_container
                == parent_container_ptr
        }) by {
            reveal(process_cpu_wf);
        };
        assert({
            &&& krnl.thr_mp.dom().contains(current_thread_ptr)
            &&& krnl.thr_mp.spec_index(current_thread_ptr)
                .view().state == (ThreadState::RUNNING { cpu_id })
            &&& krnl.thr_mp.spec_index(current_thread_ptr)
                .view().owning_container == parent_container_ptr
            &&& krnl.thr_mp.spec_index(current_thread_ptr)
                .view().owning_proc == parent_process_ptr
        }) by {
            reveal(thread_cpu_wf);
            reveal(process_thread_wf);
        };
    }
    let container_res = krnl.wlock_container_unless_killed(parent_container_ptr, Tracked(&mut *lctx));
    if container_res.is_none() {
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::ErrorContainerKilled;
    }
    let Tracked(container_lock_perm) = container_res.unwrap();
    proof { assert(!krnl.ctn_mp.spec_index(parent_container_ptr).view().owned_processes.view().is_empty()) by { reveal(container_process_wf); }; }
    let parent_depth = krnl.ctn_mp
        .borrow_rodata(parent_container_ptr).borrow().depth;
    if parent_depth >= MAX_CONTAINER_TREE_DEPTH {
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::Error;
    }

    let process_res = krnl.wlock_process_unless_killed(parent_process_ptr, Ghost(cpu_id), Tracked(&mut *lctx));
    if process_res.is_none() {
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::ErrorProcessKilled;
    }
    let Tracked(process_lock_perm) = process_res.unwrap();
    proof { assert(krnl.prc_mp.spec_index(parent_process_ptr).view().owned_threads.view().len() != 0) by { reveal(process_thread_wf); }; }
    let thread_res = krnl.wlock_thread_unless_killed(current_thread_ptr, Tracked(&mut *lctx));
    if thread_res.is_none() {
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::ErrorThreadKilled;
    }
    let Tracked(thread_lock_perm) = thread_res.unwrap();
    let thread = krnl.thr_mp.borrow_typed(
        current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(&thread_lock_perm));
    let quota_4k = thread.quota_4k;
    let quota_2m = thread.quota_2m;
    let source_pagetable_ptr = thread.proc_pagetable_ptr;
    let required_4k = 9usize + funding_page_count + 3 * range;
    let quota_available =
        quota_4k >= required_4k && quota_2m >= 2;
    if !quota_available {
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::ErrorNoQuota;
    }

    proof {
        assert({
            &&& krnl.pt_mp.dom().contains(source_pagetable_ptr)
            &&& !lctx.pagetable_lock_map().dom().contains(source_pagetable_ptr)
        }) by {
            reveal(process_thread_wf);
            reveal(process_pagetable_match);
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
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return RetValueType::Error;
    }
    let parent_cpu_set = krnl.ctn_mp.borrow_rodata(parent_container_ptr).borrow().cpu_set;
    proof { assert(krnl.cpu_set_mp.dom().contains(parent_cpu_set)) by { reveal(container_cpu_set_wf); }; }
    let Tracked(cpu_set_lock_perm) = krnl.wlock_cpu_set(parent_cpu_set, Tracked(&mut *lctx));
    let parent_set = krnl.cpu_set_mp.borrow_typed(parent_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&cpu_set_lock_perm));
    let transfer_cpu_owned = parent_set.owned_cpus.contains(transfer_cpu_id);
    let transfer_cpu_off = parent_set.owned_cpus.is_closed(transfer_cpu_id);
    if !transfer_cpu_owned || !transfer_cpu_off {
        krnl.wunlock_cpu_set(parent_cpu_set, Tracked(&mut *lctx), Tracked(cpu_set_lock_perm));
        krnl.wunlock_pagetable(source_pagetable_ptr, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
        krnl.wunlock_thread(current_thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
        krnl.wunlock_process(parent_process_ptr, Tracked(&mut *lctx), Tracked(process_lock_perm));
        krnl.wunlock_container(parent_container_ptr, Tracked(&mut *lctx), Tracked(container_lock_perm));
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            steps.end_kernel_step_nonlock_fields_unchanged(&*krnl, &*lctx);
        }
        return if !transfer_cpu_owned { RetValueType::ErrorIpcCpuOwnerMismatch } else { RetValueType::ErrorIpcCpuNotOff };
    }
    proof {
        assert(krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off) by { reveal(container_cpu_wf); reveal(cpu_array_wf); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
    let (child_container_ptr, child_process_ptr, new_thread_ptr) = commit_new_container(
        krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, parent_container_ptr, parent_process_ptr, current_thread_ptr,
        source_pagetable_ptr, &source_range, funding_page_count, process_quota_4k, transfer_cpu_id, parent_cpu_set,
        Tracked(cpu_lock_perm), Tracked(container_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm),
        Tracked(source_pagetable_lock_perm), Tracked(cpu_set_lock_perm), initial_regs,
    );
    RetValueType::SuccessThreeUsize { value1: child_container_ptr, value2: child_process_ptr, value3: new_thread_ptr }
}
}
