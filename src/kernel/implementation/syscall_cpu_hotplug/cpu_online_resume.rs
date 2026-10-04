use vstd::prelude::*;
use crate::*;

verus! {
pub enum OnlineResumeResult {
    StillOff,
    Resumed,
}

/// IPI entry of a cpu that halted after going Off: under its own lock it re-reads its state. While still Off
/// it releases the lock and halts again; once `syscall_cpu_online` has published Idle it records that its
/// hardware runs again and returns to the idle loop. Neither outcome is a U step.
pub fn cpu_online_resume(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId) -> (ret: OnlineResumeResult)
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
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view().len() == 0,
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        ret is StillOff == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view() == (CpuView {
            hw_halted: if ret is StillOff { old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().hw_halted } else { false },
            ..old(krnl).cpu_arr.spec_index(cpu_id).view().view().view()
        }),
        forall|other_cpu: CpuId| #![trigger final(krnl).cpu_arr.spec_index(other_cpu)]
            index_valid(NUM_CPUS, other_cpu) && other_cpu != cpu_id ==> final(krnl).cpu_arr.spec_index(other_cpu).view().view().view() == old(krnl).cpu_arr.spec_index(other_cpu).view().view().view(),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    let Tracked(cpu_lock_perm) = krnl.wlock_cpu(cpu_id, Tracked(&mut *lctx));
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let state = cpu.state();
    proof {
        assert({
            &&& krnl.cpu_published[cpu_id as int].view() == (krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid)
            &&& krnl.cpu_arr.spec_index(cpu_id).view().view().wf()
        }) by { reveal(cpu_published_wf); reveal(cpu_array_wf); };
    }
    if let CpuState::Off = state {
        release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
        proof { assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl); }; }
        halt_until_ipi(Tracked(&*lctx));
        return OnlineResumeResult::StillOff;
    }
    let ghost locked = *krnl;
    let ghost old_lock_id = krnl.cpu_arr.lock_id_by_index(cpu_id);
    let cpu = krnl.cpu_arr.borrow_mut_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    cpu.clear_hw_halted();
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Cpu(cpu_id), old_lock_id, krnl.cpu_arr.lock_id_by_index(cpu_id));
        assert(krnl.subsystems_inv()) by { reveal(cpu_array_wf); reveal(cpu_published_wf); reveal(cpu_offline_flags_wf); reveal(KernelK::default_pagetable_wf); };
        assert(krnl.process_management_inv()) by { reveal(container_cpu_wf); reveal(process_cpu_wf); reveal(thread_cpu_wf); };
        assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by {
            reveal(cpu_dirty_map_contains_container_processes); reveal(cpu_not_in_dirty_map_imply_not_in_tlb); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_contains_pagetable_pcid_match);
        };
        assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr, krnl.pcid_needflush)) by { reveal(tlb_wf_spec); };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&locked, &*krnl)) by {
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_cpu_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&locked, &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(locked.ep_mp, krnl.ep_mp)) by { reveal(kernel_endpoint_nonlock_fields_unchanged); };
        assert({
            &&& kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)
            &&& kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)
            &&& kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp)
        }) by {
            broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive, kernel_container_nonlock_fields_and_quotas_unchanged_transitive, kernel_endpoint_nonlock_fields_unchanged_transitive;
        };
    }
    release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    proof { assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl); }; }
    OnlineResumeResult::Resumed
}
}
