use vstd::prelude::*;
use crate::*;

verus! {
pub enum OnlineResumeResult {
    StillOff,
    Resumed,
}

/// IPI entry of a cpu that halted after going Off: under its own lock it re-reads its state and releases the lock.
/// While still Off it halts again; once `syscall_cpu_online` has published Idle it returns to the idle loop. A cpu a
/// killer marked is not waited for: it halts again as if still Off. Neither outcome changes the cpu or is a U step.
pub fn cpu_online_resume(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId) -> (ret: OnlineResumeResult)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Off || old(krnl).cpu_op.view().view()[cpu_id as int] is Idle,
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).no_locks_held(),
        old(krnl).all_objects_unlocked(old(lctx)),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == old(steps).view(),
        kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
        ret is StillOff == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off || old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()),
        forall|c: CpuId| #![trigger final(krnl).cpu_arr.spec_index(c)]
            index_valid(NUM_CPUS, c) ==> final(krnl).cpu_arr.spec_index(c).view().view().view() == old(krnl).cpu_arr.spec_index(c).view().view().view(),
{
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }
    let cpu_lock_res = krnl.wlock_own_cpu(cpu_id, Tracked(&mut *lctx));
    if cpu_lock_res.is_none() {
        proof { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); enter_kernel_view_release_preserving_lock_alignments(&*krnl, lctx); }
        halt_until_ipi(Tracked(&*lctx));
        return OnlineResumeResult::StillOff;
    }
    let Tracked(cpu_lock_perm) = cpu_lock_res.unwrap();
    let cpu = krnl.cpu_arr.borrow_typed(cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&cpu_lock_perm));
    let state = cpu.state();
    release_cpu_and_finish_syscall(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, Tracked(cpu_lock_perm));
    proof {
        assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by {
            assert(krnl.cpu_op.view().view() =~= old(krnl).cpu_op.view().view()); kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(old(krnl), &*krnl);
        };
    }
    if let CpuState::Off = state {
        halt_until_ipi(Tracked(&*lctx));
        return OnlineResumeResult::StillOff;
    }
    OnlineResumeResult::Resumed
}
}
