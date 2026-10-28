use vstd::prelude::*;
use crate::*;
use super::syscall_thread_exit_spec::*;
use super::syscall_thread_exit_trace::*;
use super::syscall_thread_exit_drop::thread_exit_drop_descriptors;
use super::syscall_thread_exit_reclaim::thread_exit_reclaim;
use super::syscall_thread_exit_finish::thread_exit_finish;
use super::syscall_thread_exit_entry::{thread_exit_lock_entry, ThreadExitEntered};

verus! {
/// Exit the running thread. Success records an entering step that write-locks the cpu, container, process, and thread
/// and wakes the caller the thread serves with `ErrorIpcCalleeExited` or takes over the dangling thread of a killed caller; steps
/// reclaiming that dangling thread and the killed callers it takes over; one step per descriptor holding an endpoint; for the
/// process's last thread, the reclaiming steps that unmap every user 4K page of the process, flush its PCID once, and
/// return the thread's and the process's quota to their container; and a finishing step that removes the thread,
/// returns its page and quotas, makes an emptied process a zombie that releases its PCID, leaves the cpu idle, and
/// unlocks the cpu, container, and process. Failure records no step. The result is `thread_exit_syscall_result` of the
/// state at entry.
pub fn syscall_thread_exit(krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId) -> (ret: RetValueType)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is Trap,
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
        ret == thread_exit_syscall_result(kernel_k_to_kernel_u(*old(krnl)), cpu_id),
        thread_exit_syscall_trace(final(steps).view().subrange(old(steps).view().len() as int, final(steps).view().len() as int), kernel_k_to_kernel_u(*old(krnl)),
            kernel_k_to_kernel_u(*final(krnl)), cpu_id, ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed()),
        !(ret is CpuIdle && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running && !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed())
            ==> final(steps).nonlock_view().len() == 0 && kernel_k_to_nonlock_kernel_u(*final(krnl)) == kernel_k_to_nonlock_kernel_u(*old(krnl)),
{
    let entry = match thread_exit_lock_entry(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id) { Ok(entry) => entry, Err(ret) => return ret };
    let ThreadExitEntered { container_ptr, process_ptr, thread_ptr, cpu_lock_perm, container_lock_perm, process_lock_perm, thread_lock_perm } = entry;
    let Tracked(cpu_lock_perm) = cpu_lock_perm;
    let Tracked(container_lock_perm) = container_lock_perm;
    let Tracked(process_lock_perm) = process_lock_perm;
    let Tracked(thread_lock_perm) = thread_lock_perm;
    let ghost start = old(steps).view().len() as int;
    let ghost pre = kernel_k_to_kernel_u(*old(krnl));
    proof { assert(krnl.cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    thread_exit_drop_descriptors(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, Tracked(&thread_lock_perm), Ghost(start), Ghost(pre));
    proof { process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, process_ptr); krnl.prc_mp.spec_index(process_ptr).view().owned_threads.lemma_len_view(); }
    let last = krnl.prc_mp.borrow_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(&process_lock_perm)).owned_threads.len() == 1;
    if last {
        thread_exit_reclaim(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, Tracked(&cpu_lock_perm), Tracked(&process_lock_perm),
            Tracked(&thread_lock_perm), Ghost(start), Ghost(pre));
    }
    proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
    thread_exit_finish(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, container_ptr, process_ptr, thread_ptr, last, Tracked(cpu_lock_perm), Tracked(container_lock_perm),
        Tracked(process_lock_perm), Tracked(thread_lock_perm), Ghost(start), Ghost(pre));
    proof { no_locks_held_imply_all_objects_unlocked(&*krnl, &*lctx); }
    RetValueType::CpuIdle
}
} // verus!
