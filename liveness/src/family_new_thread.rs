//! Round 5: `new_thread` and `new_thread_with_endpoint`, an enter step that write-locks the cpu, the running process,
//! the running thread, and the optional endpoint, and a finish step that creates the thread and unlocks them.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use veriflat_syscall_new_thread::syscall_new_thread::syscall_new_thread_spec::*;

verus! {
pub open spec fn new_thread_label(l: StepLabel) -> bool { l is NewThreadEnter || l is NewThreadFinish }

/// `c` is inside thread creation: its cpu is write-locked and its running thread records `NewThread` progress.
pub open spec fn in_new_thread(u: KernelU, c: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, c)
    &&& u.cpu_array[c as int].lock_state is WriteLocked
    &&& u.cpu_array[c as int].current_thread is Some
    &&& cur_thread(u, c).syscall_progress is Some
    &&& cur_thread(u, c).syscall_progress->Some_0 is NewThread
}

/// What `c` inside thread creation holds: its process and its running thread, and, with an endpoint recorded, a valid
/// descriptor naming an endpoint it write-holds.
pub open spec fn new_thread_holds(u: KernelU, c: CpuId) -> bool {
    let t = cur_thread(u, c);
    let ep_idx = t.syscall_progress->Some_0->NewThread_endpoint_index;
    let ep_ptr = t.endpoint_descriptors[ep_idx->Some_0 as int]->Some_0;
    &&& u.process_map[u.cpu_array[c as int].current_process->Some_0].lock_state == (LockStateU::WriteLocked { writer: c })
    &&& t.lock_state == (LockStateU::WriteLocked { writer: c })
    &&& ep_idx is Some ==> edp_idx_valid(ep_idx->Some_0) && t.endpoint_descriptors[ep_idx->Some_0 as int] is Some
        && u.endpoint_map[ep_ptr].lock_state == (LockStateU::WriteLocked { writer: c })
}

/// Every cpu inside thread creation holds its locks.
pub open spec fn new_thread_locks_held(u: KernelU) -> bool { forall|x: CpuId| #![trigger u.cpu_array[x as int]] in_new_thread(u, x) ==> new_thread_holds(u, x) }

/// One call with its arguments.
pub ghost struct NewThreadCall { pub regs: Registers, pub ep_idx: Option<EndpointIdx> }

/// `t` is a complete trace of `call` on `c` as its exec contract ensures it: the enter and finish steps, or nothing.
pub open spec fn new_thread_call_trace_ok(call: NewThreadCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    t.len() == 0 || new_thread_syscall_trace(t, t[0].old_u, t[1].new_u, c, call.regs, call.ep_idx, true)
}

pub open spec fn new_thread_call_bound(call: NewThreadCall) -> nat { 2 }

pub proof fn new_thread_call_trace_ok_implies_len_bounded(call: NewThreadCall, t: Seq<KernelStep>, c: CpuId)
    requires new_thread_call_trace_ok(call, t, c),
    ensures t.len() <= new_thread_call_bound(call),
{ reveal(new_thread_syscall_trace); }

/// A thread-creation step of `d` keeps every other cpu and every pagetable; `d` is unlocked before entering and after
/// finishing, and inside after entering.
pub proof fn new_thread_step_implies_others_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), new_thread_label(l), labeled_step(l, u, u2, d),
    ensures
        others_kept(u, u2, d), tables_kept(u, u2), !table_op(u, d), !table_op(u2, d), cpu_outside(u, d) || in_new_thread(u, d),
        cpu_outside(u2, d) || in_new_thread(u2, d), op_in_step_kept(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    let ud = u.cpu_array[d as int];
    match l {
        StepLabel::NewThreadEnter { regs, endpoint_index } => { reveal(new_thread_enter_step_pre); reveal(new_thread_enter_step); },
        StepLabel::NewThreadFinish => { reveal(new_thread_finish_step_pre); reveal(new_thread_finish_step); reveal(kernel_u_new_thread_changed); },
        _ => {},
    }
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        let ux = u.cpu_array[x as int];
        if ux.current_thread is Some && ux.current_thread == ud.current_thread { assert(u.thread_map[ux.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: x })); }
    };
}

/// A thread-creation step of `d` gives up no foreign hold: entering locks only unlocked objects and finishing unlocks only
/// those of `d`; after entering, `d` holds its locks.
pub proof fn new_thread_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), new_thread_locks_held(u), new_thread_label(l), labeled_step(l, u, u2, d),
    ensures foreign_holds_kept(u, u2, d), in_new_thread(u2, d) ==> new_thread_holds(u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    let ud = u.cpu_array[d as int];
    match l {
        StepLabel::NewThreadEnter { regs, endpoint_index } => { reveal(new_thread_enter_step_pre); reveal(new_thread_enter_step); },
        StepLabel::NewThreadFinish => {
            reveal(new_thread_finish_step_pre); reveal(new_thread_finish_step); reveal(kernel_u_new_thread_changed);
            assert(in_new_thread(u, d) && u.cpu_array[d as int] == ud);
        },
        _ => {},
    }
}

/// A cpu inside thread creation can finish.
pub proof fn new_thread_locks_held_implies_finish_enabled(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), new_thread_locks_held(u), in_new_thread(u, c),
    ensures new_thread_finish_step_pre(u, c),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); reveal(new_thread_finish_step_pre);
    assert(new_thread_holds(u, c) && u.cpu_array[c as int] == u.cpu_array[c as int]);
    let t = cur_thread(u, c);
    let ep_idx = t.syscall_progress->Some_0->NewThread_endpoint_index;
    if ep_idx is Some { assert(u.thread_map[u.cpu_array[c as int].current_thread->Some_0].endpoint_descriptors[ep_idx->Some_0 as int] is Some); }
}

/// A step that keeps every other cpu and every foreign hold keeps `new_thread_locks_held`, given the holds of `d` after it.
pub proof fn frame_implies_new_thread_locks_held_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        kernel_u_ownership_wf(u), new_thread_locks_held(u), others_kept(u, u2, d), foreign_holds_kept(u, u2, d),
        in_new_thread(u2, d) ==> new_thread_holds(u2, d),
    ensures new_thread_locks_held(u2),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] in_new_thread(u2, x) implies new_thread_holds(u2, x) by {
        if x != d {
            assert(cpu_kept(u, u2, x));
            let ux = u.cpu_array[x as int];
            assert(in_new_thread(u, x) && new_thread_holds(u, x));
            let t = cur_thread(u, x);
            let ep_idx = t.syscall_progress->Some_0->NewThread_endpoint_index;
            assert(u2.process_map[ux.current_process->Some_0].lock_state == u.process_map[ux.current_process->Some_0].lock_state);
            if ep_idx is Some {
                let ep_ptr = t.endpoint_descriptors[ep_idx->Some_0 as int]->Some_0;
                assert(u.thread_map[ux.current_thread->Some_0].endpoint_descriptors[ep_idx->Some_0 as int] is Some);
                assert(u2.endpoint_map[ep_ptr].lock_state == u.endpoint_map[ep_ptr].lock_state);
            }
        }
    };
}
} // verus!
