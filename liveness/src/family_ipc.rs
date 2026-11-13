//! Round 11: ordinary IPC, the IPC representative of the world. A send, receive, call, or receive-call whose endpoint
//! queue is empty or waits in the same direction blocks the caller (`IpcBlock`); one whose queue head waits in the opposite
//! direction schedules that head (`IpcRendezvous`). Each is one step from an unlocked cpu with an unlocked thread and
//! endpoint, so it has no inside and is never blocked, and a call records at most one step (`ipc_ordinary_syscall_trace`).
//! The world leaves out the rendezvous with a PCI payload, which moves a PCI function between processes that neither
//! cpu holds; the call handoff and reply, the endpoint transfer, and the pages transfer are other paths not yet in the
//! world.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::family_kill::*;
use crate::kill_frame::*;
use veriflat_syscall_ipc::syscall_ipc::syscall_ipc_spec::*;

verus! {
pub open spec fn ipc_label(l: StepLabel) -> bool { l is IpcBlock || (l is IpcRendezvous && !(l->IpcRendezvous_payload is Pci)) }

/// One call with its arguments and result.
pub ghost struct IpcCall { pub ep_idx: EndpointIdx, pub waiting_state: ThreadState, pub payload: IPCPayLoad, pub flushed_default_pcid: bool, pub ret: RetValueType }

/// `t` is a complete trace of `call` on `c` as its exec contract ensures it: the block or rendezvous step, or nothing.
pub open spec fn ipc_call_trace_ok(call: IpcCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    t.len() == 0 || ipc_ordinary_syscall_trace(t, t[0].old_u, t[0].new_u, c, call.ep_idx, call.waiting_state, call.payload, call.flushed_default_pcid, call.ret)
}

pub open spec fn ipc_call_bound(call: IpcCall) -> nat { 1 }

pub proof fn ipc_call_trace_ok_implies_len_bounded(call: IpcCall, t: Seq<KernelStep>, c: CpuId)
    requires ipc_call_trace_ok(call, t, c),
    ensures t.len() <= ipc_call_bound(call),
{ reveal(ipc_ordinary_syscall_trace); }

/// A block or rendezvous step of `d` keeps every other write-locked cpu, every lock, and every pagetable; `d` is unlocked
/// before and after. The changed threads, the caller and the queue head, are unlocked and well formed, and no process
/// changes.
pub proof fn ipc_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), threads_wf(u), ipc_label(l), labeled_step(l, u, u2, d),
    ensures single_step_frame(u, u2, d), kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(ipc_step_pre);
    match l {
        StepLabel::IpcBlock { channel_index, waiting_state, payload, flushed_default_pcid } => { reveal(ipc_block_step_pre); reveal(kernel_u_ipc_block_changed); },
        StepLabel::IpcRendezvous { channel_index, waiting_state, payload } => {
            reveal(ipc_rendezvous_step_pre); reveal(kernel_u_ipc_rendezvous_changed);
            let peer = u.endpoint_map[u.thread_map[u.cpu_array[d as int].current_thread->Some_0].endpoint_descriptors[channel_index as int]->Some_0].queue[0];
            assert(thread_wf_at(u.thread_map[peer]));
        },
        _ => {},
    }
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by {
        let ux = u.cpu_array[x as int];
        if ux.current_thread is Some { assert(u.thread_map[ux.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: x })); }
    };
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_kept(u, u2, d, t) by {
        if u.thread_map.dom().contains(t) { assert(thread_wf_at(u.thread_map[t])); }
    };
}
} // verus!
