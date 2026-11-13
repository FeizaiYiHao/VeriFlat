//! Round 8: what a step of a family other than `kill_process` leaves alone for the kill invariants, and that it keeps
//! them. A step of `d` changes only `d`'s own process, never a process or thread another cpu write-holds in the fields the
//! kill reads, makes no thread dangling, and leaves every changed or new thread well formed.
use vstd::prelude::*;
use crate::*;
use crate::trace::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::family_kill::*;
use crate::kill_steps::*;
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;
use crate::family_alloc::*;
use crate::family_new_thread::*;
use crate::family_cpu::*;
use crate::family_pci::*;
use crate::family_schedule::*;
use crate::family_env::*;
use crate::family_split_merge::*;
use veriflat_map_4k::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;
use veriflat_syscall_new_thread::{syscall_new_endpoint::syscall_new_endpoint_spec::*, syscall_new_thread::syscall_new_thread_spec::*};
use veriflat_syscall_alloc_quota::syscall_alloc_quota::{syscall_alloc_quota_spec::*, syscall_alloc_quota_1g_spec::*};
use veriflat_syscall_cpu_hotplug::syscall_cpu_hotplug::syscall_cpu_hotplug_spec::*;
use veriflat_syscall_pci::syscall_pci::syscall_pci_spec::*;
use veriflat_syscall_schedule::{rebalance_pull::rebalance_pull_spec::*, syscall_schedule::syscall_schedule_spec::*};
use veriflat_syscall_split_2m::syscall_split_2m::syscall_split_2m_spec::*;
use veriflat_syscall_merge_2m::syscall_merge_2m::syscall_merge_2m_spec::*;

verus! {
/// The threads of `p` after the step were its threads before or are new.
pub open spec fn owned_grown_fresh(u: KernelU, u2: KernelU, p: RwLockProcessPtr) -> bool {
    &&& u2.process_map[p].owned_threads.no_duplicates()
    &&& forall|t: RwLockThreadPtr| #![trigger u2.process_map[p].owned_threads.contains(t)] u2.process_map[p].owned_threads.contains(t)
        ==> u.process_map[p].owned_threads.contains(t) || !u.thread_map.dom().contains(t) && u2.thread_map.dom().contains(t) && u2.thread_map[t].owning_proc == p
}

/// The children of `p` after the step are its children before and new processes naming `p` as their parent.
pub open spec fn children_grown_fresh(u: KernelU, u2: KernelU, p: RwLockProcessPtr) -> bool {
    &&& u2.process_map[p].children.no_duplicates()
    &&& forall|ch: RwLockProcessPtr| #![trigger u.process_map[p].children.contains(ch)] u.process_map[p].children.contains(ch) ==> u2.process_map[p].children.contains(ch)
    &&& forall|ch: RwLockProcessPtr| #![trigger u2.process_map[p].children.contains(ch)] u2.process_map[p].children.contains(ch) ==> u.process_map[p].children.contains(ch)
        || !u.process_map.dom().contains(ch) && u2.process_map.dom().contains(ch) && u2.process_map[ch].parent == Some(p)
            && u2.process_map[ch].uppertree_seq == u2.process_map[p].uppertree_seq.push(p)
}

/// Process `p` keeps its parent, ancestors, mark, and table presence; its children change only while `d` holds it, by new
/// processes; its lock changes only from unlocked or from `d`, and its threads only while `d` holds it; it changes beyond
/// its subtree set only as `d`'s running process or while `d` holds it.
pub open spec fn proc_kept(u: KernelU, u2: KernelU, d: CpuId, p: RwLockProcessPtr) -> bool {
    let a = u.process_map[p];
    let b = u2.process_map[p];
    &&& b.parent == a.parent && b.uppertree_seq == a.uppertree_seq && b.depth == a.depth
    &&& b.children != a.children ==> a.lock_state == (LockStateU::WriteLocked { writer: d }) && children_grown_fresh(u, u2, p)
    &&& b.killed == a.killed && b.zombie == a.zombie && (b.pagetable is Some) == (a.pagetable is Some)
    &&& b.lock_state != a.lock_state ==> a.lock_state is Unlocked || a.lock_state == (LockStateU::WriteLocked { writer: d })
    &&& b.owned_threads != a.owned_threads ==> a.lock_state == (LockStateU::WriteLocked { writer: d }) && owned_grown_fresh(u, u2, p) && !a.zombie
    &&& proc_kview(b) != proc_kview(a)
        ==> index_valid(NUM_CPUS, d) && u.cpu_array[d as int].current_thread is Some && u.cpu_array[d as int].current_process == Some(p)
            || a.lock_state == (LockStateU::WriteLocked { writer: d })
}

/// A process the step creates is unmarked, write-held by `d`, without threads or children, and well formed.
pub open spec fn proc_new_ok(u2: KernelU, d: CpuId, p: RwLockProcessPtr) -> bool {
    let b = u2.process_map[p];
    &&& !b.killed && b.lock_state == (LockStateU::WriteLocked { writer: d }) && b.owned_threads.len() == 0 && b.children.len() == 0
    &&& proc_wf_at(u2, p)
}

/// Thread `t` keeps its mark, keeps what the kill reads while another cpu holds it, does not become dangling, and stays
/// well formed; a new thread is well formed and not dangling.
pub open spec fn thread_kept(u: KernelU, u2: KernelU, d: CpuId, t: RwLockThreadPtr) -> bool {
    let a = u.thread_map[t];
    let b = u2.thread_map[t];
    &&& u.thread_map.dom().contains(t) ==> {
        &&& b.killed == a.killed && b.owning_proc == a.owning_proc
        &&& a.lock_state is WriteLocked && a.lock_state->WriteLocked_writer != d ==> b.lock_state == a.lock_state && b.state == a.state
            && b.blocking_endpoint_ptr == a.blocking_endpoint_ptr && b.syscall_progress == a.syscall_progress && b.caller == a.caller
            && b.endpoint_descriptors == a.endpoint_descriptors && b.quota_4k == a.quota_4k && b.quota_2m == a.quota_2m && b.quota_1g == a.quota_1g
            && b.owning_container == a.owning_container
        &&& b.state is DANGLING ==> a.state is DANGLING
        &&& thread_wf_at(b) || thread_wf_view(b) == thread_wf_view(a)
    }
    &&& !u.thread_map.dom().contains(t) ==> thread_wf_at(b) && !(b.state is DANGLING)
}

/// The kill frame of a step of `d` outside `kill_process`.
pub open spec fn kill_frame(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    &&& u.process_map.dom().subset_of(u2.process_map.dom())
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) ==> proc_kept(u, u2, d, p)
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u2.process_map.dom().contains(p) && !u.process_map.dom().contains(p) ==> proc_new_ok(u2, d, p)
    &&& u.thread_map.dom().subset_of(u2.thread_map.dom())
    &&& forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) ==> thread_kept(u, u2, d, t)
    &&& forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && cpu_outside(u2, x) && u2.cpu_array[x as int].op is InStep
        ==> cpu_outside(u, x) && u.cpu_array[x as int].op is InStep
    &&& u2.kernel_l4_end == u.kernel_l4_end
    &&& in_kill(u, d) || in_kill(u2, d) ==> u2.process_map == u.process_map && u2.thread_map == u.thread_map
        && u2.cpu_array[d as int].lock_state == u.cpu_array[d as int].lock_state && u2.cpu_array[d as int].current_thread == u.cpu_array[d as int].current_thread
        && u2.cpu_array[d as int].current_process == u.cpu_array[d as int].current_process
    &&& index_valid(NUM_CPUS, d) && !cpu_outside(u2, d) && u2.cpu_array[d as int].current_thread is Some ==> cur_thread(u2, d).lock_state == (LockStateU::WriteLocked { writer: d })
        || !cpu_outside(u, d) && u2.cpu_array[d as int].current_thread == u.cpu_array[d as int].current_thread && cur_thread(u2, d).lock_state == cur_thread(u, d).lock_state
            && cur_thread(u, d).lock_state == (LockStateU::WriteLocked { writer: d })
        || cur_thread(u2, d).syscall_progress is None
}

/// `d`'s running process has a thread, so an empty process is not `d`'s.
proof fn running_process_has_thread(u: KernelU, d: CpuId, p: RwLockProcessPtr)
    requires kernel_u_ownership_wf(u), index_valid(NUM_CPUS, d), u.cpu_array[d as int].current_thread is Some, u.cpu_array[d as int].current_process == Some(p),
    ensures u.process_map[p].owned_threads.len() > 0,
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    let t = u.cpu_array[d as int].current_thread->Some_0;
    assert(u.thread_map.dom().contains(t));
    assert(u.process_map[p].owned_threads.contains(t));
}

/// A process that a cpu other than `d` write-holds stays with its depth, and one without threads keeps everything but its
/// subtree set.
pub open spec fn empty_held_procs_kept(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d)
        && u.process_map[p].owned_threads.len() == 0 ==> u2.process_map.dom().contains(p) && proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p])
    &&& forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d)
        ==> u2.process_map.dom().contains(p) && u2.process_map[p].depth == u.process_map[p].depth
}

pub proof fn kill_frame_implies_empty_held_procs_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_frame(u, u2, d),
    ensures empty_held_procs_kept(u, u2, d),
{
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d)
        && u.process_map[p].owned_threads.len() == 0 implies u2.process_map.dom().contains(p) && proc_kview(u2.process_map[p]) == proc_kview(u.process_map[p]) by {
        assert(proc_kept(u, u2, d, p));
        if proc_kview(u2.process_map[p]) != proc_kview(u.process_map[p]) { running_process_has_thread(u, d, p); }
    };
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) && held_by_other(u.process_map[p].lock_state, d)
        implies u2.process_map.dom().contains(p) && u2.process_map[p].depth == u.process_map[p].depth by { assert(proc_kept(u, u2, d, p)); };
}

pub proof fn kill_d_frame_implies_empty_held_procs_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kill_d_frame(u, u2, d),
    ensures empty_held_procs_kept(u, u2, d),
{}

/// A killer other than `d` keeps what it holds across a step with the kill frame.
proof fn kill_frame_implies_kill_holds_kept(u: KernelU, u2: KernelU, d: CpuId, x: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), kill_frame(u, u2, d), x != d, in_kill(u, x), cpu_kept(u, u2, x),
    ensures kill_holds(u2, x),
{
    reveal(kernel_u_process_ownership_wf);
    kill_holds_at(u, x);
    let pp = kill_own(u, x);
    let tp = kill_target(u, x);
    let st = kill_stage(u, x);
    assert(u2.cpu_array[x as int] == u.cpu_array[x as int] && cur_thread(u2, x) == cur_thread(u, x));
    assert(kill_target(u2, x) == tp && kill_stage(u2, x) == st && kill_own(u2, x) == pp);
    assert(proc_kept(u, u2, d, pp) && proc_kept(u, u2, d, tp));
    assert forall|q: RwLockProcessPtr| #![trigger u2.process_map[kill_target(u2, x)].uppertree_seq.contains(q)]
        u2.process_map.dom().contains(q) && u2.process_map[kill_target(u2, x)].uppertree_seq.contains(q) && u2.process_map[q].uppertree_seq.contains(pp)
        implies u2.process_map[q].killed && u2.process_map[q].lock_state == (LockStateU::WriteLocked { writer: x }) by {
        assert(proc_kept(u, u2, d, q));
    };
    if st is Thread {
        let v = st->Thread_thread;
        assert(u.thread_map.dom().contains(v));
        assert(thread_kept(u, u2, d, v));
    }
    if u.process_map[tp].owned_threads.len() == 0 && proc_kview(u2.process_map[tp]) != proc_kview(u.process_map[tp]) {
        running_process_has_thread(u, d, tp);
    }
}

/// Every step with the kill frame keeps the kill invariants.
pub proof fn kill_frame_implies_kill_world_inv_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), others_kept(u, u2, d), kill_frame(u, u2, d),
    ensures kill_world_inv(u2),
{
    reveal(kernel_u_process_threads_wf); reveal(kernel_u_process_ownership_wf);
    if in_kill(u, d) || in_kill(u2, d) {
        assert(cur_thread(u2, d) == cur_thread(u, d));
        assert(in_kill(u, d) && in_kill(u2, d));
        kill_holds_at(u, d);
        assert(kill_target(u2, d) == kill_target(u, d) && kill_stage(u2, d) == kill_stage(u, d) && kill_own(u2, d) == kill_own(u, d));
    }
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] in_kill(u2, x) implies kill_holds(u2, x) by {
        if x != d {
            assert(cpu_kept(u, u2, x));
            assert(in_kill(u, x));
            kill_frame_implies_kill_holds_kept(u, u2, d, x);
        }
    };
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p].killed] u2.process_map.dom().contains(p) && u2.process_map[p].killed implies {
        let w = u2.process_map[p].lock_state->WriteLocked_writer;
        &&& u2.process_map[p].lock_state is WriteLocked
        &&& in_kill(u2, w)
        &&& kill_on_path(u2, w, p)
    } by {
        if !u.process_map.dom().contains(p) { assert(proc_new_ok(u2, d, p)); }
        assert(proc_kept(u, u2, d, p));
        assert(u.process_map[p].killed);
        let w = u.process_map[p].lock_state->WriteLocked_writer;
        assert(in_kill(u, w));
        if w != d { assert(cpu_kept(u, u2, w)); }
        assert(cur_thread(u2, w) == cur_thread(u, w));
        let tw = kill_target(u, w);
        assert(proc_kept(u, u2, d, tw));
        if p != tw { assert(proc_kept(u, u2, d, p)); }
    };
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_wf_at(u2.thread_map[t]) by {
        assert(thread_kept(u, u2, d, t));
    };
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) implies {
        &&& cpu_outside(u2, x) ==> !(u2.cpu_array[x as int].op is InStep)
        &&& !cpu_outside(u2, x) && u2.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x).lock_state == (LockStateU::WriteLocked { writer: x }) || cur_thread(u2, x).syscall_progress is None
    } by {
        assert(u.cpu_array[x as int] == u.cpu_array[x as int]);
        if x != d { assert(cpu_kept(u, u2, x)); }
    };
    assert forall|p: RwLockProcessPtr| #![trigger proc_wf_at(u2, p)] u2.process_map.dom().contains(p) implies proc_wf_at(u2, p) by {
        if !u.process_map.dom().contains(p) { assert(proc_new_ok(u2, d, p)); } else {
            proc_wf_at_of(u, p);
            let a = u.process_map[p];
            let b = u2.process_map[p];
            assert(proc_kept(u, u2, d, p));
            assert forall|ch: RwLockProcessPtr| #![trigger b.children.contains(ch)] b.children.contains(ch)
                implies u2.process_map.dom().contains(ch) && u2.process_map[ch].parent == Some(p) && u2.process_map[ch].uppertree_seq == b.uppertree_seq.push(p) by {
                if a.children.contains(ch) { assert(proc_kept(u, u2, d, ch)); } else { assert(children_grown_fresh(u, u2, p)); }
            };
            if b.parent is Some {
                let par = b.parent->Some_0;
                assert(proc_kept(u, u2, d, par));
                assert(a.parent == Some(par) && u.process_map[par].children.contains(p));
                if u2.process_map[par].children != u.process_map[par].children { assert(children_grown_fresh(u, u2, par)); }
            }
            assert forall|q: RwLockProcessPtr| #![trigger b.uppertree_seq.contains(q)] b.uppertree_seq.contains(q) && u2.process_map.dom().contains(q)
                implies u2.process_map[q].uppertree_seq.len() < b.uppertree_seq.len() by { assert(proc_kept(u, u2, d, q)); };
            assert forall|t: RwLockThreadPtr| #![trigger b.owned_threads.contains(t)] b.owned_threads.contains(t)
                implies !(u2.thread_map[t].state is DANGLING) && u2.thread_map[t].owning_proc == p by {
                if a.owned_threads.contains(t) {
                    assert(u.thread_map.dom().contains(t));
                    assert(thread_kept(u, u2, d, t));
                } else {
                    assert(owned_grown_fresh(u, u2, p));
                    assert(thread_kept(u, u2, d, t));
                }
            };
        }
    };
}

/// A traced step outside endpoint creation keeps the kill frame.
pub proof fn traced_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), new_endpoint_locks_held(u), traced_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    reveal(thread_pagetable_op_locked);
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => {
            reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed);
            assert(in_new_endpoint(u, d));
        },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); },
        StepLabel::Unmap4kEnter { range } => { reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); },
        StepLabel::Unmap4kLeaf => { reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); },
        StepLabel::Unmap4kTlbFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => { reveal(unmap_4k_refund_step_pre); reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); },
        _ => {},
    }
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) implies proc_kept(u, u2, d, p) by {
        assert(u2.process_map[p].lock_state != u.process_map[p].lock_state ==> u.process_map[p].lock_state is Unlocked || u.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d }));
        assert(u2.process_map[p].owned_threads != u.process_map[p].owned_threads ==> u.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d }) && owned_grown_fresh(u, u2, p)
            && !u.process_map[p].zombie);
    };
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_kept(u, u2, d, t) by {
        if u.thread_map.dom().contains(t) {
            assert(u2.thread_map[t].killed == u.thread_map[t].killed && u2.thread_map[t].owning_proc == u.thread_map[t].owning_proc);
            assert(u2.thread_map[t].state is DANGLING ==> u.thread_map[t].state is DANGLING);
            assert(thread_wf_at(u2.thread_map[t]) || thread_wf_view(u2.thread_map[t]) == thread_wf_view(u.thread_map[t]));
        }
    };
    assert(!in_kill(u, d) && !in_kill(u2, d));
    assert(forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && cpu_outside(u2, x) && u2.cpu_array[x as int].op is InStep
        ==> cpu_outside(u, x) && u.cpu_array[x as int].op is InStep);
    assert(!cpu_outside(u2, d) && u2.cpu_array[d as int].current_thread is Some ==> cur_thread(u2, d).lock_state == (LockStateU::WriteLocked { writer: d })
        || !cpu_outside(u, d) && u2.cpu_array[d as int].current_thread == u.cpu_array[d as int].current_thread && cur_thread(u2, d).lock_state == cur_thread(u, d).lock_state
            && cur_thread(u, d).lock_state == (LockStateU::WriteLocked { writer: d }));
    assert(u2.process_map.dom() == u.process_map.dom() && u.thread_map.dom().subset_of(u2.thread_map.dom()) && u2.kernel_l4_end == u.kernel_l4_end);

}

/// A quota allocation keeps the kill frame.
pub proof fn alloc_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), alloc_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::AllocThreadQuota4k { alloc_amount } => { reveal(alloc_thread_quota_4k_step_pre); reveal(kernel_u_only_process2thread_quota_4k_changed); },
        StepLabel::AllocQuota2m { alloc_amount } => { reveal(alloc_quota_2m_step_pre); reveal(kernel_u_only_process_quota_2m_changed); },
        StepLabel::AllocThreadQuota2m { alloc_amount } => { reveal(alloc_thread_quota_2m_step_pre); reveal(kernel_u_only_process2thread_quota_2m_changed); },
        StepLabel::AllocQuota1g { alloc_amount } => { reveal(alloc_quota_1g_step_pre); reveal(kernel_u_only_process_quota_1g_changed); },
        StepLabel::AllocThreadQuota1g { alloc_amount } => { reveal(alloc_thread_quota_1g_step_pre); reveal(kernel_u_only_process2thread_quota_1g_changed); },
        _ => {},
    }
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) implies proc_kept(u, u2, d, p) by {
        assert(u2.process_map[p].lock_state != u.process_map[p].lock_state ==> u.process_map[p].lock_state is Unlocked || u.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d }));
        assert(u2.process_map[p].owned_threads != u.process_map[p].owned_threads ==> u.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d }) && owned_grown_fresh(u, u2, p)
            && !u.process_map[p].zombie);
    };
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_kept(u, u2, d, t) by {
        if u.thread_map.dom().contains(t) {
            assert(u2.thread_map[t].killed == u.thread_map[t].killed && u2.thread_map[t].owning_proc == u.thread_map[t].owning_proc);
            assert(u2.thread_map[t].state is DANGLING ==> u.thread_map[t].state is DANGLING);
            assert(thread_wf_at(u2.thread_map[t]) || thread_wf_view(u2.thread_map[t]) == thread_wf_view(u.thread_map[t]));
        }
    };
    assert(!in_kill(u, d) && !in_kill(u2, d));
    assert(forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && cpu_outside(u2, x) && u2.cpu_array[x as int].op is InStep
        ==> cpu_outside(u, x) && u.cpu_array[x as int].op is InStep);
    assert(!cpu_outside(u2, d) && u2.cpu_array[d as int].current_thread is Some ==> cur_thread(u2, d).lock_state == (LockStateU::WriteLocked { writer: d })
        || !cpu_outside(u, d) && u2.cpu_array[d as int].current_thread == u.cpu_array[d as int].current_thread && cur_thread(u2, d).lock_state == cur_thread(u, d).lock_state
            && cur_thread(u, d).lock_state == (LockStateU::WriteLocked { writer: d }));
    assert(u2.process_map.dom() == u.process_map.dom() && u.thread_map.dom().subset_of(u2.thread_map.dom()) && u2.kernel_l4_end == u.kernel_l4_end);

}

/// A thread-creation step keeps the kill frame: the new thread is scheduled, unlocked, and joins the process `d` holds.
pub proof fn new_thread_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), new_thread_locks_held(u), new_thread_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_threads_wf);
    match l {
        StepLabel::NewThreadEnter { regs, endpoint_index } => { reveal(new_thread_enter_step_pre); reveal(new_thread_enter_step); },
        StepLabel::NewThreadFinish => {
            reveal(new_thread_finish_step_pre); reveal(new_thread_finish_step); reveal(kernel_u_new_thread_changed);
            assert(in_new_thread(u, d) && new_thread_holds(u, d));
            let pd = u.cpu_array[d as int].current_process->Some_0;
            proc_wf_at_of(u, pd);
            running_process_has_thread(u, d, pd);
            let s = u.process_map[pd].owned_threads;
            let n = u2.process_map[pd].owned_threads.last();
            assert(u2.process_map[pd].owned_threads == s.push(n) && !u.thread_map.dom().contains(n));
            assert(!s.contains(n));
            assert(s.push(n).no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < s.push(n).len() && 0 <= j < s.push(n).len() && i != j implies s.push(n)[i] != s.push(n)[j] by {
                    if i < s.len() && j < s.len() {} else if i < s.len() { assert(s.contains(s[i])); } else { assert(s.contains(s[j])); }
                };
            };
            assert forall|t: RwLockThreadPtr| #![trigger u2.process_map[pd].owned_threads.contains(t)] u2.process_map[pd].owned_threads.contains(t)
                implies s.contains(t) || !u.thread_map.dom().contains(t) && u2.thread_map.dom().contains(t) by {
                let i = choose|i: int| 0 <= i < s.push(n).len() && s.push(n)[i] == t;
                if i < s.len() { assert(s[i] == t); }
            };
        },
        _ => {},
    }
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) implies proc_kept(u, u2, d, p) by {
        assert(u2.process_map[p].lock_state != u.process_map[p].lock_state ==> u.process_map[p].lock_state is Unlocked || u.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d }));
        assert(u2.process_map[p].owned_threads != u.process_map[p].owned_threads ==> u.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d }) && owned_grown_fresh(u, u2, p)
            && !u.process_map[p].zombie);
    };
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_kept(u, u2, d, t) by {
        if u.thread_map.dom().contains(t) {
            assert(u2.thread_map[t].killed == u.thread_map[t].killed && u2.thread_map[t].owning_proc == u.thread_map[t].owning_proc);
            assert(u2.thread_map[t].state is DANGLING ==> u.thread_map[t].state is DANGLING);
            assert(thread_wf_at(u2.thread_map[t]) || thread_wf_view(u2.thread_map[t]) == thread_wf_view(u.thread_map[t]));
        }
    };
    assert(!in_kill(u, d) && !in_kill(u2, d));
    assert(forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && cpu_outside(u2, x) && u2.cpu_array[x as int].op is InStep
        ==> cpu_outside(u, x) && u.cpu_array[x as int].op is InStep);
    assert(!cpu_outside(u2, d) && u2.cpu_array[d as int].current_thread is Some ==> cur_thread(u2, d).lock_state == (LockStateU::WriteLocked { writer: d })
        || !cpu_outside(u, d) && u2.cpu_array[d as int].current_thread == u.cpu_array[d as int].current_thread && cur_thread(u2, d).lock_state == cur_thread(u, d).lock_state
            && cur_thread(u, d).lock_state == (LockStateU::WriteLocked { writer: d }));
    assert(u2.process_map.dom() == u.process_map.dom() && u.thread_map.dom().subset_of(u2.thread_map.dom()) && u2.kernel_l4_end == u.kernel_l4_end);

}

/// A hotplug request keeps the kill frame.
pub proof fn cpu_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), cpu_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    match l {
        StepLabel::CpuOfflineRequest { target } => { reveal(cpu_offline_request_step_pre); reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOnline { target } => { reveal(cpu_online_step_pre); reveal(kernel_u_cpu_online_changed); },
        StepLabel::CpuOfflineRequestChild { target } => { reveal(cpu_offline_request_child_step_pre); reveal(kernel_u_cpu_offline_request_changed); },
        StepLabel::CpuOnlineChild { target } => { reveal(cpu_online_child_step_pre); reveal(kernel_u_cpu_online_changed); },
        _ => {},
    }
}

/// A PCI attach keeps the kill frame.
pub proof fn pci_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), pci_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::PciAttach { bus, device, function } => { reveal(pci_attach_dma_step_pre); reveal(kernel_u_pci_attach_changed); },
        _ => {},
    }
    assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p) implies proc_kept(u, u2, d, p) by {
        assert(u2.process_map[p].lock_state != u.process_map[p].lock_state ==> u.process_map[p].lock_state is Unlocked || u.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d }));
        assert(u2.process_map[p].owned_threads != u.process_map[p].owned_threads ==> u.process_map[p].lock_state == (LockStateU::WriteLocked { writer: d }) && owned_grown_fresh(u, u2, p)
            && !u.process_map[p].zombie);
    };
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_kept(u, u2, d, t) by {
        if u.thread_map.dom().contains(t) {
            assert(u2.thread_map[t].killed == u.thread_map[t].killed && u2.thread_map[t].owning_proc == u.thread_map[t].owning_proc);
            assert(u2.thread_map[t].state is DANGLING ==> u.thread_map[t].state is DANGLING);
            assert(thread_wf_at(u2.thread_map[t]) || thread_wf_view(u2.thread_map[t]) == thread_wf_view(u.thread_map[t]));
        }
    };
    assert(!in_kill(u, d) && !in_kill(u2, d));
    assert(forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && cpu_outside(u2, x) && u2.cpu_array[x as int].op is InStep
        ==> cpu_outside(u, x) && u.cpu_array[x as int].op is InStep);
    assert(!cpu_outside(u2, d) && u2.cpu_array[d as int].current_thread is Some ==> cur_thread(u2, d).lock_state == (LockStateU::WriteLocked { writer: d })
        || !cpu_outside(u, d) && u2.cpu_array[d as int].current_thread == u.cpu_array[d as int].current_thread && cur_thread(u2, d).lock_state == cur_thread(u, d).lock_state
            && cur_thread(u, d).lock_state == (LockStateU::WriteLocked { writer: d }));
    assert(u2.process_map.dom() == u.process_map.dom() && u.thread_map.dom().subset_of(u2.thread_map.dom()) && u2.kernel_l4_end == u.kernel_l4_end);

}

/// A switch or pull keeps the kill frame: the threads it moves are unlocked.
pub proof fn schedule_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), schedule_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::Schedule { flushed_pcid } => { reveal(schedule_step_pre); reveal(kernel_u_context_switch_changed); },
        StepLabel::RebalancePull => { reveal(rebalance_pull_step_pre); reveal(kernel_u_rebalance_pull_changed); },
        _ => {},
    }
}

/// A split or merge section keeps the kill frame.
pub proof fn split_merge_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), threads_wf(u), split_merge_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    assert forall|t: RwLockThreadPtr| #![trigger u2.thread_map[t]] u2.thread_map.dom().contains(t) implies thread_kept(u, u2, d, t) by {
        if u.thread_map.dom().contains(t) { assert(thread_wf_at(u.thread_map[t])); }
    };
}

/// An environment step keeps the kill frame.
pub proof fn env_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), locked_cpus_in_step(u), env_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    env_step_implies_frame(u, u2, l, d);
    if index_valid(NUM_CPUS, d) && !cpu_outside(u, d) {
        assert(u.cpu_array[d as int] == u.cpu_array[d as int]);
        assert(u2.cpu_array == u.cpu_array && u2.thread_map == u.thread_map);
    }
    match l {
        StepLabel::TrapEnter => { reveal(kernel_u_trap_enter_step_pre); reveal(kernel_u_trap_enter_step); },
        StepLabel::TrapReturn => { reveal(kernel_u_trap_return_step_pre); reveal(kernel_u_trap_return_step); },
        StepLabel::TrapDivert => { reveal(kernel_u_trap_divert_step_pre); reveal(kernel_u_trap_divert_step); },
        StepLabel::RegsChanged { regs } => { reveal(kernel_u_regs_changed_step_pre); reveal(kernel_u_regs_changed_step); },
        StepLabel::TrapReturnValuesWritten { rax, rdx, rsi } => {
            reveal(kernel_u_trap_return_values_written_step_pre); reveal(kernel_u_trap_return_values_written_step);
        },
        StepLabel::CpuTlbFilled { cpu_id, pcid, added } => { reveal(kernel_u_cpu_tlb_filled_step); },
        StepLabel::IommuTlbFilled { did, added } => { reveal(kernel_u_iommu_tlb_filled_step); },
        StepLabel::IommuContextCacheFilled => { reveal(kernel_u_iommu_context_cache_filled_step); },
        _ => {},
    }
}
} // verus!
