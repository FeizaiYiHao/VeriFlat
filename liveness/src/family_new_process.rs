//! Round 9: `new_process`, `new_process_with_endpoint`, and `new_process_with_iommu_and_endpoint`. The three share their
//! steps: an enter step that write-locks the cpu, the running process and thread, the container's PCID allocator, and the
//! optional endpoint, read-locks the process's pagetable, and write-locks the existing 2M windows of the range there; a
//! publish step that creates the child with its pagetable write-held and releases the process and the allocator; directory
//! and leaf steps that share the range into the child; and a finish step that creates the child's thread and unlocks
//! everything. A cpu inside always has the publish, leaf, or finish step enabled, and the trace spec bounds its steps by
//! `4 * len + 3`.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use crate::sharer_tables::*;
use crate::fill_quota::*;
use crate::family_kill::*;
use crate::kill_frame::*;
use crate::kill_steps::*;
use crate::family_new_thread::*;
use veriflat_map_4k::*;
use veriflat_map_4k::map_4k::share_mapping_4k_spec::*;
use veriflat_syscall_new_process::syscall_new_process::syscall_new_process_spec::*;

verus! {
pub open spec fn new_process_label(l: StepLabel) -> bool {
    l is NewProcessEnter || l is NewProcessPublish || l is NewProcessFinish || l is Share4kDirectory || l is Share4kLeaf
}

/// `c` is inside process creation: its cpu is write-locked and its running thread records the creation or the share into
/// the child that follows it.
pub open spec fn in_new_process(u: KernelU, c: CpuId) -> bool { table_sharer(u, c) }

/// The creation record of `c`, before and after publishing.
pub open spec fn sharer_record(u: KernelU, c: CpuId) -> NewProcessProgress {
    let prog = table_progress(u, c);
    if prog is NewProcess { prog->NewProcess_0 } else { prog->Share4k_origin->NewProcess_0 }
}

/// The 4K quota publishing takes: the child's process, pagetable object, and L4 page, plus the IOMMU table and its root.
pub open spec fn new_process_cost(rec: NewProcessProgress) -> int { if rec.with_iommu { 5 } else { 3 } }

/// What `c` inside process creation holds besides the pagetables: its running thread and the endpoint of a recorded
/// descriptor; before publishing its process, its container's PCID allocator with a free PCID, and quota for publishing and
/// one more page; after publishing the child, empty, of its container, with its IOMMU table held, the share ranges equal to
/// the recorded range, and quota for the child's thread.
pub open spec fn new_process_holds(u: KernelU, c: CpuId) -> bool {
    let t = cur_thread(u, c);
    let prog = table_progress(u, c);
    let rec = sharer_record(u, c);
    let ep_idx = rec.endpoint_index;
    let ep_ptr = t.endpoint_descriptors[ep_idx->Some_0 as int]->Some_0;
    let ctn = u.container_map[t.owning_container];
    let ch = u.process_map[rec.child->Some_0];
    &&& t.lock_state == (LockStateU::WriteLocked { writer: c })
    &&& ep_idx is Some ==> edp_idx_valid(ep_idx->Some_0) && t.endpoint_descriptors[ep_idx->Some_0 as int] is Some
        && u.endpoint_map[ep_ptr].lock_state == (LockStateU::WriteLocked { writer: c })
    &&& prog is NewProcess ==> {
        &&& u.process_map[t.owning_proc].lock_state == (LockStateU::WriteLocked { writer: c })
        &&& u.process_map[t.owning_proc].depth < usize::MAX
        &&& ctn.pcid_allocator_lock == (LockStateU::WriteLocked { writer: c })
        &&& !ctn.free_pcids.is_empty()
        &&& t.quota_4k >= new_process_cost(rec) + 1
    }
    &&& prog is Share4k ==> {
        &&& rec.child is Some
        &&& prog->Share4k_source_range == rec.range && prog->Share4k_target_range == rec.range
        &&& prog->Share4k_shared <= rec.range.len
        &&& t.quota_4k >= 1
        &&& u.process_map.dom().contains(rec.child->Some_0)
        &&& ch.lock_state == (LockStateU::WriteLocked { writer: c })
        &&& ch.owning_container == t.owning_container
        &&& ch.iommu_table is Some ==> ch.iommu_table->Some_0.lock_state == (LockStateU::WriteLocked { writer: c })
        &&& ch.owned_threads.len() == 0 && !ch.zombie
    }
}

/// Restriction `new_process_depth_room` (G21): a cpu enters process creation only from a process whose depth leaves room for
/// a child. The publish step now requires it, and U states no bound on depths.
pub open spec fn new_process_depth_room(u: KernelU, l: StepLabel, d: CpuId) -> bool {
    l is NewProcessEnter ==> u.process_map[cur_thread(u, d).owning_proc].depth < usize::MAX
}

/// Every cpu inside process creation holds its locks.
pub open spec fn new_process_locks_held(u: KernelU) -> bool { forall|x: CpuId| #![trigger table_sharer(u, x)] table_sharer(u, x) ==> new_process_holds(u, x) }

pub proof fn new_process_locks_held_implies_sharer_children_held(u: KernelU)
    requires new_process_locks_held(u),
    ensures sharer_children_held(u),
{
    assert forall|c: CpuId| #![trigger table_sharer(u, c)] table_sharer(u, c) && sharer_child(u, c) is Some
        implies u.process_map[sharer_child(u, c)->Some_0].lock_state == (LockStateU::WriteLocked { writer: c }) by { assert(new_process_holds(u, c)); };
}

/// Some step of `c` inside process creation is enabled: publishing, given a fresh child, sharing the next page, or finishing,
/// given a fresh thread.
pub open spec fn new_process_next_pre(u: KernelU, c: CpuId) -> bool {
    let t = cur_thread(u, c);
    ||| new_process_publish_step_pre(u, c) && t.quota_4k >= new_process_cost(sharer_record(u, c)) && !u.container_map[t.owning_container].free_pcids.is_empty()
    ||| share_4k_leaf_step_pre(u, c)
    ||| new_process_finish_step_pre(u, c) && t.quota_4k > 0
}

/// Never blocked inside process creation: before publishing the publish step is enabled, while pages remain the leaf step,
/// and once every page is shared the finish step.
pub proof fn new_process_invariants_implies_next_pre(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), pagetable_locks_consistent(u), table_ops_vas(u), new_process_locks_held(u), in_new_process(u, c),
    ensures new_process_next_pre(u, c),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
    assert(new_process_holds(u, c) && sharer_holds_tables(u, c) && sharer_vas(u, c));
    let tp = u.cpu_array[c as int].current_thread->Some_0;
    assert(u.thread_map.dom().contains(tp));
    let prog = table_progress(u, c);
    let rec = sharer_record(u, c);
    if prog is NewProcess {
        reveal(new_process_publish_step_pre);
    } else if prog->Share4k_shared < rec.range.len {
        reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_pre_at);
        assert(table_mapping(u, c).dom().contains(rec.range.view()[prog->Share4k_shared as int]));
    } else {
        reveal(new_process_finish_step_pre);
        if rec.endpoint_index is Some { assert(u.thread_map[tp].endpoint_descriptors[rec.endpoint_index->Some_0 as int] is Some); }
    }
}

/// One call with its arguments.
pub ghost struct NewProcessCall { pub va: VAddr, pub len: usize, pub regs: Registers, pub ep_idx: Option<EndpointIdx>, pub with_iommu: bool }

/// `t` is a complete trace of `call` on `c` as its exec contract ensures it on success, or nothing.
pub open spec fn new_process_call_trace_ok(call: NewProcessCall, t: Seq<KernelStep>, c: CpuId) -> bool {
    t.len() == 0 || new_process_commit_trace(t, t[0].old_u, c, spec_va_range_4k(call.va, call.len), call.regs, call.ep_idx, call.with_iommu)
}

/// Enter, publish, one leaf and up to three directories per page, and finish.
pub open spec fn new_process_call_bound(call: NewProcessCall) -> nat { 4 * call.len as nat + 3 }

pub proof fn new_process_call_trace_ok_implies_len_bounded(call: NewProcessCall, t: Seq<KernelStep>, c: CpuId)
    requires new_process_call_trace_ok(call, t, c),
    ensures t.len() <= new_process_call_bound(call),
{ reveal(new_process_commit_trace); }

/// A process-creation step of `d` keeps every other cpu; `d` is outside or inside process creation before and after.
pub proof fn new_process_step_implies_others_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), threads_wf(u), new_process_label(l), labeled_step(l, u, u2, d),
    ensures
        others_kept(u, u2, d), op_in_step_kept(u, u2, d), cpu_outside(u, d) || in_new_process(u, d), cpu_outside(u2, d) || in_new_process(u2, d),
        !(cpu_outside(u, d) && cpu_outside(u2, d)), !table_op(u, d), !table_op(u2, d), !table_killer(u, d), !table_killer(u2, d),
        !in_new_thread(u2, d), !in_kill(u, d), !in_kill(u2, d), others_slices_same(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    let ud = u.cpu_array[d as int];
    match l {
        StepLabel::NewProcessEnter { range, regs, endpoint_index, with_iommu } => { reveal(new_process_enter_step_pre); reveal(new_process_enter_step); },
        StepLabel::NewProcessPublish => { reveal(new_process_publish_step_pre); reveal(new_process_publish_step); },
        StepLabel::NewProcessFinish => { reveal(new_process_finish_step_pre); reveal(new_process_finish_step); reveal(kernel_u_new_thread_changed); },
        StepLabel::Share4kDirectory => {
            reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_at); reveal(share_4k_directory_pre_at);
            assert(thread_wf_at(u.thread_map[ud.current_thread->Some_0]));
        },
        StepLabel::Share4kLeaf => {
            reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_at); reveal(share_4k_leaf_pre_at);
            assert(thread_wf_at(u.thread_map[ud.current_thread->Some_0]));
        },
        _ => {},
    }
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && x != d
        implies u2.cpu_array[x as int] == u.cpu_array[x as int] && (u.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x) == cur_thread(u, x)) by {
        let ux = u.cpu_array[x as int];
        if ux.current_thread is Some && ux.current_thread == ud.current_thread { assert(u.thread_map[ux.current_thread->Some_0].state == (ThreadState::RUNNING { cpu_id: x })); }
    };
    assert forall|x: CpuId| #![trigger cpu_kept(u, u2, x)] index_valid(NUM_CPUS, x) && x != d implies cpu_kept(u, u2, x) by { assert(u2.cpu_array[x as int] == u.cpu_array[x as int]); };
}

/// A process-creation step of `d` gives up no foreign hold, and after it `d` holds what it needs inside.
pub proof fn new_process_step_implies_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires
        kernel_u_ownership_wf(u), threads_wf(u), new_process_locks_held(u), pagetable_locks_consistent(u), new_process_label(l), labeled_step(l, u, u2, d),
        new_process_depth_room(u, l, d),
    ensures foreign_holds_kept(u, u2, d), in_new_process(u2, d) ==> new_process_holds(u2, d),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf);
    new_process_step_implies_others_kept(u, u2, l, d);
    let ud = u.cpu_array[d as int];
    match l {
        StepLabel::NewProcessEnter { range, regs, endpoint_index, with_iommu } => { reveal(new_process_enter_step_pre); reveal(new_process_enter_step); },
        StepLabel::NewProcessPublish => {
            reveal(new_process_publish_step_pre); reveal(new_process_publish_step);
            assert(in_new_process(u, d) && new_process_holds(u, d));
        },
        StepLabel::NewProcessFinish => {
            reveal(new_process_finish_step_pre); reveal(new_process_finish_step); reveal(kernel_u_new_thread_changed);
            assert(in_new_process(u, d) && new_process_holds(u, d));
        },
        StepLabel::Share4kDirectory => {
            reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_at); reveal(share_4k_directory_pre_at);
            assert(in_new_process(u, d) && new_process_holds(u, d));
        },
        StepLabel::Share4kLeaf => {
            reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_at); reveal(share_4k_leaf_pre_at);
            assert(in_new_process(u, d) && new_process_holds(u, d));
        },
        _ => {},
    }
}

/// A step that keeps every other cpu, every foreign hold, and every empty process another cpu holds keeps
/// `new_process_locks_held`, given the holds of `d` after it.
pub proof fn frame_implies_new_process_locks_held_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        kernel_u_ownership_wf(u), new_process_locks_held(u), others_kept(u, u2, d), foreign_holds_kept(u, u2, d), empty_held_procs_kept(u, u2, d),
        in_new_process(u2, d) ==> new_process_holds(u2, d),
    ensures new_process_locks_held(u2),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_endpoint_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    assert forall|x: CpuId| #![trigger table_sharer(u2, x)] table_sharer(u2, x) implies new_process_holds(u2, x) by {
        if x != d {
            assert(cpu_kept(u, u2, x));
            let tx = u.cpu_array[x as int].current_thread->Some_0;
            assert(u.thread_map.dom().contains(tx));
            assert(cur_thread(u2, x) == cur_thread(u, x));
            assert(table_sharer(u, x));
            assert(new_process_holds(u, x));
            let t = cur_thread(u, x);
            let rec = sharer_record(u, x);
            assert(u.container_map.dom().contains(t.owning_container));
            assert(u.process_map.dom().contains(t.owning_proc));
            assert(u2.process_map[t.owning_proc].lock_state == u.process_map[t.owning_proc].lock_state || !(table_progress(u, x) is NewProcess));
            assert(u2.process_map[t.owning_proc].depth == u.process_map[t.owning_proc].depth || !(table_progress(u, x) is NewProcess));
            if rec.endpoint_index is Some {
                let ep_ptr = t.endpoint_descriptors[rec.endpoint_index->Some_0 as int]->Some_0;
                assert(u.thread_map[tx].endpoint_descriptors[rec.endpoint_index->Some_0 as int] is Some);
                assert(u2.endpoint_map[ep_ptr].lock_state == u.endpoint_map[ep_ptr].lock_state);
            }
            if table_progress(u, x) is Share4k {
                let chp = rec.child->Some_0;
                assert(proc_kview(u2.process_map[chp]) == proc_kview(u.process_map[chp]));
            } else {
                assert(u2.container_map[t.owning_container].pcid_allocator_lock == u.container_map[t.owning_container].pcid_allocator_lock);
            }
        }
    };
}

/// A process-creation step of `d` keeps the kill frame: it changes its own process, the child it creates and write-holds,
/// and the subtree sets of the ancestors, and the child's first thread is well formed.
pub proof fn new_process_step_implies_kill_frame(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), new_process_locks_held(u), new_process_label(l), labeled_step(l, u, u2, d),
    ensures kill_frame(u, u2, d),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_process_threads_wf); reveal(kernel_u_process_ownership_wf);
    new_process_step_implies_others_kept(u, u2, l, d);
    let ud = u.cpu_array[d as int];
    let pd = ud.current_process->Some_0;
    match l {
        StepLabel::NewProcessEnter { range, regs, endpoint_index, with_iommu } => { reveal(new_process_enter_step_pre); reveal(new_process_enter_step); },
        StepLabel::NewProcessPublish => {
            reveal(new_process_publish_step_pre); reveal(new_process_publish_step);
            assert(in_new_process(u, d) && new_process_holds(u, d));
            let child = u2.process_map[pd].children.last();
            proc_wf_at_of(u, pd);
            let s = u.process_map[pd].children;
            assert(u2.process_map[pd].children == s.push(child));
            assert(!s.contains(child));
            assert(s.push(child).no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < s.push(child).len() && 0 <= j < s.push(child).len() && i != j implies s.push(child)[i] != s.push(child)[j] by {
                    if i < s.len() && j < s.len() {} else if i < s.len() { assert(s.contains(s[i])); } else { assert(s.contains(s[j])); }
                };
            };
            assert forall|ch: RwLockProcessPtr| #![trigger u2.process_map[pd].children.contains(ch)] u2.process_map[pd].children.contains(ch)
                implies s.contains(ch) || ch == child by {
                let i = choose|i: int| 0 <= i < s.push(child).len() && s.push(child)[i] == ch;
                if i < s.len() { assert(s[i] == ch); }
            };
            assert forall|ch: RwLockProcessPtr| #![trigger s.contains(ch)] s.contains(ch) implies u2.process_map[pd].children.contains(ch) by {
                let i = choose|i: int| 0 <= i < s.len() && s[i] == ch;
                assert(s.push(child)[i] == ch);
            };
            assert(children_grown_fresh(u, u2, pd));
            let anc = u.process_map[pd].uppertree_seq.push(pd);
            assert forall|q: RwLockProcessPtr| #![trigger anc.contains(q)] anc.contains(q) && u2.process_map.dom().contains(q)
                implies u2.process_map[q].uppertree_seq.len() < anc.len() by {
                let i = choose|i: int| 0 <= i < anc.len() && anc[i] == q;
                if i < anc.len() - 1 { assert(u.process_map[pd].uppertree_seq.contains(q)); }
            };
            assert(proc_wf_at(u2, child));
            assert(proc_new_ok(u2, d, child));
            assert forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u2.process_map.dom().contains(p) && !u.process_map.dom().contains(p)
                implies proc_new_ok(u2, d, p) by { assert(p == child); };
        },
        StepLabel::NewProcessFinish => {
            reveal(new_process_finish_step_pre); reveal(new_process_finish_step); reveal(kernel_u_new_thread_changed);
            assert(in_new_process(u, d) && new_process_holds(u, d));
            let chp = sharer_record(u, d).child->Some_0;
            let s = u.process_map[chp].owned_threads;
            let n = u2.process_map[chp].owned_threads.last();
            assert(u2.process_map[chp].owned_threads == s.push(n) && !u.thread_map.dom().contains(n));
            assert(s.len() == 0);
            assert(s.push(n).no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < s.push(n).len() && 0 <= j < s.push(n).len() && i != j implies s.push(n)[i] != s.push(n)[j] by {};
            };
            assert forall|t: RwLockThreadPtr| #![trigger u2.process_map[chp].owned_threads.contains(t)] u2.process_map[chp].owned_threads.contains(t)
                implies s.contains(t) || !u.thread_map.dom().contains(t) && u2.thread_map.dom().contains(t) && u2.thread_map[t].owning_proc == chp by {
                let i = choose|i: int| 0 <= i < s.push(n).len() && s.push(n)[i] == t;
            };
        },
        StepLabel::Share4kDirectory => {
            reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_at); reveal(share_4k_directory_pre_at);
            assert(in_new_process(u, d) && new_process_holds(u, d));
        },
        StepLabel::Share4kLeaf => {
            reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_at); reveal(share_4k_leaf_pre_at);
            assert(in_new_process(u, d) && new_process_holds(u, d));
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
    assert(forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && cpu_outside(u2, x) && u2.cpu_array[x as int].op is InStep
        ==> cpu_outside(u, x) && u.cpu_array[x as int].op is InStep);
    assert(!cpu_outside(u2, d) && u2.cpu_array[d as int].current_thread is Some ==> cur_thread(u2, d).lock_state == (LockStateU::WriteLocked { writer: d })
        || !cpu_outside(u, d) && u2.cpu_array[d as int].current_thread == u.cpu_array[d as int].current_thread && cur_thread(u2, d).lock_state == cur_thread(u, d).lock_state
            && cur_thread(u, d).lock_state == (LockStateU::WriteLocked { writer: d }));
    assert(u.process_map.dom().subset_of(u2.process_map.dom()) && u.thread_map.dom().subset_of(u2.thread_map.dom()) && u2.kernel_l4_end == u.kernel_l4_end);
}

/// A step that only grows the windows of every pagetable, keeps every other cpu, and leaves `d` filling nothing keeps the
/// fill quota.
pub proof fn windows_grown_implies_fill_quota_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        pagetable_locks_consistent(u), fill_quota(u), others_slices_same(u, u2, d), !table_op(u2, d),
        forall|p: RwLockProcessPtr| #![trigger table_windows(u2, p)] table_present(u, p) ==> table_windows(u, p).dom().subset_of(table_windows(u2, p).dom()),
    ensures fill_quota(u2),
{
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) && table_filling(u2, c) implies fill_quota_at(u2, c) by {
        assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
        assert(table_op(u, c));
        assert(table_filling(u, c) && table_op_holds_locks(u, c));
        fill_quota_implies_fill_quota_at(u, c);
        let p = table_proc(u, c);
        assert(table_windows(u, p).dom().subset_of(table_windows(u2, p).dom()));
        windows_grown_implies_missing_pages_shrunk(table_windows(u, p), table_windows(u2, p), table_range(u, c), 0);
    };
}

/// Every process-creation step keeps pagetable lock consistency, VA progress, and the fill quota.
pub proof fn new_process_step_implies_table_invariants_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires
        kernel_u_ownership_wf(u), threads_wf(u), new_process_locks_held(u), pagetable_locks_consistent(u), table_ops_vas(u), fill_quota(u),
        new_process_label(l), labeled_step(l, u, u2, d),
    ensures pagetable_locks_consistent(u2), table_ops_vas(u2), fill_quota(u2),
{
    reveal(kernel_u_cpu_ownership_wf);
    new_process_step_implies_others_kept(u, u2, l, d);
    assert forall|x: CpuId| #![trigger other_cpu_unchanged(u, u2, x)] x != d implies other_cpu_unchanged(u, u2, x) by {
        if index_valid(NUM_CPUS, x) { assert(cpu_kept(u, u2, x)); }
    };
    let ud = u.cpu_array[d as int];
    let pd = cur_thread(u, d).owning_proc;
    match l {
        StepLabel::NewProcessEnter { range, regs, endpoint_index, with_iommu } => {
            reveal(new_process_enter_step_pre); reveal(new_process_enter_step);
            sharer_enter_implies_locks_consistent_kept(u, u2, d, pd, range);
            assert(sharer_vas(u2, d));
            table_mappings_same_implies_vas_kept(u, u2, d);
            windows_grown_implies_fill_quota_kept(u, u2, d);
        },
        StepLabel::NewProcessPublish => {
            reveal(new_process_publish_step_pre); reveal(new_process_publish_step);
            assert(in_new_process(u, d) && new_process_holds(u, d) && sharer_holds_tables(u, d));
            let ch = u2.process_map[pd].children.last();
            sharer_publish_implies_locks_consistent_kept(u, u2, d, ch);
            sharer_publish_implies_vas_kept(u, u2, d, ch);
            windows_grown_implies_fill_quota_kept(u, u2, d);
        },
        StepLabel::Share4kDirectory => {
            reveal(share_4k_directory_step_pre); reveal(share_4k_directory_step); reveal(share_4k_directory_at); reveal(share_4k_directory_pre_at);
            assert(in_new_process(u, d) && new_process_holds(u, d) && sharer_holds_tables(u, d) && sharer_vas(u, d));
            let ch = sharer_child(u, d)->Some_0;
            let old_w = table_windows(u, ch);
            let new_w = table_windows(u2, ch);
            if cur_thread(u2, d).syscall_progress->Some_0->Share4k_directory is L3 {
                assert(!new_w.dom().subset_of(old_w.dom()));
                let w0 = choose|w0: WindowVa| new_w.dom().contains(w0) && !old_w.dom().contains(w0);
                assert(new_w == pagetable_window_locks_after_new_l2_page(old_w, spec_v2l4index(w0.va), spec_v2l3index(w0.va), table_range(u, d), d));
            }
            assert(old_w.dom().subset_of(new_w.dom()));
            assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) == table_present(u, p)
                && (table_present(u, p) ==> table_lock(u2, p) == table_lock(u, p) && table_windows(u, p).dom().subset_of(table_windows(u2, p).dom())) by {};
            assert forall|p: RwLockProcessPtr, w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)]
                table_present(u2, p) && table_windows(u2, p).dom().contains(w) implies window_kept_or_new(u, u2, d, p, w) by {};
            table_frame_implies_locks_consistent_kept(u, u2, d);
            table_mappings_same_implies_vas_kept(u, u2, d);
            windows_grown_implies_fill_quota_kept(u, u2, d);
        },
        StepLabel::Share4kLeaf => {
            reveal(share_4k_leaf_step_pre); reveal(share_4k_leaf_step); reveal(share_4k_leaf_at); reveal(share_4k_leaf_pre_at);
            assert(in_new_process(u, d) && new_process_holds(u, d) && sharer_holds_tables(u, d));
            table_views_same_implies_locks_consistent_kept(u, u2, d);
            sharer_leaf_implies_vas_kept(u, u2, d);
            windows_grown_implies_fill_quota_kept(u, u2, d);
        },
        StepLabel::NewProcessFinish => {
            reveal(new_process_finish_step_pre); reveal(new_process_finish_step); reveal(kernel_u_new_thread_changed);
            assert(in_new_process(u, d) && new_process_holds(u, d) && sharer_holds_tables(u, d));
            let ch = sharer_child(u, d)->Some_0;
            sharer_finish_implies_locks_consistent_kept(u, u2, d, pd, ch);
            table_mappings_same_implies_vas_kept(u, u2, d);
            windows_grown_implies_fill_quota_kept(u, u2, d);
        },
        _ => {},
    }
}
} // verus!
