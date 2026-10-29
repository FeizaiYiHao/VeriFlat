use vstd::prelude::*;
use crate::*;
use veriflat_syscall_kill_process::syscall_kill_container::syscall_kill_container_spec::*;

verus! {
/// Entering a container kill on a cpu of `a` locks the cpu, its container, the running process and thread, and marks a
/// child of that container, all of `a`, so it leaves the view of `b` unchanged.
pub proof fn kill_container_enter_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, child_index: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_enter_step_pre(old_u, cpu_id, child_index),
        kill_container_enter_step(old_u, new_u, cpu_id, child_index),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_container_enter_step_pre); reveal(kill_container_enter_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let child = old_u.container_map[owner].children[child_index as int];
    assert(old_u.container_map[a].subtree_set.contains(child)) by {
        reveal(kernel_u_container_tree_wf); broadcast use vstd::seq::Seq::lemma_index_contains;
        assert(old_u.container_map[child].uppertree_seq.contains(owner));
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
    };
}

/// The step of `kill_container_enter_step_lr` preserves isolation.
pub proof fn kill_container_enter_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, child_index: usize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_enter_step_pre(old_u, cpu_id, child_index),
        kill_container_enter_step(old_u, new_u, cpu_id, child_index),
    ensures isolated(new_u, a, b),
{
    reveal(kill_container_enter_step_pre); reveal(kill_container_enter_step); reveal(kernel_u_cpu_ownership_wf);
    assert(new_u.process_map.dom() =~= old_u.process_map.dom());
    assert(forall|p: RwLockProcessPtr| #![trigger new_u.process_map[p]] new_u.process_map[p].pagetable == old_u.process_map[p].pagetable
        && new_u.process_map[p].iommu_table == old_u.process_map[p].iommu_table && new_u.process_map[p].owning_container == old_u.process_map[p].owning_container);
    assert(new_u.container_map.dom() =~= old_u.container_map.dom());
    assert(forall|c: RwLockContainerPtr| #![trigger new_u.container_map[c]] new_u.container_map[c].subtree_set == old_u.container_map[c].subtree_set);
    assert(new_u.thread_map.dom() =~= old_u.thread_map.dom());
    assert(forall|t: RwLockThreadPtr| #![trigger new_u.thread_map[t]]
        new_u.thread_map[t].owning_container == old_u.thread_map[t].owning_container && new_u.thread_map[t].state == old_u.thread_map[t].state);
}

/// Descending from the target of a container kill on a cpu of `a`, which lies in `a`, marks a child of the target, so
/// it leaves the view of `b` unchanged.
pub proof fn kill_container_mark_child_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_mark_child_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_container_step_pre); reveal(kill_container_mark_child_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = kill_container_target(old_u, cpu_id);
    let child = old_u.container_map[target].children[0];
    assert(old_u.container_map[a].subtree_set.contains(child)) by {
        reveal(kernel_u_container_tree_wf); broadcast use vstd::seq::Seq::lemma_index_contains;
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
        assert(old_u.container_map[target].uppertree_seq.contains(a));
        assert(old_u.container_map[child].uppertree_seq.contains(target));
    };
}

/// The step of `kill_container_mark_child_step_lr` preserves isolation.
pub proof fn kill_container_mark_child_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_mark_child_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_step_pre); reveal(kill_container_mark_child_step); reveal(kernel_u_cpu_ownership_wf); }

/// Marking the root process of the target of a container kill on a cpu of `a`, which lies in `a`, marks a process the
/// target owns, so it leaves the view of `b` unchanged.
pub proof fn kill_container_mark_root_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_mark_root_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_container_step_pre); reveal(kill_container_mark_root_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = kill_container_target(old_u, cpu_id);
    let root = old_u.container_map[target].root_process;
    assert(old_u.container_map[a].subtree_set.contains(target)) by {
        reveal(kernel_u_container_tree_wf);
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
        assert(old_u.container_map[target].uppertree_seq.contains(a));
    };
    assert(old_u.container_map[target].owned_processes.contains(root)) by { reveal(kernel_u_container_root_process_wf); };
    assert(old_u.process_map[root].owning_container == target) by { reveal(kernel_u_process_ownership_wf); };
}

/// The step of `kill_container_mark_root_step_lr` preserves isolation.
pub proof fn kill_container_mark_root_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_mark_root_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_step_pre); reveal(kill_container_mark_root_step); reveal(kernel_u_cpu_ownership_wf); }

/// Retiring the empty zombie root process of the target of a container kill on a cpu of `a`, which lies in `a`, removes a
/// process of the target and changes only the target, so it leaves the view of `b` unchanged.
pub proof fn kill_container_retire_root_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_retire_root_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_container_step_pre); reveal(kill_container_retire_root_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = kill_container_target(old_u, cpu_id);
    assert(old_u.container_map[a].subtree_set.contains(target)) by {
        reveal(kernel_u_container_tree_wf);
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
        assert(old_u.container_map[target].uppertree_seq.contains(a));
    };
}

/// The step of `kill_container_retire_root_step_lr` preserves isolation.
pub proof fn kill_container_retire_root_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_retire_root_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_step_pre); reveal(kill_container_retire_root_step); reveal(kernel_u_cpu_ownership_wf); }

/// Marking the cpu set of the target of a container kill on a cpu of `a`, which lies in `a`, changes only the target, so
/// it leaves the view of `b` unchanged.
pub proof fn kill_container_cpus_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_cpus_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_container_step_pre); reveal(kill_container_cpus_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = kill_container_target(old_u, cpu_id);
    assert(old_u.container_map[a].subtree_set.contains(target)) by {
        reveal(kernel_u_container_tree_wf);
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
        assert(old_u.container_map[target].uppertree_seq.contains(a));
    };
}

/// The step of `kill_container_cpus_step_lr` preserves isolation.
pub proof fn kill_container_cpus_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_cpus_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_step_pre); reveal(kill_container_cpus_step); reveal(kernel_u_cpu_ownership_wf); }

/// Moving a cpu of the target of a container kill on a cpu of `a`, which lies in `a`, to the killer's container moves it
/// within `a`, so it leaves the view of `b` unchanged.
pub proof fn kill_container_move_cpu_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_move_cpu_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_container_step_pre); reveal(kill_container_move_cpu_step); reveal(kernel_u_cpu_ownership_wf);
    broadcast use vstd::set_lib::range_set_properties;
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = kill_container_target(old_u, cpu_id);
    let moved = Set::range(0usize, NUM_CPUS).filter(|i: CpuId| old_u.cpu_array[i as int] != new_u.cpu_array[i as int]);
    assert(old_u.container_map[a].subtree_set.contains(target)) by {
        reveal(kernel_u_container_tree_wf);
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
        assert(old_u.container_map[target].uppertree_seq.contains(a));
    };
    assert(!in_domain(old_u, b, target) && !in_domain(old_u, b, owner) && new_u.container_map[b] == old_u.container_map[b]);
    assert forall|i: int| #![trigger new_u.cpu_array[i]] 0 <= i < NUM_CPUS implies
        domain_view(new_u, b).cpus[i] == domain_view(old_u, b).cpus[i] by { if !moved.contains(i as CpuId) { assert(Set::range(0usize, NUM_CPUS).contains(i as CpuId)); } };
}

/// The step of `kill_container_move_cpu_step_lr` preserves isolation.
pub proof fn kill_container_move_cpu_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_move_cpu_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_step_pre); reveal(kill_container_move_cpu_step); }

/// Moving on to the free pages of a container kill on a cpu of `a` changes only the killer, a thread of `a`.
pub proof fn kill_container_pages_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_pages_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kill_container_step_pre); reveal(kill_container_pages_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `kill_container_pages_step_lr` preserves isolation.
pub proof fn kill_container_pages_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_pages_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_step_pre); reveal(kill_container_pages_step); reveal(kernel_u_cpu_ownership_wf); }

/// Moving a free page of the target of a container kill on a cpu of `a`, which lies in `a`, to the killer's container
/// moves pages and quota within `a`, so it leaves the view of `b` unchanged.
pub proof fn kill_container_move_page_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, size: PageSize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_move_page_step(old_u, new_u, cpu_id, size),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_container_step_pre); reveal(kill_container_move_page_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = kill_container_target(old_u, cpu_id);
    assert(old_u.container_map[a].subtree_set.contains(target)) by {
        reveal(kernel_u_container_tree_wf);
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
        assert(old_u.container_map[target].uppertree_seq.contains(a));
    };
}

/// The step of `kill_container_move_page_step_lr` preserves isolation.
pub proof fn kill_container_move_page_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, size: PageSize, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_move_page_step(old_u, new_u, cpu_id, size),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_step_pre); reveal(kill_container_move_page_step); reveal(kernel_u_cpu_ownership_wf); }

/// Starting to retire the target of a container kill on a cpu of `a` changes only the killer, a thread of `a`.
pub proof fn kill_container_retire_stage_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_retire_stage_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kill_container_step_pre); reveal(kill_container_retire_stage_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `kill_container_retire_stage_step_lr` preserves isolation.
pub proof fn kill_container_retire_stage_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_retire_stage_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_step_pre); reveal(kill_container_retire_stage_step); reveal(kernel_u_cpu_ownership_wf); }

/// Retiring the empty target of a container kill on a cpu of `a`, which lies in `a`, removes it from its ancestors, none
/// of which is `b` or below it, and hands its pages to the killer's container, so it leaves the view of `b` unchanged.
pub proof fn kill_container_retire_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_retire_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{
    reveal(kill_container_step_pre); reveal(kill_container_retire_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = kill_container_target(old_u, cpu_id);
    let parent = old_u.container_map[target].parent->Some_0;
    assert(old_u.container_map[a].subtree_set.contains(target)) by {
        reveal(kernel_u_container_tree_wf);
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
        assert(old_u.container_map[target].uppertree_seq.contains(a));
    };
    assert forall|c: RwLockContainerPtr| #![trigger old_u.container_map[target].uppertree_seq.contains(c)]
        old_u.container_map[target].uppertree_seq.contains(c) implies !in_domain(old_u, b, c) by {
        reveal(kernel_u_container_tree_wf);
        if in_domain(old_u, b, c) {
            if c != b { assert(old_u.container_map[c].uppertree_seq.contains(b)); }
            assert(old_u.container_map[target].uppertree_seq.contains(b));
            assert(old_u.container_map[b].subtree_set.contains(target));
        }
    };
    assert(old_u.container_map[target].uppertree_seq.contains(parent)) by { reveal(kernel_u_container_tree_wf); };
    assert(!in_domain(old_u, b, target) && !in_domain(old_u, b, owner) && !in_domain(old_u, b, parent) && new_u.container_map[b] == old_u.container_map[b]);
}

/// The step of `kill_container_retire_step_lr` preserves isolation: it removes the target, which is neither `a` nor `b`,
/// and shrinks every subtree.
pub proof fn kill_container_retire_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_step_pre(old_u, cpu_id),
        kill_container_retire_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{
    reveal(kill_container_step_pre); reveal(kill_container_retire_step); reveal(kernel_u_cpu_ownership_wf);
    let owner = old_u.cpu_array[cpu_id as int].owning_container;
    let target = kill_container_target(old_u, cpu_id);
    assert(old_u.container_map[a].subtree_set.contains(target)) by {
        reveal(kernel_u_container_tree_wf);
        if owner != a { assert(old_u.container_map[owner].uppertree_seq.contains(a)); }
        assert(old_u.container_map[target].uppertree_seq.contains(a));
    };
    assert(target != a && target != b) by { reveal(kernel_u_container_tree_wf); reveal(kernel_u_container_depth_wf); };
    assert forall|r: RwLockContainerPtr, c: RwLockContainerPtr| #![trigger new_u.container_map[r].subtree_set.contains(c)]
        new_u.container_map.dom().contains(r) && new_u.container_map[r].subtree_set.contains(c) implies old_u.container_map[r].subtree_set.contains(c) by {};
}

/// Finishing a container kill on a cpu of `a` unlocks the cpu, its container, the running process and thread, all of
/// `a`, so it leaves the view of `b` unchanged.
pub proof fn kill_container_finish_step_lr(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_finish_step_pre(old_u, cpu_id),
        kill_container_finish_step(old_u, new_u, cpu_id),
    ensures domain_view(new_u, b) =~~= domain_view(old_u, b),
{ reveal(kill_container_finish_step_pre); reveal(kill_container_finish_step); reveal(kernel_u_cpu_ownership_wf); }

/// The step of `kill_container_finish_step_lr` preserves isolation.
pub proof fn kill_container_finish_step_iso(old_u: KernelU, new_u: KernelU, cpu_id: CpuId, a: RwLockContainerPtr, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(old_u),
        isolated(old_u, a, b),
        steps_in_domain(old_u, cpu_id, a),
        kill_container_finish_step_pre(old_u, cpu_id),
        kill_container_finish_step(old_u, new_u, cpu_id),
    ensures isolated(new_u, a, b),
{ reveal(kill_container_finish_step_pre); reveal(kill_container_finish_step); reveal(kernel_u_cpu_ownership_wf); }

/// The container kill result of a cpu of `b` reads only the view of `b`: the cpu, its container with the running process
/// and thread, and the child container at `child_index`, which lies in `b`.
pub proof fn kill_container_syscall_result_oc(u1: KernelU, u2: KernelU, cpu_id: CpuId, child_index: usize, b: RwLockContainerPtr)
    requires
        kernel_u_ownership_wf(u1),
        u1.container_map.dom().contains(b),
        steps_in_domain(u1, cpu_id, b),
        domain_view(u1, b) =~~= domain_view(u2, b),
    ensures kill_container_syscall_result(u1, cpu_id, child_index) == kill_container_syscall_result(u2, cpu_id, child_index),
{
    let cpu = u1.cpu_array[cpu_id as int];
    let children = u1.container_map[cpu.owning_container].children;
    assert({
        let v1 = domain_view(u1, b);
        let v2 = domain_view(u2, b);
        &&& v1.cpus[cpu_id as int] == Some(cpu)
        &&& v1.containers.dom().contains(cpu.owning_container) && v1.containers[cpu.owning_container] == v2.containers[cpu.owning_container]
        &&& cpu.state is Running ==> v1.processes.dom().contains(cpu.current_process->Some_0) && v1.processes[cpu.current_process->Some_0] == v2.processes[cpu.current_process->Some_0]
        &&& cpu.state is Running ==> v1.threads.dom().contains(cpu.current_thread->Some_0) && v1.threads[cpu.current_thread->Some_0] == v2.threads[cpu.current_thread->Some_0]
    }) by { reveal(kernel_u_cpu_ownership_wf); };
    if child_index < children.len() {
        let child = children[child_index as int];
        assert(domain_view(u1, b).containers.dom().contains(child)) by {
            reveal(kernel_u_container_tree_wf); reveal(kernel_u_cpu_ownership_wf); broadcast use vstd::seq::Seq::lemma_index_contains;
            assert(u1.container_map[child].uppertree_seq.contains(cpu.owning_container));
            if cpu.owning_container != b { assert(u1.container_map[cpu.owning_container].uppertree_seq.contains(b)); }
        };
        assert(domain_view(u1, b).containers[child] == domain_view(u2, b).containers[child]);
    }
}
} // verus!
