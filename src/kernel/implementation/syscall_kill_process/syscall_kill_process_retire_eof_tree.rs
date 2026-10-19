use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_retire_spec::*;

verus! {
/// Dropping the retired zombie leaf keeps its container's process tree well formed, every container's process set
/// consistent with the process map, and the root container's root process.
pub(crate) proof fn kill_retire_eof_tree(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr,
)
    requires
        pre.inv(),
        kill_retire_eof_transition_framing(pre, post, cpu_id, target, parent_ptr, container_ptr, allocator_ptr),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).locking_thread() is Write,
        pre.prc_mp.spec_index(target).being_killed(),
        pre.prc_mp.spec_index(target).view().zombie,
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        pre.prc_mp.spec_index(target).view().owned_threads.view().len() == 0,
        pre.prc_mp.spec_index(target).view_ghost().owned_pci_functions.view() == Set::<PciBdf>::empty(),
        pre.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.dom().contains(parent_ptr),
        parent_ptr != target,
        pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()),
        pre.prc_mp.spec_index(parent_ptr).view().children.map().spec_index(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()) == target,
        pre.ctn_mp.dom().contains(container_ptr),
    ensures
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
        post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process),
{
    reveal(kill_retire_eof_transition_framing);
    kill_retire_eof_per_container_process_tree_wf(pre, post, container_ptr, parent_ptr, target);
    kill_retire_eof_container_process_wf(pre, post, container_ptr, parent_ptr, target);
    let root_process = pre.ctn_mp.spec_index(container_ptr).view().root_process;
    let process_tree_dom = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    assert(process_tree_dom.contains(target)) by { container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, target); };
    assert(process_tree_wf(root_process, process_tree_dom, pre.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(root_process != target) by { reveal(process_root_wf); reveal(process_children_parent_wf); };
    assert(pre.ctn_mp.dom().contains(pre.rt_ctn)) by { reveal(container_root_wf); };
}

/// Retiring the childless non-root `target` of `parent_ptr` from a tree whose processes keep their tree fields,
/// except the parent's child list and the ancestors' subtree sets, keeps the remaining tree well formed.
pub(crate) proof fn kill_retire_eof_process_tree_wf(
    pre: KernelK, post: KernelK, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, parent_ptr: RwLockProcessPtr, target: RwLockProcessPtr,
)
    requires
        process_tree_fields_wf(pre.prc_mp),
        process_tree_wf(root_process, process_tree_dom, pre.prc_mp),
        process_tree_dom.contains(target),
        pre.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        post.prc_mp.dom() == pre.prc_mp.dom().remove(target),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger post.prc_mp.spec_index(p_ptr)]
            post.prc_mp.dom().contains(p_ptr) ==> {
                &&& post.prc_mp.spec_index(p_ptr).view_rodata() == pre.prc_mp.spec_index(p_ptr).view_rodata()
                &&& post.prc_mp.spec_index(p_ptr).view().parent_linkedlist_node == pre.prc_mp.spec_index(p_ptr).view().parent_linkedlist_node
                &&& post.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq == pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq
                &&& p_ptr != parent_ptr ==> post.prc_mp.spec_index(p_ptr).view().children == pre.prc_mp.spec_index(p_ptr).view().children
                &&& pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
                    ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view().remove(target)
                &&& !pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
                    ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set
            },
        post.prc_mp.spec_index(parent_ptr).view().children.view() == pre.prc_mp.spec_index(parent_ptr).view().children.view().remove_value(target),
        post.prc_mp.spec_index(parent_ptr).view().children.map() == pre.prc_mp.spec_index(parent_ptr).view().children.map().remove(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()),
    ensures
        process_tree_wf(root_process, process_tree_dom.remove(target), post.prc_mp),
{
    let new_tree_dom = process_tree_dom.remove(target);
    assert(process_tree_dom.subset_of(pre.prc_mp.dom())) by { reveal(process_root_wf); };
    kill_retire_eof_target_no_descendant(pre, root_process, process_tree_dom, target);
    assert(process_tree_dom.contains(parent_ptr) && target != root_process && pre.prc_mp.spec_index(parent_ptr).view().children.view().contains(target)) by {
        reveal(process_root_wf); reveal(process_children_parent_wf);
    };
    kill_retire_eof_process_tree_parent_links_wf(pre, post, root_process, process_tree_dom, parent_ptr, target);
    assert(process_subtree_set_wf(root_process, new_tree_dom, post.prc_mp)) by { reveal(process_subtree_set_wf); };
    assert(process_uppertree_seq_wf(root_process, new_tree_dom, post.prc_mp)) by { reveal(process_uppertree_seq_wf); };
    assert(process_subtree_set_exclusive(root_process, new_tree_dom, post.prc_mp)) by { reveal(process_subtree_set_exclusive); };
}

/// Every process below the retired `target` in its tree records `target` at `target`'s depth in its upper tree, followed by
/// the next process on its path.
proof fn kill_retire_eof_target_descendant_uppers(pre: KernelK, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, target: RwLockProcessPtr)
    requires
        process_tree_fields_wf(pre.prc_mp),
        process_tree_wf(root_process, process_tree_dom, pre.prc_mp),
        process_tree_dom.subset_of(pre.prc_mp.dom()),
        process_tree_dom.contains(target),
    ensures
        forall|p_ptr: RwLockProcessPtr|
            #![trigger pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(target)]
            process_tree_dom.contains(p_ptr) && p_ptr != target && pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(target) ==> {
                let uppers = pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view();
                let child_depth = pre.prc_mp.spec_index(target).view_rodata().view().depth;
                let succ_ptr = uppers.spec_index(child_depth + 1);
                &&& child_depth < uppers.len() && uppers.spec_index(child_depth as int) == target
                &&& child_depth + 1 < uppers.len() ==> uppers.contains(succ_ptr)
            },
{
    reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf);
}

/// The process after `target` on the upper-tree path of a process below `target` is in the tree at its path depth, with
/// that path prefix as its upper tree.
proof fn kill_retire_eof_target_descendant_successor(pre: KernelK, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, target: RwLockProcessPtr)
    requires
        process_tree_fields_wf(pre.prc_mp),
        process_tree_wf(root_process, process_tree_dom, pre.prc_mp),
        process_tree_dom.subset_of(pre.prc_mp.dom()),
        process_tree_dom.contains(target),
    ensures
        forall|p_ptr: RwLockProcessPtr|
            #![trigger pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(target)]
            process_tree_dom.contains(p_ptr) && p_ptr != target && pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(target) ==> {
                let uppers = pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view();
                let child_depth = pre.prc_mp.spec_index(target).view_rodata().view().depth;
                let succ_ptr = uppers.spec_index(child_depth + 1);
                &&& child_depth + 1 < uppers.len() ==> process_tree_dom.contains(succ_ptr) && pre.prc_mp.spec_index(succ_ptr).view_rodata().view().depth == uppers.index_of(succ_ptr)
                &&& child_depth + 1 < uppers.len() ==> pre.prc_mp.spec_index(succ_ptr).view_ghost().uppertree_seq.view() =~= uppers.subrange(0, pre.prc_mp.spec_index(succ_ptr).view_rodata().view().depth as int)
            },
{
    kill_retire_eof_target_descendant_uppers(pre, root_process, process_tree_dom, target);
    reveal(process_uppertree_seq_wf);
}

/// A process below `target` and the process after `target` on its upper-tree path are not the root, and that process sits
/// one level below `target` with `target` at `target`'s depth in its upper tree.
proof fn kill_retire_eof_target_descendant_root(pre: KernelK, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, target: RwLockProcessPtr)
    requires
        process_tree_fields_wf(pre.prc_mp),
        process_tree_wf(root_process, process_tree_dom, pre.prc_mp),
        process_tree_dom.subset_of(pre.prc_mp.dom()),
        process_tree_dom.contains(target),
    ensures
        forall|p_ptr: RwLockProcessPtr|
            #![trigger pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(target)]
            process_tree_dom.contains(p_ptr) && p_ptr != target && pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(target) ==> {
                let uppers = pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view();
                let child_depth = pre.prc_mp.spec_index(target).view_rodata().view().depth;
                let succ_ptr = uppers.spec_index(child_depth + 1);
                &&& p_ptr != root_process
                &&& child_depth + 1 < uppers.len() ==> pre.prc_mp.spec_index(succ_ptr).view_rodata().view().depth as int == child_depth + 1 && succ_ptr != root_process
                &&& child_depth + 1 < uppers.len() ==> pre.prc_mp.spec_index(succ_ptr).view_ghost().uppertree_seq.view().spec_index(child_depth as int) == target
            },
{
    kill_retire_eof_target_descendant_uppers(pre, root_process, process_tree_dom, target);
    kill_retire_eof_target_descendant_successor(pre, root_process, process_tree_dom, target);
    reveal(process_root_wf);
}

/// A process below `target` reaches it through one of `target`'s children: the process after `target` on its upper-tree
/// path, or the process itself when `target` ends that path.
proof fn kill_retire_eof_target_descendant_child(pre: KernelK, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, target: RwLockProcessPtr)
    requires
        process_tree_fields_wf(pre.prc_mp),
        process_tree_wf(root_process, process_tree_dom, pre.prc_mp),
        process_tree_dom.subset_of(pre.prc_mp.dom()),
        process_tree_dom.contains(target),
    ensures
        forall|p_ptr: RwLockProcessPtr|
            #![trigger pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(target)]
            process_tree_dom.contains(p_ptr) && p_ptr != target && pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(target) ==> {
                let uppers = pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view();
                let child_depth = pre.prc_mp.spec_index(target).view_rodata().view().depth;
                let succ_ptr = uppers.spec_index(child_depth + 1);
                &&& child_depth + 1 < uppers.len() ==> pre.prc_mp.spec_index(target).view().children.view().contains(succ_ptr)
                &&& child_depth + 1 == uppers.len() ==> pre.prc_mp.spec_index(target).view().children.view().contains(p_ptr)
            },
{
    kill_retire_eof_target_descendant_uppers(pre, root_process, process_tree_dom, target);
    kill_retire_eof_target_descendant_successor(pre, root_process, process_tree_dom, target);
    kill_retire_eof_target_descendant_root(pre, root_process, process_tree_dom, target);
    reveal(process_linkedlist_wf); reveal(process_children_depth_wf);
}

/// No other process of the tree has the childless `target` in its upper tree.
proof fn kill_retire_eof_target_no_descendant(pre: KernelK, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, target: RwLockProcessPtr)
    requires
        process_tree_fields_wf(pre.prc_mp),
        process_tree_wf(root_process, process_tree_dom, pre.prc_mp),
        process_tree_dom.subset_of(pre.prc_mp.dom()),
        process_tree_dom.contains(target),
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
    ensures
        forall|p_ptr: RwLockProcessPtr, u_ptr: RwLockProcessPtr|
            #![trigger pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(u_ptr)]
            process_tree_dom.contains(p_ptr) && p_ptr != target && pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(u_ptr) ==> u_ptr != target,
{
    kill_retire_eof_target_descendant_uppers(pre, root_process, process_tree_dom, target);
    kill_retire_eof_target_descendant_successor(pre, root_process, process_tree_dom, target);
    kill_retire_eof_target_descendant_root(pre, root_process, process_tree_dom, target);
    kill_retire_eof_target_descendant_child(pre, root_process, process_tree_dom, target);
}

/// Parent-link part of `kill_retire_eof_process_tree_wf`: the remaining tree keeps its root, parent/child links,
/// child-list nodes, and parent depths.
pub(crate) proof fn kill_retire_eof_process_tree_parent_links_wf(
    pre: KernelK, post: KernelK, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, parent_ptr: RwLockProcessPtr, target: RwLockProcessPtr,
)
    requires
        process_tree_fields_wf(pre.prc_mp),
        process_tree_wf(root_process, process_tree_dom, pre.prc_mp),
        process_tree_dom.contains(target),
        pre.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        post.prc_mp.dom() == pre.prc_mp.dom().remove(target),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger post.prc_mp.spec_index(p_ptr)]
            post.prc_mp.dom().contains(p_ptr) ==> {
                &&& post.prc_mp.spec_index(p_ptr).view_rodata() == pre.prc_mp.spec_index(p_ptr).view_rodata()
                &&& post.prc_mp.spec_index(p_ptr).view().parent_linkedlist_node == pre.prc_mp.spec_index(p_ptr).view().parent_linkedlist_node
                &&& post.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq == pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq
                &&& p_ptr != parent_ptr ==> post.prc_mp.spec_index(p_ptr).view().children == pre.prc_mp.spec_index(p_ptr).view().children
                &&& pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
                    ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view().remove(target)
                &&& !pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
                    ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set
            },
        post.prc_mp.spec_index(parent_ptr).view().children.view() == pre.prc_mp.spec_index(parent_ptr).view().children.view().remove_value(target),
        post.prc_mp.spec_index(parent_ptr).view().children.map() == pre.prc_mp.spec_index(parent_ptr).view().children.map().remove(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()),
    ensures
        process_root_wf(root_process, process_tree_dom.remove(target), post.prc_mp),
        process_children_parent_wf(root_process, process_tree_dom.remove(target), post.prc_mp),
        process_linkedlist_wf(root_process, process_tree_dom.remove(target), post.prc_mp),
        process_children_depth_wf(root_process, process_tree_dom.remove(target), post.prc_mp),
{
    let new_tree_dom = process_tree_dom.remove(target);
    assert(process_tree_dom.subset_of(pre.prc_mp.dom())) by { reveal(process_root_wf); };
    assert(process_tree_dom.contains(parent_ptr) && target != root_process && pre.prc_mp.spec_index(parent_ptr).view().children.view().contains(target)) by {
        reveal(process_root_wf); reveal(process_children_parent_wf);
    };
    assert(pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr())
        && pre.prc_mp.spec_index(parent_ptr).view().children.map().spec_index(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()) == target) by {
        reveal(process_linkedlist_wf);
    };
    assert(process_root_wf(root_process, new_tree_dom, post.prc_mp)) by { reveal(process_root_wf); };
    assert(process_children_parent_wf(root_process, new_tree_dom, post.prc_mp)) by { reveal(process_children_parent_wf); lemma_seq_remove_value_membership::<RwLockProcessPtr>(); };
    assert(process_linkedlist_wf(root_process, new_tree_dom, post.prc_mp)) by {
        reveal(process_root_wf); reveal(process_linkedlist_wf); lemma_seq_remove_value_membership::<RwLockProcessPtr>();
    };
    assert(process_children_depth_wf(root_process, new_tree_dom, post.prc_mp)) by { reveal(process_children_depth_wf); };
}

/// Container-level form of `kill_retire_eof_process_tree_wf`: `container_ptr`, the owner of the retired leaf
/// `target`, drops it from its ghost process set and every other container entry is unchanged.
pub(crate) proof fn kill_retire_eof_per_container_process_tree_wf(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, target: RwLockProcessPtr,
)
    requires
        per_container_process_tree_wf(pre.ctn_mp, pre.prc_mp),
        container_process_wf(pre.ctn_mp, pre.prc_mp),
        process_perms_wf(pre.prc_mp),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        pre.prc_mp.spec_index(target).view().children.view().len() == 0,
        post.prc_mp.dom() == pre.prc_mp.dom().remove(target),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger post.prc_mp.spec_index(p_ptr)]
            post.prc_mp.dom().contains(p_ptr) ==> {
                &&& post.prc_mp.spec_index(p_ptr).view_rodata() == pre.prc_mp.spec_index(p_ptr).view_rodata()
                &&& post.prc_mp.spec_index(p_ptr).view().parent_linkedlist_node == pre.prc_mp.spec_index(p_ptr).view().parent_linkedlist_node
                &&& post.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq == pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq
                &&& p_ptr != parent_ptr ==> post.prc_mp.spec_index(p_ptr).view().children == pre.prc_mp.spec_index(p_ptr).view().children
                &&& pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
                    ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view().remove(target)
                &&& !pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
                    ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set
            },
        post.prc_mp.spec_index(parent_ptr).view().children.view() == pre.prc_mp.spec_index(parent_ptr).view().children.view().remove_value(target),
        post.prc_mp.spec_index(parent_ptr).view().children.map() == pre.prc_mp.spec_index(parent_ptr).view().children.map().remove(pre.prc_mp.spec_index(target).view().parent_linkedlist_node.addr()),
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target),
    ensures
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
{
    let root_process = pre.ctn_mp.spec_index(container_ptr).view().root_process;
    let process_tree_dom = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    assert(pre.ctn_mp.dom().contains(container_ptr) && process_tree_dom.contains(target)) by { reveal(container_process_wf); };
    assert(process_tree_wf(root_process, process_tree_dom, pre.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(process_tree_fields_wf(pre.prc_mp)) by { reveal(process_perms_wf); };
    kill_retire_eof_process_tree_wf(pre, post, root_process, process_tree_dom, parent_ptr, target);
    assert(process_tree_dom.contains(parent_ptr)) by { reveal(process_children_parent_wf); };
    kill_retire_eof_target_uppers_in_tree(pre, root_process, process_tree_dom, target);
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        reveal(per_container_process_tree_wf); reveal(container_process_wf); process_no_change_to_tree_fields_imply_wf_forall();
    };
}

/// Every process on the upper-tree path of `target` is in its tree.
proof fn kill_retire_eof_target_uppers_in_tree(pre: KernelK, root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, target: RwLockProcessPtr)
    requires
        process_tree_wf(root_process, process_tree_dom, pre.prc_mp),
        process_tree_dom.contains(target),
    ensures
        forall|p_ptr: RwLockProcessPtr| #![trigger pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)]
            pre.prc_mp.spec_index(target).view_ghost().uppertree_seq.view().to_set().contains(p_ptr) ==> process_tree_dom.contains(p_ptr),
{
    reveal(process_uppertree_seq_wf);
}

/// Dropping the retired leaf `target` from both the process map and its owning container `container_ptr` keeps the
/// container-process ownership invariant; the container keeps the leaf's parent, so its process set stays non-empty.
pub(crate) proof fn kill_retire_eof_container_process_wf(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, target: RwLockProcessPtr,
)
    requires
        per_container_process_tree_wf(pre.ctn_mp, pre.prc_mp),
        container_process_wf(pre.ctn_mp, pre.prc_mp),
        pre.prc_mp.dom().contains(target),
        pre.prc_mp.spec_index(target).view_rodata().view().owning_container == container_ptr,
        pre.prc_mp.spec_index(target).view_rodata().view().parent == Some(parent_ptr),
        post.prc_mp.dom() == pre.prc_mp.dom().remove(target),
        forall|p_ptr: RwLockProcessPtr|
            #![trigger post.prc_mp.spec_index(p_ptr)]
            post.prc_mp.dom().contains(p_ptr) ==> {
                &&& post.prc_mp.spec_index(p_ptr).view_rodata() == pre.prc_mp.spec_index(p_ptr).view_rodata()
                &&& post.prc_mp.spec_index(p_ptr).view().zombie == pre.prc_mp.spec_index(p_ptr).view().zombie
            },
        post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr),
        post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view(),
        post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata(),
        post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target),
    ensures
        container_process_wf(post.ctn_mp, post.prc_mp),
{
    let root_process = pre.ctn_mp.spec_index(container_ptr).view().root_process;
    let process_tree_dom = pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
    assert(pre.ctn_mp.dom().contains(container_ptr) && process_tree_dom.contains(target)) by { reveal(container_process_wf); };
    assert(process_tree_wf(root_process, process_tree_dom, pre.prc_mp)) by { reveal(per_container_process_tree_wf); };
    assert(process_tree_dom.contains(parent_ptr) && root_process != target && post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().contains(parent_ptr)) by {
        reveal(process_root_wf); reveal(process_children_parent_wf);
    };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
}
} // verus!
