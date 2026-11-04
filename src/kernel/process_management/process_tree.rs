use vstd::prelude::*;
use crate::*;

verus! {
// Process tree ghost fields: `children` is the direct child list; `uppertree_seq` lists the ancestors from the root,
// indexed by depth; `subtree_set` holds all descendants; `parent_linkedlist_node` is the node in the parent's child list.

/// The process map's permissions are well formed, every process satisfies its own invariant, and its tree fields are well formed.
#[verifier::opaque]
pub open spec fn process_perms_wf(prc_mp: ProcessLockedMap) -> bool {
    &&& prc_mp.perms_wf()
    &&& process_tree_fields_wf(prc_mp)
    &&& forall|p: RwLockProcessPtr|
        #![auto]
        prc_mp.dom().contains(p) ==> prc_mp.spec_index(p).inv()
}

pub proof fn process_perms_wf_map(prc_mp: ProcessLockedMap)
    requires process_perms_wf(prc_mp)
    ensures prc_mp.perms_wf()
{ reveal(process_perms_wf); }

pub proof fn process_perms_wf_at(prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_perms_wf(prc_mp),
        prc_mp.dom().contains(prc_ptr),
    ensures
        prc_mp.view().spec_index(prc_ptr).is_init(),
        prc_mp.view().spec_index(prc_ptr).addr() == prc_ptr,
        prc_mp.spec_index(prc_ptr).inv(),
        prc_mp.spec_index(prc_ptr).is_init(),
        prc_mp.spec_index(prc_ptr).view().inv(),
        prc_mp.spec_index(prc_ptr).view().owned_threads.view().no_duplicates(),
        prc_mp.spec_index(prc_ptr).view().children.view().no_duplicates(),
        prc_mp.spec_index(prc_ptr).view_ghost().uppertree_seq.view().no_duplicates(),
        !prc_mp.spec_index(prc_ptr).view().children.view().contains(prc_ptr),
        prc_mp.spec_index(prc_ptr).view_ghost().uppertree_seq.view().len() == prc_mp.spec_index(prc_ptr).view_rodata().view().depth,
{ reveal(process_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); }

/// Each process's child list and upper-tree sequence are duplicate-free, it is not its own child, and its depth is the
/// length of its upper-tree sequence.
pub open spec fn process_tree_fields_wf(prc_mp: ProcessLockedMap) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger prc_mp.dom().contains(p)]
        prc_mp.dom().contains(p) ==> {
            &&& prc_mp.spec_index(p).view().children.view().no_duplicates()
            &&& prc_mp.spec_index(p).view_ghost().uppertree_seq.view().no_duplicates()
            &&& !prc_mp.spec_index(p).view().children.view().contains(p)
            &&& prc_mp.spec_index(p).view_ghost().uppertree_seq.view().len() == prc_mp.spec_index(p).view_rodata().view().depth
        }
}

/// The root process is a depth-0 member that keeps its own list node; every other member has a parent and a nonzero depth.
#[verifier::opaque]
pub open spec fn process_root_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> bool {
    &&& process_tree_dom.contains(root_process)
    &&& process_tree_dom.subset_of(prc_mp.dom())
    &&& prc_mp.spec_index(root_process).view_rodata().view().depth == 0
    // the root's list node is not linked into any child list
    &&& prc_mp.spec_index(root_process).view().parent_linkedlist_node.is_init()
    &&& forall|p: RwLockProcessPtr|
        #![trigger process_tree_dom.contains(p)]
        process_tree_dom.contains(p) && p != root_process ==> {
            &&& prc_mp.spec_index(p).view_rodata().view().depth != 0
            // a non-root member's list node is linked into its parent's child list
            &&& !prc_mp.spec_index(p).view().parent_linkedlist_node.is_init()
        }
    &&& forall|p: RwLockProcessPtr|
        #![trigger process_tree_dom.contains(p)]
        process_tree_dom.contains(p) && p != root_process ==> prc_mp.spec_index(p).view_rodata().view().parent is Some
}

/// The tree root is a depth-0 member with an initialized parent node; member `prc_ptr` is a process, and a non-root one has a parent.
pub proof fn process_root_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_root_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures
        process_tree_dom.contains(root_process),
        prc_mp.dom().contains(prc_ptr),
        prc_mp.spec_index(root_process).view_rodata().view().depth == 0,
        prc_mp.spec_index(root_process).view().parent_linkedlist_node.is_init(),
        prc_ptr != root_process ==> {
            &&& prc_mp.spec_index(prc_ptr).view_rodata().view().depth != 0
            &&& !prc_mp.spec_index(prc_ptr).view().parent_linkedlist_node.is_init()
            &&& prc_mp.spec_index(prc_ptr).view_rodata().view().parent is Some
        },
{ reveal(process_root_wf); }

/// A member's children are members one level deeper that name it as parent; a member's parent is a member that lists it
/// as a child.
#[verifier::opaque]
pub open spec fn process_children_parent_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> bool {
    // Member -> children.
    &&& forall|p: RwLockProcessPtr, child: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p).view().children.view().contains(child)]
        process_tree_dom.contains(p) && prc_mp.spec_index(p).view().children.view().contains(child) ==> process_tree_dom.contains(child)
    &&& forall|p: RwLockProcessPtr, child: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p).view().children.view().contains(child)]
        process_tree_dom.contains(p) && prc_mp.spec_index(p).view().children.view().contains(child) ==> {
            &&& prc_mp.spec_index(child).view_rodata().view().parent.unwrap() == p
            &&& prc_mp.spec_index(child).view_rodata().view().depth == prc_mp.spec_index(p).view_rodata().view().depth + 1
        }
    // Member -> parent.
    &&& forall|p: RwLockProcessPtr|
        #![trigger process_tree_dom.contains(p)]
        process_tree_dom.contains(p) && prc_mp.spec_index(p).view_rodata().view().parent is Some ==> {
            &&& process_tree_dom.contains(prc_mp.spec_index(p).view_rodata().view().parent.unwrap())
            &&& prc_mp.spec_index(prc_mp.spec_index(p).view_rodata().view().parent.unwrap()).view().children.view().contains(p)
        }
}

/// Child `child_prc_ptr` of member `prc_ptr` is a member whose parent is `prc_ptr`, one level deeper.
pub proof fn process_children_parent_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr, child_prc_ptr: RwLockProcessPtr)
    requires
        process_children_parent_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures
        prc_mp.spec_index(prc_ptr).view().children.view().contains(child_prc_ptr) ==> {
            &&& process_tree_dom.contains(child_prc_ptr)
            &&& prc_mp.spec_index(child_prc_ptr).view_rodata().view().parent.unwrap() == prc_ptr
            &&& prc_mp.spec_index(child_prc_ptr).view_rodata().view().depth == prc_mp.spec_index(prc_ptr).view_rodata().view().depth + 1
        },
{ reveal(process_children_parent_wf); }

/// Member `prc_ptr`'s parent, if any, is a member that lists `prc_ptr` among its children.
pub proof fn process_children_parent_wf_parent_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_children_parent_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures
        prc_mp.spec_index(prc_ptr).view_rodata().view().parent is Some ==> {
            &&& process_tree_dom.contains(prc_mp.spec_index(prc_ptr).view_rodata().view().parent.unwrap())
            &&& prc_mp.spec_index(prc_mp.spec_index(prc_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(prc_ptr)
        },
{ reveal(process_children_parent_wf); }

/// Every child of member `prc_ptr` is a member.
pub proof fn process_children_parent_wf_implies_children_in_tree(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_children_parent_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures forall|child: RwLockProcessPtr| #[trigger] prc_mp.spec_index(prc_ptr).view().children.view().contains(child) ==> process_tree_dom.contains(child),
{ reveal(process_children_parent_wf); }

/// Every non-root member has a member parent, and sits in its parent's child list at its own list node.
#[verifier::opaque]
pub open spec fn process_linkedlist_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> bool {
    &&& forall|p: RwLockProcessPtr|
        #![trigger process_tree_dom.contains(prc_mp.spec_index(p).view_rodata().view().parent.unwrap())]
        process_tree_dom.contains(p) && p != root_process
            ==> prc_mp.spec_index(p).view_rodata().view().parent is Some && process_tree_dom.contains(prc_mp.spec_index(p).view_rodata().view().parent.unwrap())
    &&& forall|p: RwLockProcessPtr|
        #![trigger process_tree_dom.contains(p)]
        process_tree_dom.contains(p) && p != root_process ==> {
            &&& prc_mp.spec_index(prc_mp.spec_index(p).view_rodata().view().parent.unwrap()).view().children.view().contains(p)
            &&& prc_mp.spec_index(prc_mp.spec_index(p).view_rodata().view().parent.unwrap()).view().children.map().dom().contains(prc_mp.spec_index(p).view().parent_linkedlist_node.addr())
            &&& prc_mp.spec_index(prc_mp.spec_index(p).view_rodata().view().parent.unwrap()).view().children.map().spec_index(prc_mp.spec_index(p).view().parent_linkedlist_node.addr()) == p
        }
}

/// The parent of non-root member `prc_ptr` lists `prc_ptr` in its child list at `prc_ptr`'s parent node.
pub proof fn process_linkedlist_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_linkedlist_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures
        prc_ptr != root_process ==> {
            &&& prc_mp.spec_index(prc_mp.spec_index(prc_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(prc_ptr)
            &&& prc_mp.spec_index(prc_mp.spec_index(prc_ptr).view_rodata().view().parent.unwrap()).view().children.map().dom().contains(prc_mp.spec_index(prc_ptr).view().parent_linkedlist_node.addr())
            &&& prc_mp.spec_index(prc_mp.spec_index(prc_ptr).view_rodata().view().parent.unwrap()).view().children.map().spec_index(prc_mp.spec_index(prc_ptr).view().parent_linkedlist_node.addr()) == prc_ptr
        },
{ reveal(process_linkedlist_wf); }

/// The last entry of a non-root member's upper-tree sequence is its parent.
#[verifier::opaque]
pub open spec fn process_uppertree_seq_parent_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> bool {
    forall|p: RwLockProcessPtr|
        #![trigger process_tree_dom.contains(p)]
        process_tree_dom.contains(p) && p != root_process
            ==> prc_mp.spec_index(p).view_ghost().uppertree_seq.view().spec_index(prc_mp.spec_index(p).view_rodata().view().depth - 1) == prc_mp.spec_index(p).view_rodata().view().parent.unwrap()
}

/// The upper-tree sequence of non-root member `prc_ptr` ends with its parent.
pub proof fn process_uppertree_seq_parent_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_uppertree_seq_parent_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures
        prc_ptr != root_process ==> prc_mp.spec_index(prc_ptr).view_ghost().uppertree_seq.view().spec_index(prc_mp.spec_index(prc_ptr).view_rodata().view().depth - 1) == prc_mp.spec_index(prc_ptr).view_rodata().view().parent.unwrap(),
{ reveal(process_uppertree_seq_parent_wf); }

/// A subtree member `sub` of member `p` is a member whose upper-tree sequence holds `p` at `p`'s depth.
#[verifier::opaque]
pub open spec fn process_subtree_set_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> bool {
    forall|p: RwLockProcessPtr, sub: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p).view_ghost().subtree_set.view().contains(sub)]
        process_tree_dom.contains(p) && prc_mp.spec_index(p).view_ghost().subtree_set.view().contains(sub) ==> {
            &&& process_tree_dom.contains(sub)
            &&& prc_mp.spec_index(sub).view_ghost().uppertree_seq.view().len() > prc_mp.spec_index(p).view_rodata().view().depth
            &&& prc_mp.spec_index(sub).view_ghost().uppertree_seq.view().spec_index(prc_mp.spec_index(p).view_rodata().view().depth as int) == p
        }
}

/// Subtree member `sub_prc_ptr` of member `prc_ptr` is a member whose upper-tree sequence holds `prc_ptr` at `prc_ptr`'s depth.
pub proof fn process_subtree_set_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr, sub_prc_ptr: RwLockProcessPtr)
    requires
        process_subtree_set_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures
        prc_mp.spec_index(prc_ptr).view_ghost().subtree_set.view().contains(sub_prc_ptr) ==> {
            &&& process_tree_dom.contains(sub_prc_ptr)
            &&& prc_mp.spec_index(sub_prc_ptr).view_ghost().uppertree_seq.view().len() > prc_mp.spec_index(prc_ptr).view_rodata().view().depth
            &&& prc_mp.spec_index(sub_prc_ptr).view_ghost().uppertree_seq.view().spec_index(prc_mp.spec_index(prc_ptr).view_rodata().view().depth as int) == prc_ptr
        },
{ reveal(process_subtree_set_wf); }

/// An ancestor `u` of member `p` is a member at its own depth in `p`'s upper-tree sequence, whose subtree holds `p`.
#[verifier::opaque]
pub open spec fn process_uppertree_seq_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> bool {
    forall|p: RwLockProcessPtr, u: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p).view_ghost().uppertree_seq.view().contains(u)]
        process_tree_dom.contains(p) && prc_mp.spec_index(p).view_ghost().uppertree_seq.view().contains(u) ==> {
            &&& process_tree_dom.contains(u)
            &&& prc_mp.spec_index(p).view_ghost().uppertree_seq.view().spec_index(prc_mp.spec_index(u).view_rodata().view().depth as int) == u
            &&& prc_mp.spec_index(u).view_rodata().view().depth == prc_mp.spec_index(p).view_ghost().uppertree_seq.view().index_of(u)
            &&& prc_mp.spec_index(u).view_ghost().subtree_set.view().contains(p)
            &&& prc_mp.spec_index(u).view_ghost().uppertree_seq.view() =~= prc_mp.spec_index(p).view_ghost().uppertree_seq.view().subrange(0, prc_mp.spec_index(u).view_rodata().view().depth as int)
        }
}

/// Ancestor `upper_prc_ptr` of member `prc_ptr` is a member at its own depth in `prc_ptr`'s upper-tree sequence, whose subtree holds `prc_ptr`.
pub proof fn process_uppertree_seq_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr, upper_prc_ptr: RwLockProcessPtr)
    requires
        process_uppertree_seq_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures
        prc_mp.spec_index(prc_ptr).view_ghost().uppertree_seq.view().contains(upper_prc_ptr) ==> {
            &&& process_tree_dom.contains(upper_prc_ptr)
            &&& prc_mp.spec_index(prc_ptr).view_ghost().uppertree_seq.view().spec_index(prc_mp.spec_index(upper_prc_ptr).view_rodata().view().depth as int) == upper_prc_ptr
            &&& prc_mp.spec_index(upper_prc_ptr).view_rodata().view().depth == prc_mp.spec_index(prc_ptr).view_ghost().uppertree_seq.view().index_of(upper_prc_ptr)
            &&& prc_mp.spec_index(upper_prc_ptr).view_ghost().subtree_set.view().contains(prc_ptr)
            &&& prc_mp.spec_index(upper_prc_ptr).view_ghost().uppertree_seq.view() =~= prc_mp.spec_index(prc_ptr).view_ghost().uppertree_seq.view().subrange(0, prc_mp.spec_index(upper_prc_ptr).view_rodata().view().depth as int)
        },
{ reveal(process_uppertree_seq_wf); }

/// Every ancestor of member `prc_ptr` is a member.
pub proof fn process_uppertree_seq_wf_implies_ancestors_in_dom(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap, prc_ptr: RwLockProcessPtr)
    requires
        process_uppertree_seq_wf(root_process, process_tree_dom, prc_mp),
        process_tree_dom.contains(prc_ptr),
    ensures forall|u: RwLockProcessPtr| #[trigger] prc_mp.spec_index(prc_ptr).view_ghost().uppertree_seq.view().contains(u) ==> process_tree_dom.contains(u),
{ reveal(process_uppertree_seq_wf); }

/// Member `sub` is in the subtree of member `p` iff `p` is in `sub`'s upper-tree sequence.
#[verifier::opaque]
pub open spec fn process_subtree_uppertree_agree_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> bool {
    forall|p: RwLockProcessPtr, sub: RwLockProcessPtr|
        #![trigger prc_mp.spec_index(p).view_ghost().subtree_set.view().contains(sub), prc_mp.spec_index(sub).view_ghost().uppertree_seq.view().contains(p)]
        process_tree_dom.contains(p) && process_tree_dom.contains(sub)
            ==> prc_mp.spec_index(p).view_ghost().subtree_set.view().contains(sub) == prc_mp.spec_index(sub).view_ghost().uppertree_seq.view().contains(p)
}

/// The process tree rooted at `root_process` with members `process_tree_dom` is well formed.
pub open spec fn process_tree_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, prc_mp: ProcessLockedMap) -> bool {
    &&& process_root_wf(root_process, process_tree_dom, prc_mp)
    &&& process_children_parent_wf(root_process, process_tree_dom, prc_mp)
    &&& process_linkedlist_wf(root_process, process_tree_dom, prc_mp)
    &&& process_uppertree_seq_parent_wf(root_process, process_tree_dom, prc_mp)
    &&& process_subtree_set_wf(root_process, process_tree_dom, prc_mp)
    &&& process_uppertree_seq_wf(root_process, process_tree_dom, prc_mp)
    &&& process_subtree_uppertree_agree_wf(root_process, process_tree_dom, prc_mp)
}


pub open spec fn process_add_child_ensures(
    root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap,
    new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr,
) -> bool {
    &&& process_perms_wf(old_prc_mp)
    &&& process_perms_wf(new_prc_mp)
    &&& process_tree_wf(root_process, process_tree_dom, old_prc_mp)
    &&& process_tree_dom.subset_of(old_prc_mp.dom())
    &&& process_tree_dom.contains(parent_ptr)
    &&& !process_tree_dom.contains(child_ptr)
    &&& old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX
    &&& new_prc_mp.dom() == old_prc_mp.dom().insert(child_ptr)
    &&& new_prc_mp.spec_index(child_ptr).view_rodata().view().parent == Some(parent_ptr)
    &&& new_prc_mp.spec_index(child_ptr).view_rodata().view().depth == old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth + 1
    &&& new_prc_mp.spec_index(child_ptr).view().children.view() == Seq::<RwLockProcessPtr>::empty()
    &&& !new_prc_mp.spec_index(child_ptr).view().parent_linkedlist_node.is_init()
    &&& new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view() == old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr)
    &&& new_prc_mp.spec_index(child_ptr).view_ghost().subtree_set.view() == Set::<RwLockProcessPtr>::empty()
    &&& forall|p: RwLockProcessPtr|
        #![trigger process_tree_dom.contains(p)]
        #![trigger new_prc_mp.spec_index(p).view_rodata()]
        process_tree_dom.contains(p) && p != parent_ptr ==> {
            &&& new_prc_mp.spec_index(p).view_rodata() == old_prc_mp.spec_index(p).view_rodata()
            &&& new_prc_mp.spec_index(p).view().children == old_prc_mp.spec_index(p).view().children
            &&& new_prc_mp.spec_index(p).view().parent_linkedlist_node == old_prc_mp.spec_index(p).view().parent_linkedlist_node
        }
    &&& forall|p: RwLockProcessPtr|
        #![trigger old_prc_mp.spec_index(p).view_ghost().uppertree_seq]
        #![trigger new_prc_mp.spec_index(p).view_ghost().uppertree_seq]
        process_tree_dom.contains(p) ==> new_prc_mp.spec_index(p).view_ghost().uppertree_seq == old_prc_mp.spec_index(p).view_ghost().uppertree_seq
    &&& forall|p: RwLockProcessPtr|
        #![trigger new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set().contains(p)]
        new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set().contains(p)
            ==> new_prc_mp.spec_index(p).view_ghost().subtree_set.view() == old_prc_mp.spec_index(p).view_ghost().subtree_set.view().insert(child_ptr)
    &&& forall|p: RwLockProcessPtr|
        #![trigger process_tree_dom.contains(p)]
        process_tree_dom.contains(p) && !new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set().contains(p)
            ==> new_prc_mp.spec_index(p).view_ghost().subtree_set == old_prc_mp.spec_index(p).view_ghost().subtree_set
    &&& new_prc_mp.spec_index(parent_ptr).view_rodata() == old_prc_mp.spec_index(parent_ptr).view_rodata()
    &&& new_prc_mp.spec_index(parent_ptr).view().parent_linkedlist_node == old_prc_mp.spec_index(parent_ptr).view().parent_linkedlist_node
    &&& new_prc_mp.spec_index(parent_ptr).view().children.view() == old_prc_mp.spec_index(parent_ptr).view().children.view().push(child_ptr)
    &&& !old_prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(new_prc_mp.spec_index(child_ptr).view().parent_linkedlist_node.addr())
    &&& new_prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(new_prc_mp.spec_index(child_ptr).view().parent_linkedlist_node.addr())
    &&& new_prc_mp.spec_index(parent_ptr).view().children.map().spec_index(new_prc_mp.spec_index(child_ptr).view().parent_linkedlist_node.addr()) == child_ptr
    &&& new_prc_mp.spec_index(parent_ptr).view().children.map() == old_prc_mp.spec_index(parent_ptr).view().children.map().insert(new_prc_mp.spec_index(child_ptr).view().parent_linkedlist_node.addr(), child_ptr)
}

pub proof fn process_add_child_preserves_tree_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_add_child_ensures(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr),
    ensures
        process_tree_wf(root_process, process_tree_dom.insert(child_ptr), new_prc_mp),
{
    hide(Seq::no_duplicates);
    let parent_uppers = old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
    let child_uppers = new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
    let parent_depth = old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth;
    assert(parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()) by { reveal(process_perms_wf); };
    assert(!parent_uppers.contains(parent_ptr)) by { reveal(process_uppertree_seq_wf); };
    assert(child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
        && child_uppers.subrange(0, parent_depth as int) =~= parent_uppers) by { seq_push_implies_contains::<RwLockProcessPtr>(); seq_push_absent_implies_no_duplicates_and_index_of::<RwLockProcessPtr>(); };
    child_uppers.to_set_ensures();
    assert(process_tree_fields_wf(old_prc_mp) && process_tree_fields_wf(new_prc_mp)) by { reveal(process_perms_wf); };
    process_add_child_eof_process_uppertree_seq_wf(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr);
    process_add_child_eof_process_root_wf(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr);
    process_add_child_eof_process_children_parent_wf(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr);
    process_add_child_eof_process_linkedlist_wf(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr);
    process_add_child_eof_process_children_depth_wf(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr);
    process_add_child_eof_process_subtree_set_wf(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr);
    process_add_child_eof_process_subtree_set_exclusive(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr);
}

/// Closure of `process_add_child_preserves_tree_wf` for `process_uppertree_seq_wf`.
proof fn process_add_child_eof_process_uppertree_seq_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_add_child_ensures(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr),
        ({
            let parent_uppers = old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            let child_uppers = new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
            let parent_depth = old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth;
            &&& parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()
            &&& !parent_uppers.contains(parent_ptr)
            &&& child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
            &&& child_uppers.subrange(0, parent_depth as int) =~= parent_uppers
        }),
        process_tree_fields_wf(old_prc_mp),
        process_tree_fields_wf(new_prc_mp),
    ensures
        process_uppertree_seq_wf(root_process, process_tree_dom.insert(child_ptr), new_prc_mp),
{
    hide(Seq::no_duplicates);
    new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
    seq_push_implies_contains::<RwLockProcessPtr>(); seq_push_absent_implies_no_duplicates_and_index_of::<RwLockProcessPtr>(); reveal(process_uppertree_seq_wf);
}

/// Closure of `process_add_child_preserves_tree_wf` for `process_root_wf`.
proof fn process_add_child_eof_process_root_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_add_child_ensures(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr),
        ({
            let parent_uppers = old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            let child_uppers = new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
            let parent_depth = old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth;
            &&& parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()
            &&& !parent_uppers.contains(parent_ptr)
            &&& child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
            &&& child_uppers.subrange(0, parent_depth as int) =~= parent_uppers
        }),
        process_tree_fields_wf(old_prc_mp),
        process_tree_fields_wf(new_prc_mp),
    ensures
        process_root_wf(root_process, process_tree_dom.insert(child_ptr), new_prc_mp),
{
    hide(Seq::no_duplicates);
    new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
    reveal(process_root_wf);
}

/// Closure of `process_add_child_preserves_tree_wf` for `process_children_parent_wf`.
proof fn process_add_child_eof_process_children_parent_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_add_child_ensures(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr),
        ({
            let parent_uppers = old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            let child_uppers = new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
            let parent_depth = old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth;
            &&& parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()
            &&& !parent_uppers.contains(parent_ptr)
            &&& child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
            &&& child_uppers.subrange(0, parent_depth as int) =~= parent_uppers
        }),
        process_tree_fields_wf(old_prc_mp),
        process_tree_fields_wf(new_prc_mp),
    ensures
        process_children_parent_wf(root_process, process_tree_dom.insert(child_ptr), new_prc_mp),
{
    hide(Seq::no_duplicates);
    new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
    reveal(process_root_wf); reveal(process_children_parent_wf); seq_push_implies_contains::<RwLockProcessPtr>();
}

/// Closure of `process_add_child_preserves_tree_wf` for `process_linkedlist_wf`.
proof fn process_add_child_eof_process_linkedlist_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_add_child_ensures(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr),
        ({
            let parent_uppers = old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            let child_uppers = new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
            let parent_depth = old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth;
            &&& parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()
            &&& !parent_uppers.contains(parent_ptr)
            &&& child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
            &&& child_uppers.subrange(0, parent_depth as int) =~= parent_uppers
        }),
        process_tree_fields_wf(old_prc_mp),
        process_tree_fields_wf(new_prc_mp),
    ensures
        process_linkedlist_wf(root_process, process_tree_dom.insert(child_ptr), new_prc_mp),
{
    hide(Seq::no_duplicates);
    new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
    reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); seq_push_implies_contains::<RwLockProcessPtr>();
}

/// Closure of `process_add_child_preserves_tree_wf` for `process_uppertree_seq_parent_wf`.
proof fn process_add_child_eof_process_children_depth_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_add_child_ensures(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr),
        ({
            let parent_uppers = old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            let child_uppers = new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
            let parent_depth = old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth;
            &&& parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()
            &&& !parent_uppers.contains(parent_ptr)
            &&& child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
            &&& child_uppers.subrange(0, parent_depth as int) =~= parent_uppers
        }),
        process_tree_fields_wf(old_prc_mp),
        process_tree_fields_wf(new_prc_mp),
    ensures
        process_uppertree_seq_parent_wf(root_process, process_tree_dom.insert(child_ptr), new_prc_mp),
{
    hide(Seq::no_duplicates);
    new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
    reveal(process_uppertree_seq_parent_wf); seq_push_implies_contains::<RwLockProcessPtr>(); seq_push_absent_implies_no_duplicates_and_index_of::<RwLockProcessPtr>();
}

/// Closure of `process_add_child_preserves_tree_wf` for `process_subtree_set_wf`.
proof fn process_add_child_eof_process_subtree_set_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_add_child_ensures(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr),
        ({
            let parent_uppers = old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            let child_uppers = new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
            let parent_depth = old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth;
            &&& parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()
            &&& !parent_uppers.contains(parent_ptr)
            &&& child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
            &&& child_uppers.subrange(0, parent_depth as int) =~= parent_uppers
        }),
        process_tree_fields_wf(old_prc_mp),
        process_tree_fields_wf(new_prc_mp),
    ensures
        process_subtree_set_wf(root_process, process_tree_dom.insert(child_ptr), new_prc_mp),
{
    hide(Seq::no_duplicates);
    new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
    reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); seq_push_implies_contains::<RwLockProcessPtr>(); seq_push_absent_implies_no_duplicates_and_index_of::<RwLockProcessPtr>();
}

/// Closure of `process_add_child_preserves_tree_wf` for `process_subtree_uppertree_agree_wf`.
proof fn process_add_child_eof_process_subtree_set_exclusive(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
    requires
        process_add_child_ensures(root_process, process_tree_dom, old_prc_mp, new_prc_mp, parent_ptr, child_ptr),
        ({
            let parent_uppers = old_prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
            let child_uppers = new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view();
            let parent_depth = old_prc_mp.spec_index(parent_ptr).view_rodata().view().depth;
            &&& parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()
            &&& !parent_uppers.contains(parent_ptr)
            &&& child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
            &&& child_uppers.subrange(0, parent_depth as int) =~= parent_uppers
        }),
        process_tree_fields_wf(old_prc_mp),
        process_tree_fields_wf(new_prc_mp),
    ensures
        process_subtree_uppertree_agree_wf(root_process, process_tree_dom.insert(child_ptr), new_prc_mp),
{
    hide(Seq::no_duplicates);
    new_prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set_ensures();
    reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_uppertree_agree_wf); seq_push_implies_contains::<RwLockProcessPtr>(); seq_push_absent_implies_no_duplicates_and_index_of::<RwLockProcessPtr>();
}

pub proof fn process_insert_child_into_ancestor_subtree_sets(tracked prc_mp: &mut ProcessLockedMap, ancestors: Seq<RwLockProcessPtr>, child_ptr: RwLockProcessPtr, held_locks: Map<RwLockProcessPtr, TypedHeldLock>, thread_id: LockThreadId)
    requires
        old(prc_mp).perms_wf(),
        ancestors.to_set().subset_of(old(prc_mp).dom()),
        ancestors.no_duplicates(),
        !ancestors.to_set().contains(child_ptr),
        old(prc_mp).typed_lock_map_aligned(held_locks, thread_id),
    ensures
        final(prc_mp).perms_wf(),
        final(prc_mp).dom() == old(prc_mp).dom(),
        process_perms_wf(*old(prc_mp)) ==> process_perms_wf(*final(prc_mp)),
        final(prc_mp).typed_lock_map_aligned(held_locks, thread_id),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_ghost().subtree_set]
            ancestors.to_set().contains(p) ==> final(prc_mp).spec_index(p).view_ghost().subtree_set == Ghost(old(prc_mp).spec_index(p).view_ghost().subtree_set.view().insert(child_ptr)),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_ghost().subtree_set]
            old(prc_mp).dom().contains(p) && !ancestors.to_set().contains(p) ==> final(prc_mp).spec_index(p).view_ghost().subtree_set == old(prc_mp).spec_index(p).view_ghost().subtree_set,
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).view() == old(prc_mp).spec_index(p).view(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_rodata()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).view_rodata() == old(prc_mp).spec_index(p).view_rodata(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_ghost().uppertree_seq]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).view_ghost().uppertree_seq == old(prc_mp).spec_index(p).view_ghost().uppertree_seq,
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_ghost().owned_pci_functions]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).view_ghost().owned_pci_functions == old(prc_mp).spec_index(p).view_ghost().owned_pci_functions,
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).locking_thread()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).locking_thread() == old(prc_mp).spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).being_killed()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).being_killed() == old(prc_mp).spec_index(p).being_killed(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).killer_info()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).killer_info() == old(prc_mp).spec_index(p).killer_info(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).is_init()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).is_init() == old(prc_mp).spec_index(p).is_init(),
    decreases ancestors.len(),
{
    if ancestors.len() > 0 {
        let p0 = ancestors.spec_index(0);
        assert(ancestors.to_set().contains(p0)) by { ancestors.to_set_ensures(); };
        prc_mp.update_ghost(p0, ProcessGhost { uppertree_seq: prc_mp.spec_index(p0).view_ghost().uppertree_seq,
            subtree_set: Ghost(prc_mp.spec_index(p0).view_ghost().subtree_set.view().insert(child_ptr)), owned_pci_functions: prc_mp.spec_index(p0).view_ghost().owned_pci_functions });
        assert(prc_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(ancestors.drop_first().to_set().subset_of(prc_mp.dom())) by { ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures(); };
        process_insert_child_into_ancestor_subtree_sets(prc_mp, ancestors.drop_first(), child_ptr, held_locks, thread_id);
        assert({
            &&& !ancestors.drop_first().to_set().contains(p0)
            &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(p0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    }
    assert(process_perms_wf(*old(prc_mp)) ==> process_perms_wf(*prc_mp)) by { reveal(process_perms_wf); };
}

/// Removes `child_ptr` from the ghost subtree set of every process in `ancestors`; nothing else changes.
pub proof fn process_remove_child_from_ancestor_subtree_sets(tracked prc_mp: &mut ProcessLockedMap, ancestors: Seq<RwLockProcessPtr>, child_ptr: RwLockProcessPtr, held_locks: Map<RwLockProcessPtr, TypedHeldLock>, thread_id: LockThreadId)
    requires
        old(prc_mp).perms_wf(),
        ancestors.to_set().subset_of(old(prc_mp).dom()),
        ancestors.no_duplicates(),
        old(prc_mp).typed_lock_map_aligned(held_locks, thread_id),
    ensures
        final(prc_mp).perms_wf(),
        final(prc_mp).dom() == old(prc_mp).dom(),
        process_perms_wf(*old(prc_mp)) ==> process_perms_wf(*final(prc_mp)),
        final(prc_mp).typed_lock_map_aligned(held_locks, thread_id),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_ghost().subtree_set]
            ancestors.to_set().contains(p) ==> final(prc_mp).spec_index(p).view_ghost().subtree_set == Ghost(old(prc_mp).spec_index(p).view_ghost().subtree_set.view().remove(child_ptr)),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_ghost().subtree_set]
            old(prc_mp).dom().contains(p) && !ancestors.to_set().contains(p) ==> final(prc_mp).spec_index(p).view_ghost().subtree_set == old(prc_mp).spec_index(p).view_ghost().subtree_set,
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).view() == old(prc_mp).spec_index(p).view(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_rodata()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).view_rodata() == old(prc_mp).spec_index(p).view_rodata(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_ghost().uppertree_seq]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).view_ghost().uppertree_seq == old(prc_mp).spec_index(p).view_ghost().uppertree_seq,
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).view_ghost().owned_pci_functions]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).view_ghost().owned_pci_functions == old(prc_mp).spec_index(p).view_ghost().owned_pci_functions,
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).locking_thread()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).locking_thread() == old(prc_mp).spec_index(p).locking_thread(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).being_killed()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).being_killed() == old(prc_mp).spec_index(p).being_killed(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).killer_info()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).killer_info() == old(prc_mp).spec_index(p).killer_info(),
        forall|p: RwLockProcessPtr| #![trigger final(prc_mp).spec_index(p).is_init()]
            old(prc_mp).dom().contains(p) ==> final(prc_mp).spec_index(p).is_init() == old(prc_mp).spec_index(p).is_init(),
    decreases ancestors.len(),
{
    if ancestors.len() > 0 {
        let p0 = ancestors.spec_index(0);
        assert(ancestors.to_set().contains(p0)) by { ancestors.to_set_ensures(); };
        prc_mp.update_ghost(p0, ProcessGhost { uppertree_seq: prc_mp.spec_index(p0).view_ghost().uppertree_seq,
            subtree_set: Ghost(prc_mp.spec_index(p0).view_ghost().subtree_set.view().remove(child_ptr)), owned_pci_functions: prc_mp.spec_index(p0).view_ghost().owned_pci_functions });
        assert(prc_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(ancestors.drop_first().to_set().subset_of(prc_mp.dom())) by { ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures(); };
        process_remove_child_from_ancestor_subtree_sets(prc_mp, ancestors.drop_first(), child_ptr, held_locks, thread_id);
        assert({
            &&& !ancestors.drop_first().to_set().contains(p0)
            &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(p0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    }
    assert(process_perms_wf(*old(prc_mp)) ==> process_perms_wf(*prc_mp)) by { reveal(process_perms_wf); };
}

pub proof fn process_no_change_to_tree_fields_imply_wf_forall()
    ensures
        forall|root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap|
            #![trigger process_tree_wf(root_process, process_tree_dom, old_prc_mp), process_tree_wf(root_process, process_tree_dom, new_prc_mp)]
            (process_tree_wf(root_process, process_tree_dom, old_prc_mp) && process_tree_dom.subset_of(new_prc_mp.dom()) && forall|p: RwLockProcessPtr|
                #![trigger new_prc_mp.spec_index(p)]
                process_tree_dom.contains(p)
                    ==> new_prc_mp.spec_index(p).view().children == old_prc_mp.spec_index(p).view().children
                    && new_prc_mp.spec_index(p).view().parent_linkedlist_node == old_prc_mp.spec_index(p).view().parent_linkedlist_node
                    && new_prc_mp.spec_index(p).view_ghost().uppertree_seq == old_prc_mp.spec_index(p).view_ghost().uppertree_seq
                    && new_prc_mp.spec_index(p).view_ghost().subtree_set == old_prc_mp.spec_index(p).view_ghost().subtree_set
                    && new_prc_mp.spec_index(p).view_rodata() == old_prc_mp.spec_index(p).view_rodata())
            ==> process_tree_wf(root_process, process_tree_dom, new_prc_mp),
{
    reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); reveal(process_uppertree_seq_parent_wf);
    reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_uppertree_agree_wf);
}

pub proof fn per_container_process_tree_wf_preserved_for_tree_fields_eq(ctn_mp: ContainerLockedMap, old_prc_mp: ProcessLockedMap, new_prc_mp: ProcessLockedMap)
    requires
        per_container_process_tree_wf(ctn_mp, old_prc_mp),
        container_process_wf(ctn_mp, old_prc_mp),
        old_prc_mp.dom() == new_prc_mp.dom(),
        forall|p: RwLockProcessPtr| #![trigger new_prc_mp.spec_index(p)]
            old_prc_mp.dom().contains(p)
                ==> new_prc_mp.spec_index(p).view().children == old_prc_mp.spec_index(p).view().children
                && new_prc_mp.spec_index(p).view().parent_linkedlist_node == old_prc_mp.spec_index(p).view().parent_linkedlist_node
                && new_prc_mp.spec_index(p).view_ghost().uppertree_seq == old_prc_mp.spec_index(p).view_ghost().uppertree_seq
                && new_prc_mp.spec_index(p).view_ghost().subtree_set == old_prc_mp.spec_index(p).view_ghost().subtree_set
                && new_prc_mp.spec_index(p).view_rodata() == old_prc_mp.spec_index(p).view_rodata(),
    ensures
        per_container_process_tree_wf(ctn_mp, new_prc_mp),
{
    reveal(per_container_process_tree_wf); reveal(process_root_wf); reveal(process_children_parent_wf);
    reveal(process_linkedlist_wf); reveal(process_uppertree_seq_parent_wf); reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_uppertree_agree_wf);
}
}
