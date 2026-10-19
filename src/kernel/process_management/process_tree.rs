use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn process_perms_wf(process_perms: ProcessLockedMap) -> bool {
        &&& process_perms.perms_wf()
        &&& process_tree_fields_wf(process_perms)
        &&& forall|p_ptr: RwLockProcessPtr| #![auto] process_perms.dom().contains(p_ptr) ==> process_perms.spec_index(p_ptr).inv()
    }

    pub proof fn process_perms_wf_map(process_perms: ProcessLockedMap)
        requires process_perms_wf(process_perms)
        ensures process_perms.perms_wf()
    { reveal(process_perms_wf); }

    pub proof fn process_perms_wf_at(process_perms: ProcessLockedMap, process_ptr: RwLockProcessPtr)
        requires
            process_perms_wf(process_perms),
            process_perms.dom().contains(process_ptr),
        ensures
            process_perms.view().spec_index(process_ptr).is_init(),
            process_perms.view().spec_index(process_ptr).addr() == process_ptr,
            process_perms.spec_index(process_ptr).inv(),
            process_perms.spec_index(process_ptr).is_init(),
            process_perms.spec_index(process_ptr).view().inv(),
            process_perms.spec_index(process_ptr).view().owned_threads.view().no_duplicates(),
            process_perms.spec_index(process_ptr).view().children.view().no_duplicates(),
            process_perms.spec_index(process_ptr).view_ghost().uppertree_seq.view().no_duplicates(),
            !process_perms.spec_index(process_ptr).view().children.view().contains(process_ptr),
            process_perms.spec_index(process_ptr).view_ghost().uppertree_seq.view().len() == process_perms.spec_index(process_ptr).view_rodata().view().depth,
    { reveal(process_perms_wf); reveal(LinkedList::wf_value_list); reveal(LinkedList::value_list_unique); }

    pub open spec fn process_tree_fields_wf(process_perms: ProcessLockedMap) -> bool {
        forall|p_ptr: RwLockProcessPtr|
            #![trigger process_perms.dom().contains(p_ptr)]
            process_perms.dom().contains(p_ptr) ==> {
                &&& process_perms.spec_index(p_ptr).view().children.view().no_duplicates()
                &&& process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().no_duplicates()
                &&& process_perms.spec_index(p_ptr).view().children.view().contains(p_ptr) == false
                &&& process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().len() == process_perms.spec_index(p_ptr).view_rodata().view().depth
            }
    }

    #[verifier::opaque]
    pub open spec fn process_root_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap) -> bool {
        &&& process_tree_dom.contains(root_process)
        &&& process_tree_dom.subset_of(process_perms.dom())
        &&& process_perms.spec_index(root_process).view_rodata().view().depth == 0
        &&& process_perms.spec_index(root_process).view().parent_linkedlist_node.is_init()
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) && p_ptr != root_process ==> {
                &&& process_perms.spec_index(p_ptr).view_rodata().view().depth != 0
                &&& process_perms.spec_index(p_ptr).view().parent_linkedlist_node.is_init() == false
            }
        &&& forall|p_ptr: RwLockProcessPtr| #![trigger process_tree_dom.contains(p_ptr)] process_tree_dom.contains(p_ptr) && p_ptr != root_process ==> process_perms.spec_index(p_ptr).view_rodata().view().parent is Some
    }

    /// The tree root is a depth-0 member with an initialized parent node; member `p_ptr` is a process, and a non-root one has a parent.
    pub proof fn process_root_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr)
        requires
            process_root_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures
            process_tree_dom.contains(root_process),
            process_perms.dom().contains(p_ptr),
            process_perms.spec_index(root_process).view_rodata().view().depth == 0,
            process_perms.spec_index(root_process).view().parent_linkedlist_node.is_init(),
            p_ptr != root_process ==> {
                &&& process_perms.spec_index(p_ptr).view_rodata().view().depth != 0
                &&& process_perms.spec_index(p_ptr).view().parent_linkedlist_node.is_init() == false
                &&& process_perms.spec_index(p_ptr).view_rodata().view().parent is Some
            },
    { reveal(process_root_wf); }

    #[verifier::opaque]
    pub open spec fn process_children_parent_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap) -> bool {
        &&& forall|p_ptr: RwLockProcessPtr, child_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr)]
            process_tree_dom.contains(p_ptr) && process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr) ==> process_tree_dom.contains(child_p_ptr)
        &&& forall|p_ptr: RwLockProcessPtr, child_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr)]
            process_tree_dom.contains(p_ptr) && process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr) ==> {
                &&& process_perms.spec_index(child_p_ptr).view_rodata().view().parent.unwrap() == p_ptr
                &&& process_perms.spec_index(child_p_ptr).view_rodata().view().depth == process_perms.spec_index(p_ptr).view_rodata().view().depth + 1
            }
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) && process_perms.spec_index(p_ptr).view_rodata().view().parent is Some ==> {
                &&& process_tree_dom.contains(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap())
                &&& process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(p_ptr)
            }
    }

    /// Child `child_p_ptr` of member `p_ptr` is a member whose parent is `p_ptr`, one level deeper.
    pub proof fn process_children_parent_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr, child_p_ptr: RwLockProcessPtr)
        requires
            process_children_parent_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures
            process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr) ==> {
                &&& process_tree_dom.contains(child_p_ptr)
                &&& process_perms.spec_index(child_p_ptr).view_rodata().view().parent.unwrap() == p_ptr
                &&& process_perms.spec_index(child_p_ptr).view_rodata().view().depth == process_perms.spec_index(p_ptr).view_rodata().view().depth + 1
            },
    { reveal(process_children_parent_wf); }

    /// Member `p_ptr`'s parent, if any, is a member that lists `p_ptr` among its children.
    pub proof fn process_children_parent_wf_parent_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr)
        requires
            process_children_parent_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures
            process_perms.spec_index(p_ptr).view_rodata().view().parent is Some ==> {
                &&& process_tree_dom.contains(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap())
                &&& process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(p_ptr)
            },
    { reveal(process_children_parent_wf); }

    /// Every child of member `p_ptr` is a member.
    pub proof fn process_children_parent_wf_children_dom_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr)
        requires
            process_children_parent_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures forall|child_p_ptr: RwLockProcessPtr| #[trigger] process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr) ==> process_tree_dom.contains(child_p_ptr),
    { reveal(process_children_parent_wf); }

    #[verifier::opaque]
    pub open spec fn process_linkedlist_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap) -> bool {
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap())]
            process_tree_dom.contains(p_ptr) && p_ptr != root_process ==> process_perms.spec_index(p_ptr).view_rodata().view().parent is Some && process_tree_dom.contains(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap())
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) && p_ptr != root_process ==> {
                &&& process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(p_ptr)
                &&& process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.map().dom().contains(process_perms.spec_index(p_ptr).view().parent_linkedlist_node.addr())
                &&& process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.map().spec_index(process_perms.spec_index(p_ptr).view().parent_linkedlist_node.addr()) == p_ptr
            }
    }

    /// The parent of non-root member `p_ptr` lists `p_ptr` in its child list at `p_ptr`'s parent node.
    pub proof fn process_linkedlist_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr)
        requires
            process_linkedlist_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures
            p_ptr != root_process ==> {
                &&& process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(p_ptr)
                &&& process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.map().dom().contains(process_perms.spec_index(p_ptr).view().parent_linkedlist_node.addr())
                &&& process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.map().spec_index(process_perms.spec_index(p_ptr).view().parent_linkedlist_node.addr()) == p_ptr
            },
    { reveal(process_linkedlist_wf); }

    #[verifier::opaque]
    pub open spec fn process_children_depth_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap) -> bool {
        forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) && p_ptr != root_process
                ==> process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(p_ptr).view_rodata().view().depth - 1) == process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()
    }

    /// The upper-tree sequence of non-root member `p_ptr` ends with its parent.
    pub proof fn process_children_depth_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr)
        requires
            process_children_depth_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures
            p_ptr != root_process ==> process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(p_ptr).view_rodata().view().depth - 1) == process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap(),
    { reveal(process_children_depth_wf); }

    #[verifier::opaque]
    pub open spec fn process_subtree_set_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap) -> bool {
        forall|p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr)]
            process_tree_dom.contains(p_ptr) && process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr) ==> {
                &&& process_tree_dom.contains(sub_p_ptr)
                &&& process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().len() > process_perms.spec_index(p_ptr).view_rodata().view().depth
                &&& process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(p_ptr).view_rodata().view().depth as int) == p_ptr
            }
    }

    /// Subtree member `sub_p_ptr` of member `p_ptr` is a member whose upper-tree sequence holds `p_ptr` at `p_ptr`'s depth.
    pub proof fn process_subtree_set_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr)
        requires
            process_subtree_set_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures
            process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr) ==> {
                &&& process_tree_dom.contains(sub_p_ptr)
                &&& process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().len() > process_perms.spec_index(p_ptr).view_rodata().view().depth
                &&& process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(p_ptr).view_rodata().view().depth as int) == p_ptr
            },
    { reveal(process_subtree_set_wf); }

    #[verifier::opaque]
    pub open spec fn process_uppertree_seq_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap) -> bool {
        forall|p_ptr: RwLockProcessPtr, u_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(u_ptr)]
            process_tree_dom.contains(p_ptr) && process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(u_ptr) ==> {
                &&& process_tree_dom.contains(u_ptr)
                &&& process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(u_ptr).view_rodata().view().depth as int) == u_ptr
                &&& process_perms.spec_index(u_ptr).view_rodata().view().depth == process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().index_of(u_ptr)
                &&& process_perms.spec_index(u_ptr).view_ghost().subtree_set.view().contains(p_ptr)
                &&& process_perms.spec_index(u_ptr).view_ghost().uppertree_seq.view() =~= process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().subrange(0, process_perms.spec_index(u_ptr).view_rodata().view().depth as int)
            }
    }

    /// Ancestor `u_ptr` of member `p_ptr` is a member at its own depth in `p_ptr`'s upper-tree sequence, whose subtree holds `p_ptr`.
    pub proof fn process_uppertree_seq_wf_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr, u_ptr: RwLockProcessPtr)
        requires
            process_uppertree_seq_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures
            process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(u_ptr) ==> {
                &&& process_tree_dom.contains(u_ptr)
                &&& process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(u_ptr).view_rodata().view().depth as int) == u_ptr
                &&& process_perms.spec_index(u_ptr).view_rodata().view().depth == process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().index_of(u_ptr)
                &&& process_perms.spec_index(u_ptr).view_ghost().subtree_set.view().contains(p_ptr)
                &&& process_perms.spec_index(u_ptr).view_ghost().uppertree_seq.view() =~= process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().subrange(0, process_perms.spec_index(u_ptr).view_rodata().view().depth as int)
            },
    { reveal(process_uppertree_seq_wf); }

    /// Every ancestor of member `p_ptr` is a member.
    pub proof fn process_uppertree_seq_wf_dom_at(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap, p_ptr: RwLockProcessPtr)
        requires
            process_uppertree_seq_wf(root_process, process_tree_dom, process_perms),
            process_tree_dom.contains(p_ptr),
        ensures forall|u_ptr: RwLockProcessPtr| #[trigger] process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(u_ptr) ==> process_tree_dom.contains(u_ptr),
    { reveal(process_uppertree_seq_wf); }

    #[verifier::opaque]
    pub open spec fn process_subtree_set_exclusive(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap) -> bool {
        forall|p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr), process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().contains(p_ptr)]
            process_tree_dom.contains(p_ptr) && process_tree_dom.contains(sub_p_ptr)
                ==> process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr) == process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().contains(p_ptr)
    }

    pub open spec fn process_tree_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap) -> bool {
        &&& process_root_wf(root_process, process_tree_dom, process_perms)
        &&& process_children_parent_wf(root_process, process_tree_dom, process_perms)
        &&& process_linkedlist_wf(root_process, process_tree_dom, process_perms)
        &&& process_children_depth_wf(root_process, process_tree_dom, process_perms)
        &&& process_subtree_set_wf(root_process, process_tree_dom, process_perms)
        &&& process_uppertree_seq_wf(root_process, process_tree_dom, process_perms)
        &&& process_subtree_set_exclusive(root_process, process_tree_dom, process_perms)
    }

    pub open spec fn process_add_child_ensures(
        root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr,
    ) -> bool {
        &&& process_perms_wf(old_process_perms)
        &&& process_perms_wf(new_process_perms)
        &&& process_tree_wf(root_process, process_tree_dom, old_process_perms)
        &&& process_tree_dom.subset_of(old_process_perms.dom())
        &&& process_tree_dom.contains(parent_ptr)
        &&& !process_tree_dom.contains(child_ptr)
        &&& old_process_perms.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX
        &&& new_process_perms.dom() == old_process_perms.dom().insert(child_ptr)
        &&& new_process_perms.spec_index(child_ptr).view_rodata().view().parent == Some(parent_ptr)
        &&& new_process_perms.spec_index(child_ptr).view_rodata().view().depth == old_process_perms.spec_index(parent_ptr).view_rodata().view().depth + 1
        &&& new_process_perms.spec_index(child_ptr).view().children.view() == Seq::<RwLockProcessPtr>::empty()
        &&& !new_process_perms.spec_index(child_ptr).view().parent_linkedlist_node.is_init()
        &&& new_process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view() == old_process_perms.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr)
        &&& new_process_perms.spec_index(child_ptr).view_ghost().subtree_set.view() == Set::<RwLockProcessPtr>::empty()
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            #![trigger new_process_perms.spec_index(p_ptr).view_rodata()]
            process_tree_dom.contains(p_ptr) && p_ptr != parent_ptr ==> {
                &&& new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata()
                &&& new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                &&& new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
            }
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq]
            #![trigger new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq]
            process_tree_dom.contains(p_ptr) ==> new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq == old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger new_process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)]
            new_process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
                ==> new_process_perms.spec_index(p_ptr).view_ghost().subtree_set.view() == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().insert(child_ptr)
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) && !new_process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
                ==> new_process_perms.spec_index(p_ptr).view_ghost().subtree_set == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set
        &&& new_process_perms.spec_index(parent_ptr).view_rodata() == old_process_perms.spec_index(parent_ptr).view_rodata()
        &&& new_process_perms.spec_index(parent_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(parent_ptr).view().parent_linkedlist_node
        &&& new_process_perms.spec_index(parent_ptr).view().children.view() == old_process_perms.spec_index(parent_ptr).view().children.view().push(child_ptr)
        &&& !old_process_perms.spec_index(parent_ptr).view().children.map().dom().contains(new_process_perms.spec_index(child_ptr).view().parent_linkedlist_node.addr())
        &&& new_process_perms.spec_index(parent_ptr).view().children.map().dom().contains(new_process_perms.spec_index(child_ptr).view().parent_linkedlist_node.addr())
        &&& new_process_perms.spec_index(parent_ptr).view().children.map().spec_index(new_process_perms.spec_index(child_ptr).view().parent_linkedlist_node.addr()) == child_ptr
        &&& new_process_perms.spec_index(parent_ptr).view().children.map() == old_process_perms.spec_index(parent_ptr).view().children.map().insert(new_process_perms.spec_index(child_ptr).view().parent_linkedlist_node.addr(), child_ptr)
    }

    pub proof fn process_add_child_preserves_tree_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_process_perms: ProcessLockedMap, new_process_perms: ProcessLockedMap, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr)
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_tree_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        hide(Seq::no_duplicates);
        let parent_uppers = old_process_perms.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
        let child_uppers = new_process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view();
        let parent_depth = old_process_perms.spec_index(parent_ptr).view_rodata().view().depth;
        assert(parent_uppers.len() == parent_depth && child_uppers == parent_uppers.push(parent_ptr) && child_uppers.no_duplicates()) by { reveal(process_perms_wf); };
        assert(!parent_uppers.contains(parent_ptr)) by { reveal(process_uppertree_seq_wf); };
        assert(child_uppers.contains(parent_ptr) && child_uppers.spec_index(parent_depth as int) == parent_ptr && child_uppers.index_of(parent_ptr) == parent_depth
            && child_uppers.subrange(0, parent_depth as int) =~= parent_uppers) by { seq_push_lemma::<RwLockProcessPtr>(); seq_push_unique_lemma::<RwLockProcessPtr>(); };
        child_uppers.to_set_ensures();
        assert(process_tree_fields_wf(old_process_perms) && process_tree_fields_wf(new_process_perms)) by { reveal(process_perms_wf); };
        assert(process_uppertree_seq_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
            seq_push_lemma::<RwLockProcessPtr>(); seq_push_unique_lemma::<RwLockProcessPtr>(); reveal(process_uppertree_seq_wf);
        };
        assert(process_root_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by { reveal(process_root_wf); };
        assert(process_children_parent_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by { reveal(process_children_parent_wf); seq_push_lemma::<RwLockProcessPtr>(); };
        assert(process_linkedlist_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
            reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); seq_push_lemma::<RwLockProcessPtr>();
        };
        assert(process_children_depth_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
            reveal(process_children_depth_wf);
            seq_push_lemma::<RwLockProcessPtr>(); seq_push_unique_lemma::<RwLockProcessPtr>();
        };
        assert(process_subtree_set_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
            reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf);
            seq_push_lemma::<RwLockProcessPtr>(); seq_push_unique_lemma::<RwLockProcessPtr>();
        };
        assert(process_subtree_set_exclusive(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
            reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_set_exclusive);
            seq_push_lemma::<RwLockProcessPtr>(); seq_push_unique_lemma::<RwLockProcessPtr>();
        };
    }

    pub proof fn process_insert_child_into_ancestor_subtree_sets(tracked process_map: &mut ProcessLockedMap, ancestors: Seq<RwLockProcessPtr>, child_ptr: RwLockProcessPtr, held_locks: Map<RwLockProcessPtr, TypedHeldLock>, thread_id: LockThreadId)
        requires
            old(process_map).perms_wf(),
            ancestors.to_set().subset_of(old(process_map).dom()),
            ancestors.no_duplicates(),
            !ancestors.to_set().contains(child_ptr),
            old(process_map).typed_lock_map_aligned(held_locks, thread_id),
        ensures
            final(process_map).perms_wf(),
            final(process_map).dom() == old(process_map).dom(),
            process_perms_wf(*old(process_map)) ==> process_perms_wf(*final(process_map)),
            final(process_map).typed_lock_map_aligned(held_locks, thread_id),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_ghost().subtree_set]
                ancestors.to_set().contains(p) ==> final(process_map).spec_index(p).view_ghost().subtree_set == Ghost(old(process_map).spec_index(p).view_ghost().subtree_set.view().insert(child_ptr)),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_ghost().subtree_set]
                old(process_map).dom().contains(p) && !ancestors.to_set().contains(p) ==> final(process_map).spec_index(p).view_ghost().subtree_set == old(process_map).spec_index(p).view_ghost().subtree_set,
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).view() == old(process_map).spec_index(p).view(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_rodata()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).view_rodata() == old(process_map).spec_index(p).view_rodata(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_ghost().uppertree_seq]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).view_ghost().uppertree_seq == old(process_map).spec_index(p).view_ghost().uppertree_seq,
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_ghost().owned_pci_functions]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).view_ghost().owned_pci_functions == old(process_map).spec_index(p).view_ghost().owned_pci_functions,
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).locking_thread()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).locking_thread() == old(process_map).spec_index(p).locking_thread(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).being_killed()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).being_killed() == old(process_map).spec_index(p).being_killed(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).killer_info()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).killer_info() == old(process_map).spec_index(p).killer_info(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).is_init()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).is_init() == old(process_map).spec_index(p).is_init(),
        decreases ancestors.len(),
    {
        if ancestors.len() > 0 {
            let p0 = ancestors.spec_index(0);
            assert(ancestors.to_set().contains(p0)) by { ancestors.to_set_ensures(); };
            process_map.update_ghost(p0, ProcessGhost { uppertree_seq: process_map.spec_index(p0).view_ghost().uppertree_seq,
                subtree_set: Ghost(process_map.spec_index(p0).view_ghost().subtree_set.view().insert(child_ptr)), owned_pci_functions: process_map.spec_index(p0).view_ghost().owned_pci_functions });
            assert(process_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(ancestors.drop_first().to_set().subset_of(process_map.dom())) by { ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures(); };
            process_insert_child_into_ancestor_subtree_sets(process_map, ancestors.drop_first(), child_ptr, held_locks, thread_id);
            assert({
                &&& !ancestors.drop_first().to_set().contains(p0)
                &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(p0)
            }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        }
        assert(process_perms_wf(*old(process_map)) ==> process_perms_wf(*process_map)) by { reveal(process_perms_wf); };
    }

    /// Removes `child_ptr` from the ghost subtree set of every process in `ancestors`; nothing else changes.
    pub proof fn process_remove_child_from_ancestor_subtree_sets(tracked process_map: &mut ProcessLockedMap, ancestors: Seq<RwLockProcessPtr>, child_ptr: RwLockProcessPtr, held_locks: Map<RwLockProcessPtr, TypedHeldLock>, thread_id: LockThreadId)
        requires
            old(process_map).perms_wf(),
            ancestors.to_set().subset_of(old(process_map).dom()),
            ancestors.no_duplicates(),
            old(process_map).typed_lock_map_aligned(held_locks, thread_id),
        ensures
            final(process_map).perms_wf(),
            final(process_map).dom() == old(process_map).dom(),
            process_perms_wf(*old(process_map)) ==> process_perms_wf(*final(process_map)),
            final(process_map).typed_lock_map_aligned(held_locks, thread_id),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_ghost().subtree_set]
                ancestors.to_set().contains(p) ==> final(process_map).spec_index(p).view_ghost().subtree_set == Ghost(old(process_map).spec_index(p).view_ghost().subtree_set.view().remove(child_ptr)),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_ghost().subtree_set]
                old(process_map).dom().contains(p) && !ancestors.to_set().contains(p) ==> final(process_map).spec_index(p).view_ghost().subtree_set == old(process_map).spec_index(p).view_ghost().subtree_set,
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).view() == old(process_map).spec_index(p).view(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_rodata()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).view_rodata() == old(process_map).spec_index(p).view_rodata(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_ghost().uppertree_seq]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).view_ghost().uppertree_seq == old(process_map).spec_index(p).view_ghost().uppertree_seq,
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).view_ghost().owned_pci_functions]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).view_ghost().owned_pci_functions == old(process_map).spec_index(p).view_ghost().owned_pci_functions,
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).locking_thread()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).locking_thread() == old(process_map).spec_index(p).locking_thread(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).being_killed()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).being_killed() == old(process_map).spec_index(p).being_killed(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).killer_info()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).killer_info() == old(process_map).spec_index(p).killer_info(),
            forall|p: RwLockProcessPtr| #![trigger final(process_map).spec_index(p).is_init()]
                old(process_map).dom().contains(p) ==> final(process_map).spec_index(p).is_init() == old(process_map).spec_index(p).is_init(),
        decreases ancestors.len(),
    {
        if ancestors.len() > 0 {
            let p0 = ancestors.spec_index(0);
            assert(ancestors.to_set().contains(p0)) by { ancestors.to_set_ensures(); };
            process_map.update_ghost(p0, ProcessGhost { uppertree_seq: process_map.spec_index(p0).view_ghost().uppertree_seq,
                subtree_set: Ghost(process_map.spec_index(p0).view_ghost().subtree_set.view().remove(child_ptr)), owned_pci_functions: process_map.spec_index(p0).view_ghost().owned_pci_functions });
            assert(process_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(ancestors.drop_first().to_set().subset_of(process_map.dom())) by { ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures(); };
            process_remove_child_from_ancestor_subtree_sets(process_map, ancestors.drop_first(), child_ptr, held_locks, thread_id);
            assert({
                &&& !ancestors.drop_first().to_set().contains(p0)
                &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(p0)
            }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        }
        assert(process_perms_wf(*old(process_map)) ==> process_perms_wf(*process_map)) by { reveal(process_perms_wf); };
    }

    pub proof fn process_no_change_to_tree_fields_imply_wf_forall()
        ensures
            forall|root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, old_process_perms: ProcessLockedMap, new_process_perms: ProcessLockedMap|
                #![trigger process_tree_wf(root_process, process_tree_dom, old_process_perms), process_tree_wf(root_process, process_tree_dom, new_process_perms)]
                (process_tree_wf(root_process, process_tree_dom, old_process_perms) && process_tree_dom.subset_of(new_process_perms.dom()) && forall|p_ptr: RwLockProcessPtr|
                    #![trigger new_process_perms.spec_index(p_ptr)]
                    process_tree_dom.contains(p_ptr)
                        ==> new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                        && new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
                        && new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq == old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq
                        && new_process_perms.spec_index(p_ptr).view_ghost().subtree_set == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set
                        && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata())
                ==> process_tree_wf(root_process, process_tree_dom, new_process_perms),
    {
        reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); reveal(process_children_depth_wf);
        reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_set_exclusive);
    }

    pub proof fn per_container_process_tree_wf_preserved_for_tree_fields_eq(container_perms: ContainerLockedMap, old_process_perms: ProcessLockedMap, new_process_perms: ProcessLockedMap)
        requires
            per_container_process_tree_wf(container_perms, old_process_perms),
            container_process_wf(container_perms, old_process_perms),
            old_process_perms.dom() == new_process_perms.dom(),
            forall|p_ptr: RwLockProcessPtr| #![trigger new_process_perms.spec_index(p_ptr)]
                old_process_perms.dom().contains(p_ptr)
                    ==> new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                    && new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
                    && new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq == old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq
                    && new_process_perms.spec_index(p_ptr).view_ghost().subtree_set == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set
                    && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata(),
        ensures
            per_container_process_tree_wf(container_perms, new_process_perms),
    {
        reveal(per_container_process_tree_wf); reveal(process_root_wf); reveal(process_children_parent_wf);
        reveal(process_linkedlist_wf); reveal(process_children_depth_wf); reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_set_exclusive);
    }
}
