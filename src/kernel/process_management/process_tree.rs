use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn process_perms_wf(process_perms: ProcessLockedMap) -> bool{
        &&&
        process_perms.perms_wf()
        &&&
        process_tree_fields_wf(process_perms)
        &&&
        forall|p_ptr:RwLockProcessPtr|
            #![auto]
            process_perms.dom().contains(p_ptr)
            ==>
            process_perms.spec_index(p_ptr).inv()
    }

    pub open spec fn process_tree_fields_wf(
        process_perms: ProcessLockedMap,
    ) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().children]
            #![trigger process_perms.spec_index(p_ptr).view_ghost().uppertree_seq]
            #![trigger process_perms.spec_index(p_ptr).view_ghost().subtree_set]
            #![trigger process_perms.spec_index(p_ptr).view_rodata().view().depth]
            process_perms.dom().contains(p_ptr) 
            ==> 
            {
                &&&
                process_perms.spec_index(p_ptr).view().children.view().no_duplicates()
                &&&
                process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().no_duplicates()
                &&&
                process_perms.spec_index(p_ptr).view().children.view().contains(p_ptr) == false
                &&&
                process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().len()
                    ==
                    process_perms.spec_index(p_ptr).view_rodata().view().depth
            }
    }

    #[verifier::opaque]
    pub open spec fn process_root_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        process_tree_dom.contains(root_process)
        &&&
        process_tree_dom.subset_of(process_perms.dom())
        &&& 
        process_perms.spec_index(root_process).view_rodata().view().depth == 0        
        &&& 
        process_perms.spec_index(root_process).view().parent_linkedlist_node.is_init()
        &&& 
        forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && p_ptr != root_process
            ==> 
            {
                &&& process_perms.spec_index(p_ptr).view_rodata().view().depth != 0
                &&& process_perms.spec_index(p_ptr).view().parent_linkedlist_node.is_init() == false
            }
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && p_ptr != root_process
            ==>
            process_perms.spec_index(p_ptr).view_rodata().view().parent is Some
    }

    #[verifier::opaque]
    pub open spec fn process_children_parent_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&&
        forall|p_ptr: RwLockProcessPtr, child_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && 
            process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr)
            ==> 
            process_tree_dom.contains(child_p_ptr)
        &&& 
        forall|p_ptr: RwLockProcessPtr, child_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr)]
            process_tree_dom.contains(p_ptr) && process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr)
            ==> 
            {
                &&&
                process_perms.spec_index(child_p_ptr).view_rodata().view().parent.unwrap() == p_ptr
                &&&
                process_perms.spec_index(child_p_ptr).view_rodata().view().depth == process_perms.spec_index(p_ptr).view_rodata().view().depth + 1
            }
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && 
            process_perms.spec_index(p_ptr).view_rodata().view().parent is Some
            ==>
            {
                &&&
                process_tree_dom.contains(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap())
                &&&
                process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(p_ptr)
            }
    }

    #[verifier::opaque]
    pub open spec fn process_linkedlist_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap())]
            process_tree_dom.contains(p_ptr) 
            && 
            p_ptr != root_process
            ==> 
            process_perms.spec_index(p_ptr).view_rodata().view().parent is Some 
            && 
            process_tree_dom.contains(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap())
        &&& 
        forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) && p_ptr != root_process
            ==> 
            {
                &&&
                process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(p_ptr)
                &&& 
                process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.map().dom().contains(process_perms.spec_index(p_ptr).view().parent_linkedlist_node.addr())
                &&&
                process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.map().spec_index(process_perms.spec_index(p_ptr).view().parent_linkedlist_node.addr()) == p_ptr
            }
    }

    #[verifier::opaque]
    pub open spec fn process_children_depth_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && 
            p_ptr != root_process
            ==> 
            process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(p_ptr).view_rodata().view().depth - 1)
                == process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()
    }

    #[verifier::opaque]
    pub open spec fn process_subtree_set_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr)]
            process_tree_dom.contains(p_ptr)
            && 
            process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr)
            ==> 
            {
                &&&
                process_tree_dom.contains(sub_p_ptr)
                &&&
                process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().len() > process_perms.spec_index(p_ptr).view_rodata().view().depth
                &&&
                process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(p_ptr).view_rodata().view().depth as int) == p_ptr
            }
    }

    #[verifier::opaque]
    pub open spec fn process_uppertree_seq_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, u_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(u_ptr)]
            process_tree_dom.contains(p_ptr)
            && 
            process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().contains(u_ptr)
            ==> 
            {
                &&&
                process_tree_dom.contains(u_ptr)
                &&&
                process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().spec_index(process_perms.spec_index(u_ptr).view_rodata().view().depth as int) == u_ptr
                &&&
                process_perms.spec_index(u_ptr).view_rodata().view().depth == process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().index_of(u_ptr)
                &&&
                process_perms.spec_index(u_ptr).view_ghost().subtree_set.view().contains(p_ptr)
                &&&
                process_perms.spec_index(u_ptr).view_ghost().uppertree_seq.view() =~= process_perms.spec_index(p_ptr).view_ghost().uppertree_seq.view().subrange(0, process_perms.spec_index(u_ptr).view_rodata().view().depth as int)
            }
    }

    #[verifier::opaque]
    pub open spec fn process_subtree_set_exclusive(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr), process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().contains(p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && 
            process_tree_dom.contains(sub_p_ptr) 
            ==> 
            process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().contains(sub_p_ptr) == process_perms.spec_index(sub_p_ptr).view_ghost().uppertree_seq.view().contains(p_ptr)
    }

    pub open spec fn process_tree_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& process_root_wf(root_process, process_tree_dom, process_perms)
        &&& process_children_parent_wf(root_process, process_tree_dom, process_perms)
        &&& process_linkedlist_wf(root_process, process_tree_dom, process_perms)
        &&& process_children_depth_wf(root_process, process_tree_dom, process_perms)
        &&& process_subtree_set_wf(root_process, process_tree_dom, process_perms)
        &&& process_uppertree_seq_wf(root_process, process_tree_dom, process_perms)
        &&& process_subtree_set_exclusive(root_process, process_tree_dom, process_perms)
    }

    /// Preserve the process tree when its payload, ghost, and read-only tree fields are unchanged.
    pub proof fn process_no_change_to_tree_fields_imply_wf(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
    )
        requires
            process_tree_wf(root_process, process_tree_dom, old_process_perms),
            process_tree_dom.subset_of(new_process_perms.dom()),
            forall|p_ptr: RwLockProcessPtr|
                #![trigger new_process_perms.spec_index(p_ptr)]
                process_tree_dom.contains(p_ptr) ==>
                    new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                    && new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
                    && new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq == old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq
                    && new_process_perms.spec_index(p_ptr).view_ghost().subtree_set == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set
                    && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata(),
        ensures
            process_tree_wf(root_process, process_tree_dom, new_process_perms),
    {
        assert(process_tree_wf(root_process, process_tree_dom, new_process_perms)) by {
             reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); reveal(process_children_depth_wf);
            reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_set_exclusive);
        };
    }

    pub open spec fn process_add_child_ensures(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
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
            process_tree_dom.contains(p_ptr) && p_ptr != parent_ptr ==> {
                &&& new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata()
                &&& new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                &&& new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
            }
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq]
            #![trigger new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq]
            process_tree_dom.contains(p_ptr) ==>
                new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq == old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger new_process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(p_ptr)]
            new_process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(p_ptr) ==>
                new_process_perms.spec_index(p_ptr).view_ghost().subtree_set.view() == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set.view().insert(child_ptr)
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) && !new_process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(p_ptr) ==>
                new_process_perms.spec_index(p_ptr).view_ghost().subtree_set == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set
        &&& new_process_perms.spec_index(parent_ptr).view_rodata() == old_process_perms.spec_index(parent_ptr).view_rodata()
        &&& new_process_perms.spec_index(parent_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(parent_ptr).view().parent_linkedlist_node
        &&& new_process_perms.spec_index(parent_ptr).view().children.view() == old_process_perms.spec_index(parent_ptr).view().children.view().push(child_ptr)
        &&& new_process_perms.spec_index(parent_ptr).view().children.map().dom().contains(new_process_perms.spec_index(child_ptr).view().parent_linkedlist_node.addr())
        &&& new_process_perms.spec_index(parent_ptr).view().children.map().spec_index(new_process_perms.spec_index(child_ptr).view().parent_linkedlist_node.addr()) == child_ptr
        &&& forall|node_addr: usize|
            #![trigger old_process_perms.spec_index(parent_ptr).view().children.map().dom().contains(node_addr)]
            old_process_perms.spec_index(parent_ptr).view().children.map().dom().contains(node_addr) ==> {
                &&& new_process_perms.spec_index(parent_ptr).view().children.map().dom().contains(node_addr)
                &&& new_process_perms.spec_index(parent_ptr).view().children.map().spec_index(node_addr) == old_process_perms.spec_index(parent_ptr).view().children.map().spec_index(node_addr)
            }
    }

    proof fn process_add_child_preserves_root_wf(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
    )
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_root_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        assert(process_root_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
              reveal(process_root_wf);
        };
    }

    proof fn process_add_child_preserves_children_parent_wf(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
    )
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_children_parent_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        assert(process_children_parent_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
              reveal(process_children_parent_wf);
            seq_push_lemma::<RwLockProcessPtr>();
        };
    }

    proof fn process_add_child_preserves_linkedlist_wf(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
    )
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_linkedlist_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        assert(process_linkedlist_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
              reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf);
            seq_push_lemma::<RwLockProcessPtr>();
        };
    }

    proof fn process_add_child_preserves_children_depth_wf(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
    )
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_children_depth_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        assert(process_children_depth_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
              reveal(process_children_depth_wf);
            assert(process_tree_fields_wf(old_process_perms)) by { reveal(process_perms_wf); };
            assert(process_tree_fields_wf(new_process_perms)) by { reveal(process_perms_wf); };
            seq_push_lemma::<RwLockProcessPtr>();
            seq_push_unique_lemma::<RwLockProcessPtr>();
        };
    }

    proof fn process_add_child_preserves_subtree_set_wf(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
    )
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_subtree_set_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        assert(process_subtree_set_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
            process_add_child_preserves_uppertree_seq_wf(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr);
              reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf);
            assert(process_tree_fields_wf(old_process_perms)) by { reveal(process_perms_wf); };
            assert(process_tree_fields_wf(new_process_perms)) by { reveal(process_perms_wf); };
            seq_push_lemma::<RwLockProcessPtr>();
            seq_push_unique_lemma::<RwLockProcessPtr>();
        };
    }

    proof fn process_add_child_preserves_uppertree_seq_wf(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
    )
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_uppertree_seq_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        assert(process_uppertree_seq_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
            seq_push_lemma::<RwLockProcessPtr>();
            seq_push_unique_lemma::<RwLockProcessPtr>();
              reveal(process_uppertree_seq_wf);
            assert(process_tree_fields_wf(old_process_perms)) by { reveal(process_perms_wf); };
            assert(process_tree_fields_wf(new_process_perms)) by { reveal(process_perms_wf); };
        };
    }

    proof fn process_add_child_preserves_subtree_set_exclusive(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
    )
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_subtree_set_exclusive(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        assert(process_subtree_set_exclusive(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
              reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_set_exclusive);
            assert(process_tree_fields_wf(old_process_perms)) by { reveal(process_perms_wf); };
            assert(process_tree_fields_wf(new_process_perms)) by { reveal(process_perms_wf); };
            seq_push_lemma::<RwLockProcessPtr>();
            seq_push_unique_lemma::<RwLockProcessPtr>();
        };
    }

    pub proof fn process_add_child_preserves_tree_wf(
        root_process: RwLockProcessPtr,
        process_tree_dom: Set<RwLockProcessPtr>,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
        parent_ptr: RwLockProcessPtr,
        child_ptr: RwLockProcessPtr,
    )
        requires
            process_add_child_ensures(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr),
        ensures
            process_tree_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms),
    {
        assert(process_tree_wf(root_process, process_tree_dom.insert(child_ptr), new_process_perms)) by {
            process_add_child_preserves_root_wf(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr);
            process_add_child_preserves_children_parent_wf(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr);
            process_add_child_preserves_linkedlist_wf(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr);
            process_add_child_preserves_children_depth_wf(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr);
            process_add_child_preserves_subtree_set_wf(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr);
            process_add_child_preserves_uppertree_seq_wf(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr);
            process_add_child_preserves_subtree_set_exclusive(root_process, process_tree_dom, old_process_perms, new_process_perms, parent_ptr, child_ptr);
        };
    }

    pub proof fn process_insert_child_into_ancestor_subtree_sets(
        tracked process_map: &mut ProcessLockedMap,
        ancestors: Seq<RwLockProcessPtr>,
        child_ptr: RwLockProcessPtr,
    )
        requires
            old(process_map).perms_wf(),
            ancestors.to_set().subset_of(old(process_map).dom()),
            ancestors.no_duplicates(),
            !ancestors.to_set().contains(child_ptr),
        ensures
            final(process_map).perms_wf(),
            final(process_map).dom() == old(process_map).dom(),
            forall|p: RwLockProcessPtr| #![auto]
                ancestors.to_set().contains(p) ==>
                    final(process_map).spec_index(p).view_ghost().subtree_set.view() =~= old(process_map).spec_index(p).view_ghost().subtree_set.view().insert(child_ptr),
            forall|p: RwLockProcessPtr| #![auto]
                old(process_map).dom().contains(p) && !ancestors.to_set().contains(p) ==>
                    final(process_map).spec_index(p).view_ghost() == old(process_map).spec_index(p).view_ghost(),
            forall|p: RwLockProcessPtr| #![auto]
                old(process_map).dom().contains(p) ==>
                    final(process_map).spec_index(p).view() == old(process_map).spec_index(p).view()
                    && final(process_map).spec_index(p).view_rodata() == old(process_map).spec_index(p).view_rodata()
                    && final(process_map).spec_index(p).view_ghost().uppertree_seq == old(process_map).spec_index(p).view_ghost().uppertree_seq
                    && final(process_map).spec_index(p).is_init() == old(process_map).spec_index(p).is_init()
                    && final(process_map).spec_index(p).locking_thread() == old(process_map).spec_index(p).locking_thread()
                    && final(process_map).spec_index(p).being_killed() == old(process_map).spec_index(p).being_killed(),
        decreases ancestors.len(),
    {
        if ancestors.len() > 0 {
            let p0 = ancestors.spec_index(0);
            assert(ancestors.to_set().contains(p0)) by { ancestors.to_set_ensures(); };
            process_map.update_ghost(p0, ProcessGhost {
                uppertree_seq: process_map.spec_index(p0).view_ghost().uppertree_seq,
                subtree_set: Ghost(process_map.spec_index(p0).view_ghost().subtree_set.view().insert(child_ptr)),
            });
            assert(ancestors.drop_first().to_set().subset_of(process_map.dom())) by {
                ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures();
                broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
            };
            process_insert_child_into_ancestor_subtree_sets(process_map, ancestors.drop_first(), child_ptr);
            assert(!ancestors.drop_first().to_set().contains(p0)) by {
                ancestors.drop_first().to_set_ensures();
                if ancestors.drop_first().contains(p0) {
                    let k = choose|k: int| 0 <= k < ancestors.drop_first().len() && ancestors.drop_first().spec_index(k) == p0;
                }
            };
            assert_sets_equal!(ancestors.to_set() == ancestors.drop_first().to_set().insert(p0), p => {
                ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures();
                if ancestors.contains(p) && p != p0 {
                    let i = choose|i: int| 0 <= i < ancestors.len() && ancestors.spec_index(i) == p;
                    assert(i > 0 && ancestors.drop_first().spec_index(i - 1) == p) by { ancestors.to_set_ensures(); };
                }
                if ancestors.drop_first().contains(p) {
                    let i = choose|i: int| 0 <= i < ancestors.drop_first().len() && ancestors.drop_first().spec_index(i) == p;
                    assert(ancestors.spec_index(i + 1) == p) by { ancestors.drop_first().to_set_ensures(); };
                }
            });
        }
    }

    pub proof fn process_no_change_to_tree_fields_imply_wf_forall()
        ensures
            forall|
                root_process: RwLockProcessPtr,
                process_tree_dom: Set<RwLockProcessPtr>,
                old_process_perms: ProcessLockedMap,
                new_process_perms: ProcessLockedMap,
            |
                #![trigger process_tree_wf(root_process, process_tree_dom, old_process_perms), process_tree_wf(root_process, process_tree_dom, new_process_perms)]
                (process_tree_wf(root_process, process_tree_dom, old_process_perms)
                && process_tree_dom.subset_of(new_process_perms.dom())
                && forall|p_ptr: RwLockProcessPtr|
                    #![trigger new_process_perms.spec_index(p_ptr)]
                    process_tree_dom.contains(p_ptr) ==>
                        new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                        && new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
                        && new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq == old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq
                        && new_process_perms.spec_index(p_ptr).view_ghost().subtree_set == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set
                        && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata())
                ==>
                process_tree_wf(root_process, process_tree_dom, new_process_perms),
    {
         reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); reveal(process_children_depth_wf);
        reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_set_exclusive);
    }

    pub proof fn per_container_process_tree_wf_preserved_for_tree_fields_eq(
        container_perms: ContainerLockedMap,
        old_process_perms: ProcessLockedMap,
        new_process_perms: ProcessLockedMap,
    )
        requires
            per_container_process_tree_wf(container_perms, old_process_perms),
            container_process_wf(container_perms, old_process_perms),
            old_process_perms.dom() == new_process_perms.dom(),
            forall|p_ptr: RwLockProcessPtr|
                #![trigger new_process_perms.spec_index(p_ptr)]
                old_process_perms.dom().contains(p_ptr) ==>
                    new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                    && new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
                    && new_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq == old_process_perms.spec_index(p_ptr).view_ghost().uppertree_seq
                    && new_process_perms.spec_index(p_ptr).view_ghost().subtree_set == old_process_perms.spec_index(p_ptr).view_ghost().subtree_set
                    && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata(),
        ensures
            per_container_process_tree_wf(container_perms, new_process_perms),
    {
        assert(per_container_process_tree_wf(container_perms, new_process_perms)) by {
            reveal(per_container_process_tree_wf); reveal(container_process_wf);  reveal(process_root_wf); reveal(process_children_parent_wf); reveal(process_linkedlist_wf); reveal(process_children_depth_wf);
            reveal(process_subtree_set_wf); reveal(process_uppertree_seq_wf); reveal(process_subtree_set_exclusive);
        };
    }

#[verifier::loop_isolation(false)]
pub fn process_tree_check_is_ancestor(
    root_process: RwLockProcessPtr,
    process_tree_dom: Ghost<Set<RwLockProcessPtr>>,
    process_perms: &ProcessLockedMap,
    a_ptr: RwLockProcessPtr,
    child_ptr: RwLockProcessPtr,
) -> (ret: bool)
    requires
        process_perms_wf(*process_perms),
        process_tree_wf(root_process, process_tree_dom.view(), *process_perms),
        process_tree_dom.view().contains(a_ptr),
        process_tree_dom.view().contains(child_ptr),
        a_ptr != child_ptr,
    ensures
        ret == process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(a_ptr),
        ret == process_perms.spec_index(a_ptr).view_ghost().subtree_set.view().contains(child_ptr),
{
    proof {
        reveal(process_root_wf);
        reveal(process_children_parent_wf);
        reveal(process_children_depth_wf);
        reveal(process_subtree_set_wf);
        reveal(process_uppertree_seq_wf);
        reveal(process_subtree_set_exclusive);
        assert(process_perms.perms_wf()) by { reveal(process_perms_wf); };
        assert(process_tree_fields_wf(*process_perms)) by { reveal(process_perms_wf); };
        assert(process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().len() == process_perms.spec_index(child_ptr).view_rodata().view().depth) by { reveal(process_perms_wf);  };
    }
    let depth = process_perms.borrow_rodata(child_ptr).borrow().depth;
    if depth == 0 {
        assert(child_ptr == root_process) by { reveal(process_root_wf); };
        assert(process_perms.dom().contains(child_ptr)) by { reveal(process_root_wf); };
        assert(process_perms.spec_index(child_ptr).view_rodata().view().depth == 0) by { reveal(process_perms_wf); };
        assert(process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(a_ptr) == false) by { reveal(Seq::contains); };
        return false;
    }
    let mut current_p_ptr = child_ptr;
    for i in 0..(depth-1)
        invariant
            process_perms.perms_wf(),
            process_tree_fields_wf(*process_perms),
            process_tree_dom.contains(current_p_ptr),
            process_perms.spec_index(current_p_ptr).view_rodata().view().depth == depth - i,
            process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().len() == depth,
            i == 0 ==> current_p_ptr == child_ptr,
            i != 0 ==> current_p_ptr == process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i),
            forall|j:int|
                depth - i <= j < depth ==>
                process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(j) != a_ptr
    {
        let current_ro = process_perms.borrow_rodata(current_p_ptr);
        assert(current_p_ptr != root_process) by { reveal(process_root_wf); };
        assert(current_ro.view().parent is Some) by { reveal(process_children_parent_wf); };
        assert(process_perms.spec_index(current_ro.view().parent.unwrap()).view_rodata().view().depth == depth - i - 1) by { reveal(process_children_depth_wf); };
        let next_parent_ptr = current_ro.borrow().parent.unwrap();
        assert(process_perms.spec_index(current_p_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i - 1) == next_parent_ptr) by { reveal(process_children_depth_wf); };
        assert(next_parent_ptr == process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i - 1)) by {
            if i == 0 {
                assert(next_parent_ptr == process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i - 1)) by { reveal(process_children_depth_wf); };
            } else {
                assert(process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(current_p_ptr)) by { reveal(Seq::contains); };
                assert(process_perms.spec_index(current_p_ptr).view_ghost().uppertree_seq.view() == process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().subrange(0, depth - i)) by { reveal(process_uppertree_seq_wf); };
                assert(next_parent_ptr == process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i - 1)) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
            }
        };
        if next_parent_ptr == a_ptr {
            return true;
        }
        current_p_ptr = next_parent_ptr;
    }
    assert(process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0) == root_process) by {
        assert(process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains((process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0)))) by { reveal(Seq::contains); };
        assert(process_perms.dom().contains(process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0))) by { reveal(process_uppertree_seq_wf); };
        seq_index_lemma::<RwLockProcessPtr>();
        assert(process_perms.spec_index(process_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0)).view_rodata().view().depth == 0) by { reveal(process_uppertree_seq_wf); };
    };
    if root_process == a_ptr {
        return true;
    }
    return false;
}

}
