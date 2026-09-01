use vstd::prelude::*;
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
            #![trigger process_perms.spec_index(p_ptr).view().uppertree_seq]
            #![trigger process_perms.spec_index(p_ptr).view().subtree_set]
            #![trigger process_perms.spec_index(p_ptr).view_rodata().view().depth]
            process_perms.dom().contains(p_ptr) 
            ==> 
            {
                &&&
                process_perms.spec_index(p_ptr).view().children.view().no_duplicates()
                &&&
                process_perms.spec_index(p_ptr).view().uppertree_seq.view().no_duplicates()
                &&&
                process_perms.spec_index(p_ptr).view().children.view().contains(p_ptr) == false
                &&&
                process_perms.spec_index(p_ptr).view().uppertree_seq.view().len()
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
            process_perms.spec_index(p_ptr).view_rodata().view().depth != 0
            &&& 
            process_perms.spec_index(root_process).view().parent_linkedlist_node.is_init() == false
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
                process_perms.spec_index(process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()).view().children.map().spec_index(p_ptr)
                    == process_perms.spec_index(p_ptr).view().parent_linkedlist_node.addr()
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
            process_perms.spec_index(p_ptr).view().uppertree_seq.view().spec_index(process_perms.spec_index(p_ptr).view_rodata().view().depth - 1)
                == process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()
    }

    #[verifier::opaque]
    pub open spec fn process_subtree_set_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().subtree_set.view().contains(sub_p_ptr)]
            process_tree_dom.contains(p_ptr)
            && 
            process_perms.spec_index(p_ptr).view().subtree_set.view().contains(sub_p_ptr)
            ==> 
            {
                &&&
                process_tree_dom.contains(sub_p_ptr)
                &&&
                process_perms.spec_index(sub_p_ptr).view().uppertree_seq.view().len() > process_perms.spec_index(p_ptr).view_rodata().view().depth
                &&&
                process_perms.spec_index(sub_p_ptr).view().uppertree_seq.view().spec_index(process_perms.spec_index(p_ptr).view_rodata().view().depth as int) == p_ptr
            }
    }

    #[verifier::opaque]
    pub open spec fn process_uppertree_seq_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, u_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().uppertree_seq.view().contains(u_ptr)]
            process_tree_dom.contains(p_ptr)
            && 
            process_perms.spec_index(p_ptr).view().uppertree_seq.view().contains(u_ptr)
            ==> 
            {
                &&&
                process_tree_dom.contains(u_ptr)
                &&&
                process_perms.spec_index(p_ptr).view().uppertree_seq.view().spec_index(process_perms.spec_index(u_ptr).view_rodata().view().depth as int) == u_ptr
                &&&
                process_perms.spec_index(u_ptr).view_rodata().view().depth == process_perms.spec_index(p_ptr).view().uppertree_seq.view().index_of(u_ptr)
                &&&
                process_perms.spec_index(u_ptr).view().subtree_set.view().contains(p_ptr)
                &&&
                process_perms.spec_index(u_ptr).view().uppertree_seq.view() =~= process_perms.spec_index(p_ptr).view().uppertree_seq.view().subrange(0, process_perms.spec_index(u_ptr).view_rodata().view().depth as int)
            }
    }

    #[verifier::opaque]
    pub open spec fn process_subtree_set_exclusive(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: ProcessLockedMap,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().subtree_set.view().contains(sub_p_ptr), process_perms.spec_index(sub_p_ptr).view().uppertree_seq.view().contains(p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && 
            process_tree_dom.contains(sub_p_ptr) 
            ==> 
            process_perms.spec_index(p_ptr).view().subtree_set.view().contains(sub_p_ptr) == process_perms.spec_index(sub_p_ptr).view().uppertree_seq.view().contains(p_ptr)
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

    /// Framing lemma: if every process in the tree domain has unchanged
    /// tree-relevant fields, then `process_tree_wf` is preserved. Unlike a
    /// `Container`, a `Process.view()` also carries non-tree state
    /// (`quota_*`, `pagetable`, `owned_threads`) that
    /// `process_tree_wf` never reads, so requiring full `view()` equality (as
    /// `container_no_change_to_tree_fields_imply_wf` does) would needlessly
    /// shut out callers that stage pages or adjust quota while leaving the tree
    /// intact. We require equality only on the fields `process_tree_wf` reads:
    /// `children`, `parent_linkedlist_node`, `uppertree_seq`, `subtree_set`
    /// (off `view()`) and the whole read-only `view_rodata()` (immutable, so
    /// always equal — `depth`/`parent` are the parts the tree invariant uses).
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
                    && new_process_perms.spec_index(p_ptr).view().uppertree_seq == old_process_perms.spec_index(p_ptr).view().uppertree_seq
                    && new_process_perms.spec_index(p_ptr).view().subtree_set == old_process_perms.spec_index(p_ptr).view().subtree_set
                    && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata(),
        ensures
            process_tree_wf(root_process, process_tree_dom, new_process_perms),
    {
        reveal(process_root_wf);
        reveal(process_children_parent_wf);
        reveal(process_linkedlist_wf);
        reveal(process_children_depth_wf);
        reveal(process_subtree_set_wf);
        reveal(process_uppertree_seq_wf);
        reveal(process_subtree_set_exclusive);
    }

    /// Quantified-fact form of `process_no_change_to_tree_fields_imply_wf`: a
    /// single invocation installs the fact for ALL `(root, dom, old, new)`, so a
    /// caller need not spell out the tuple or wrap it in an `assert forall` — the
    /// SMT instantiates `process_tree_wf(root, dom, new)` wherever the goal needs
    /// it. Multi-trigger on the source + target `process_tree_wf` terms: fires
    /// once the caller has `process_tree_wf(root, dom, old)` in scope and the goal
    /// mentions `process_tree_wf(root, dom, new)`.
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
                        && new_process_perms.spec_index(p_ptr).view().uppertree_seq == old_process_perms.spec_index(p_ptr).view().uppertree_seq
                        && new_process_perms.spec_index(p_ptr).view().subtree_set == old_process_perms.spec_index(p_ptr).view().subtree_set
                        && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata())
                ==>
                process_tree_wf(root_process, process_tree_dom, new_process_perms),
    {
        assert forall|
            root_process: RwLockProcessPtr,
            process_tree_dom: Set<RwLockProcessPtr>,
            old_process_perms: ProcessLockedMap,
            new_process_perms: ProcessLockedMap,
        |  #![auto]
            (process_tree_wf(root_process, process_tree_dom, old_process_perms)
            && process_tree_dom.subset_of(new_process_perms.dom())
            && forall|p_ptr: RwLockProcessPtr|
                #![trigger new_process_perms.spec_index(p_ptr)]
                process_tree_dom.contains(p_ptr) ==>
                    new_process_perms.spec_index(p_ptr).view().children == old_process_perms.spec_index(p_ptr).view().children
                    && new_process_perms.spec_index(p_ptr).view().parent_linkedlist_node == old_process_perms.spec_index(p_ptr).view().parent_linkedlist_node
                    && new_process_perms.spec_index(p_ptr).view().uppertree_seq == old_process_perms.spec_index(p_ptr).view().uppertree_seq
                    && new_process_perms.spec_index(p_ptr).view().subtree_set == old_process_perms.spec_index(p_ptr).view().subtree_set
                    && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata())
            implies
            process_tree_wf(root_process, process_tree_dom, new_process_perms)
        by {
            process_no_change_to_tree_fields_imply_wf(
                root_process, process_tree_dom, old_process_perms, new_process_perms);
        };
    }

    /// `forall`-lifted twin of `process_no_change_to_tree_fields_imply_wf`:
    /// re-establishes `per_container_process_tree_wf` for the WHOLE container map
    /// in one call, so a caller mutating non-tree process state (staging, quota)
    /// need not hand-write the per-container `assert forall|c_ptr| ... by { ... }`
    /// loop — it just invokes this and the SMT expands the quantifier. Requires
    /// the per-process tree-field equality scoped to the fields `process_tree_wf`
    /// reads (see the point-wise twin), same `container_perms`, and same process
    /// dom (a process mutation preserves it). `container_process_wf` supplies each
    /// container's `owned_processes ⊆ process dom` so the per-container
    /// `subset_of` precondition discharges.
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
                    && new_process_perms.spec_index(p_ptr).view().uppertree_seq == old_process_perms.spec_index(p_ptr).view().uppertree_seq
                    && new_process_perms.spec_index(p_ptr).view().subtree_set == old_process_perms.spec_index(p_ptr).view().subtree_set
                    && new_process_perms.spec_index(p_ptr).view_rodata() == old_process_perms.spec_index(p_ptr).view_rodata(),
        ensures
            per_container_process_tree_wf(container_perms, new_process_perms),
    {
        reveal(per_container_process_tree_wf);
        reveal(container_process_wf);
        assert forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().root_process]
            #![trigger container_perms.spec_index(c_ptr).view().owned_processes]
            container_perms.dom().contains(c_ptr)
            implies container_perms.spec_index(c_ptr).view().owned_processes.view().is_empty()
                || process_tree_wf(container_perms.spec_index(c_ptr).view().root_process, container_perms.spec_index(c_ptr).view().owned_processes.view(), new_process_perms)
        by {
            if !container_perms.spec_index(c_ptr).view().owned_processes.view().is_empty() {
                process_no_change_to_tree_fields_imply_wf(
                    container_perms.spec_index(c_ptr).view().root_process,
                    container_perms.spec_index(c_ptr).view().owned_processes.view(),
                    old_process_perms, new_process_perms);
            }
        };
    }

#[verifier::loop_isolation(false)]
pub fn process_tree_check_is_ancestor(root_process: RwLockProcessPtr, process_tree_dom: Ghost<Set<RwLockProcessPtr>>, process_perms: &ProcessLockedMap,
        a_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr) -> (ret: bool)
    requires
        process_perms_wf(*process_perms),
        process_tree_wf(root_process, process_tree_dom.view(), *process_perms),
        process_tree_dom.view().contains(a_ptr),
        process_tree_dom.view().contains(child_ptr),
        
        a_ptr != child_ptr,
    ensures
        ret == process_perms.spec_index(child_ptr).view().uppertree_seq.view().contains(a_ptr),
        ret == process_perms.spec_index(a_ptr).view().subtree_set.view().contains(child_ptr),
{
    proof {
        reveal(process_root_wf);
        reveal(process_children_parent_wf);
        reveal(process_children_depth_wf);
        reveal(process_subtree_set_wf);
        reveal(process_uppertree_seq_wf);
        reveal(process_subtree_set_exclusive);
    }
    let current_child_ro = process_perms.borrow_rodata(child_ptr);
    let current_p_ptr_op = current_child_ro.borrow().parent;
    let depth = current_child_ro.borrow().depth;
    if depth == 0 {
        assert(child_ptr == root_process);
        assert(process_perms.dom().contains(child_ptr));
        assert(process_perms.spec_index(child_ptr).view_rodata().view().depth == 0);
        assert(process_perms.spec_index(child_ptr).view().uppertree_seq.view().len() == 0);
        assert(process_perms.spec_index(child_ptr).view().uppertree_seq.view().contains(a_ptr) == false);
        return false;
    }
    let mut current_p_ptr = child_ptr;
    for i in 0..(depth-1)
        invariant
            process_tree_dom.contains(current_p_ptr),
            process_perms.spec_index(current_p_ptr).view_rodata().view().depth == depth - i,
            i == 0 ==> current_p_ptr == child_ptr,
            i != 0 ==> current_p_ptr == process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i),
            forall|j:int|
                depth - i <= j < depth ==>
                process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(j) != a_ptr
            
    {
        assert(depth - i >= 0);
        let current_ro = process_perms.borrow_rodata(current_p_ptr);
        assert(process_perms.spec_index(current_p_ptr).view_rodata().view().depth == depth - i);
        assert(current_p_ptr != root_process);
        assert(current_ro.view().parent is Some);
        assert(process_perms.spec_index(current_ro.view().parent.unwrap()).view_rodata().view().depth == depth - i - 1);
        let next_parent_ptr = current_ro.borrow().parent.unwrap();
        assert(process_perms.spec_index(current_p_ptr).view().uppertree_seq.view().spec_index(depth - i - 1) == next_parent_ptr);
        assert(next_parent_ptr == process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i - 1)) by {
            if i == 0{
                assert(next_parent_ptr == process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i - 1));
            }else{
                assert(process_perms.spec_index(child_ptr).view().uppertree_seq.view().contains(current_p_ptr));
                assert(process_perms.spec_index(current_p_ptr).view().uppertree_seq.view() == process_perms.spec_index(child_ptr).view().uppertree_seq.view().subrange(0, depth - i));
                assert(next_parent_ptr == process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i - 1));
            }
        };
        if next_parent_ptr == a_ptr {
            return true;
        }
        current_p_ptr = next_parent_ptr;
    }
    assert(process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(0) == root_process) by {
        assert(process_perms.spec_index(child_ptr).view().uppertree_seq.view().contains((process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(0))));
        assert(process_perms.dom().contains(process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(0)));
        assert(process_perms.spec_index(process_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(0)).view_rodata().view().depth == 0);
    };
    if root_process == a_ptr{
        return true;
    }
    return false;
}

}
