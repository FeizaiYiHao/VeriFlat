use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::PointsTo;

verus! {
    pub struct NumContainers{
        pub inner: usize,
    }
    impl NumContainers{
        pub open spec fn view(&self) -> usize{
            self.inner
        }
    }
    impl LockInvTrait for NumContainers{
        open spec fn inv(&self) -> bool {
            true
        }
    }
    #[verifier::opaque]
    pub open spec fn container_perms_wf(container_perms: ContainerLockedMap) -> bool{
        &&&
        container_perms.perms_wf()
        &&&
        containers_inv(container_perms)
        &&&
        container_tree_fields_wf(container_perms)
    }

    pub open spec fn containers_inv(container_perms: ContainerLockedMap) -> bool{
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![auto]
            container_perms.dom().contains(c_ptr)
            ==>
            container_perms.spec_index(c_ptr).inv()
    }

    #[verifier::opaque]
    pub open spec fn container_tree_fields_wf(
        container_perms: ContainerLockedMap,
    ) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children]
            #![trigger container_perms.spec_index(c_ptr).view().uppertree_seq]
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set]
            #![trigger container_perms.spec_index(c_ptr).view_rodata().view().depth]
            // #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            ==> 
            {
                &&&
                container_perms.spec_index(c_ptr).view().children.view().no_duplicates()
                &&&
                container_perms.spec_index(c_ptr).view().uppertree_seq.view().no_duplicates()
                &&&
                container_perms.spec_index(c_ptr).view().children.view().contains(c_ptr) == false
                &&&
                container_perms.spec_index(c_ptr).view().uppertree_seq.view().len()
                    ==
                    container_perms.spec_index(c_ptr).view_rodata().view().depth
            }
    }

    #[verifier::opaque]
    pub open spec fn container_root_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap,) -> bool {
        &&& 
        container_perms.dom().contains(root_container)
        &&& 
        container_perms.spec_index(root_container).view_rodata().view().depth == 0
        &&& 
        container_perms.spec_index(root_container).view().parent_linkedlist_node.is_init()
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && c_ptr != root_container
            ==> 
            container_perms.spec_index(c_ptr).view_rodata().view().depth != 0
            &&
            container_perms.spec_index(c_ptr).view().parent_linkedlist_node.is_init() == false
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && c_ptr != root_container
            ==>
            container_perms.spec_index(c_ptr).view_rodata().view().parent is Some
    }

    #[verifier::opaque]
    pub open spec fn container_children_parent_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap,) -> bool {
        &&&
        forall|c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr)
            ==> 
            container_perms.dom().contains(child_c_ptr)
        &&& 
        forall|c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr)
            ==> 
            container_perms.spec_index(child_c_ptr).view_rodata().view().parent.unwrap() == c_ptr
            &&
            container_perms.spec_index(child_c_ptr).view_rodata().view().depth == container_perms.spec_index(c_ptr).view_rodata().view().depth + 1
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.spec_index(c_ptr).view_rodata().view().parent is Some
            ==>
            container_perms.dom().contains(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap())
            &&
            container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(c_ptr)
    }

    #[verifier::opaque]
    pub open spec fn containers_linkedlist_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view_rodata().view().parent]
            container_perms.dom().contains(c_ptr) 
            && 
            c_ptr != root_container
            ==>
            container_perms.spec_index(c_ptr).view_rodata().view().parent is Some 
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container
            &&
            container_perms.dom().contains(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap())
            ==> 
            {
                container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(c_ptr)
                && 
                container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.map().spec_index(c_ptr)
                    == container_perms.spec_index(c_ptr).view().parent_linkedlist_node.addr()
            }
    }

    #[verifier::opaque]
    pub open spec fn container_children_depth_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            c_ptr != root_container
            ==> 
            container_perms.spec_index(c_ptr).view().uppertree_seq.view().spec_index(container_perms.spec_index(c_ptr).view_rodata().view().depth - 1)
                == container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()
    }

    #[verifier::opaque]
    pub open spec fn container_subtree_set_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set.view().contains(sub_c_ptr)]
            container_perms.dom().contains(c_ptr)
            && 
            container_perms.spec_index(c_ptr).view().subtree_set.view().contains(sub_c_ptr)
            ==> 
            {
                &&&
                container_perms.dom().contains(sub_c_ptr)
                &&&
                container_perms.spec_index(sub_c_ptr).view().uppertree_seq.view().len() > container_perms.spec_index(c_ptr).view_rodata().view().depth
                &&& 
                container_perms.spec_index(sub_c_ptr).view().uppertree_seq.view().spec_index(container_perms.spec_index(c_ptr).view_rodata().view().depth as int) == c_ptr

            }
    }

    #[verifier::opaque]
    pub open spec fn container_uppertree_seq_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, u_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().uppertree_seq.view().contains(u_ptr)]
            container_perms.dom().contains(c_ptr)
            && 
            container_perms.spec_index(c_ptr).view().uppertree_seq.view().contains(u_ptr)
            ==> 
            container_perms.dom().contains(u_ptr)
            &&
            container_perms.spec_index(c_ptr).view().uppertree_seq.view().spec_index(container_perms.spec_index(u_ptr).view_rodata().view().depth as int) == u_ptr
            &&
            container_perms.spec_index(u_ptr).view_rodata().view().depth == container_perms.spec_index(c_ptr).view().uppertree_seq.view().index_of(u_ptr)
            &&
            container_perms.spec_index(u_ptr).view().subtree_set.view().contains(c_ptr)
            &&
            container_perms.spec_index(u_ptr).view().uppertree_seq.view() =~= container_perms.spec_index(c_ptr).view().uppertree_seq.view().subrange(0, container_perms.spec_index(u_ptr).view_rodata().view().depth as int)
    }

    #[verifier::opaque]
    pub open spec fn container_subtree_set_exclusive(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set.view().contains(sub_c_ptr), container_perms.spec_index(sub_c_ptr).view().uppertree_seq.view().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.dom().contains(sub_c_ptr) 
            ==> 
            container_perms.spec_index(c_ptr).view().subtree_set.view().contains(sub_c_ptr) == container_perms.spec_index(sub_c_ptr).view().uppertree_seq.view().contains(c_ptr)
    }

    pub open spec fn container_tree_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap,) -> bool {
        &&& container_root_wf(root_container, container_perms)
        &&& container_children_parent_wf(root_container, container_perms)
        &&& containers_linkedlist_wf(root_container, container_perms)
        &&& container_children_depth_wf(root_container, container_perms)
        &&& container_subtree_set_wf(root_container, container_perms)
        &&& container_uppertree_seq_wf(root_container, container_perms)
        &&& container_subtree_set_exclusive(root_container, container_perms)
    }

    /// Framing lemma: if every container's tree-relevant view (the full
    /// `view()` and `view_rodata()`) is unchanged and the domain is the same,
    /// then `container_tree_wf` is preserved. Lets callers that only changed
    /// lock-state (not payload) re-establish the tree invariant with a single
    /// cheap call instead of revealing all seven parts inline.
    #[verifier::spinoff_prover]
    pub proof fn container_no_change_to_tree_fields_imply_wf(
        root_container: RwLockContainerPtr,
        old_container_perms: ContainerLockedMap,
        new_container_perms: ContainerLockedMap,
    )
        requires
            container_tree_wf(root_container, old_container_perms),
            old_container_perms.dom() =~= new_container_perms.dom(),
            forall|c_ptr: RwLockContainerPtr|
                #![trigger new_container_perms.spec_index(c_ptr)]
                old_container_perms.dom().contains(c_ptr) ==>
                    new_container_perms.spec_index(c_ptr).view() == old_container_perms.spec_index(c_ptr).view()
                    && new_container_perms.spec_index(c_ptr).view_rodata() == old_container_perms.spec_index(c_ptr).view_rodata(),
        ensures
            container_tree_wf(root_container, new_container_perms),
    {
        reveal(container_root_wf);
        reveal(container_children_parent_wf);
        reveal(containers_linkedlist_wf);
        reveal(container_children_depth_wf);
        reveal(container_subtree_set_wf);
        reveal(container_uppertree_seq_wf);
        reveal(container_subtree_set_exclusive);
    }

#[verifier::loop_isolation(false)]
pub fn container_tree_check_is_ancestor(root_container: RwLockContainerPtr, container_perms: &ContainerLockedMap, 
        a_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr) -> (ret: bool)
    requires
        container_perms_wf(*container_perms),
        container_tree_wf(root_container, *container_perms),
        container_perms.view().dom().contains(a_ptr),
        container_perms.view().dom().contains(child_ptr),
        a_ptr != child_ptr,
    ensures
        ret == container_perms.spec_index(child_ptr).view().uppertree_seq.view().contains(a_ptr),
        ret == container_perms.spec_index(a_ptr).view().subtree_set.view().contains(child_ptr),
{
    assert({
        &&& container_perms.view().spec_index(child_ptr).is_init()
        &&& container_perms.view().spec_index(child_ptr).addr() == child_ptr
        &&& container_perms.spec_index(child_ptr).view().uppertree_seq.view()
            .contains(a_ptr) == container_perms.spec_index(a_ptr).view()
                .subtree_set.view().contains(child_ptr)
    }) by {
        reveal(container_perms_wf);
        reveal(container_subtree_set_exclusive);
    };
    let current_child_ro = container_perms.borrow_rodata(child_ptr);
    let depth = current_child_ro.borrow().depth;
    assert({
        &&& container_perms.spec_index(child_ptr).view().uppertree_seq.view().len()
            == depth
        &&& container_perms.spec_index(child_ptr).view().uppertree_seq.view()
            .no_duplicates()
    }) by {
        reveal(container_tree_fields_wf);
        reveal(container_perms_wf);
    };
    assert((depth == 0) == (child_ptr == root_container)) by {
        reveal(container_root_wf);
    };
    if depth == 0 {
        return false;
    }
    let mut current_c_ptr = child_ptr;
    for i in 0..(depth-1)
        invariant
            container_perms.dom().contains(current_c_ptr),
            container_perms.spec_index(current_c_ptr).view_rodata().view().depth == depth - i,
            i == 0 ==> current_c_ptr == child_ptr,
            i != 0 ==> current_c_ptr == container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i),
            forall|j:int|
                depth - i <= j < depth ==>
                container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(j) != a_ptr
            
    {
        assert({
            &&& container_perms.view().spec_index(current_c_ptr).is_init()
            &&& container_perms.view().spec_index(current_c_ptr).addr()
                == current_c_ptr
        }) by {
            reveal(container_perms_wf);
        };
        let current_ro = container_perms.borrow_rodata(current_c_ptr);
        assert({
            &&& current_ro.view().parent is Some
            &&& current_c_ptr != root_container
        }) by {
            reveal(container_root_wf);
        };
        let next_parent_ptr = current_ro.borrow().parent.unwrap();
        if i == 0 {
            assert(next_parent_ptr == container_perms.spec_index(child_ptr).view()
                .uppertree_seq.view().spec_index(depth - i - 1)) by {
                reveal(container_children_depth_wf);
            };
        } else {
            assert(container_perms.spec_index(child_ptr).view().uppertree_seq.view()
                .contains(current_c_ptr)) by {
                reveal(container_tree_fields_wf);
            };
            assert(container_perms.spec_index(current_c_ptr).view().uppertree_seq.view()
                == container_perms.spec_index(child_ptr).view().uppertree_seq.view()
                    .subrange(0, depth - i)) by {
                reveal(container_uppertree_seq_wf);
            };
            assert(next_parent_ptr == container_perms.spec_index(child_ptr).view()
                .uppertree_seq.view().spec_index(depth - i - 1)) by {
                reveal(container_children_depth_wf);
            };
        }
        if next_parent_ptr == a_ptr {
            return true;
        }
        assert(container_perms.spec_index(child_ptr).view().uppertree_seq.view()
            .contains(next_parent_ptr)) by {
            reveal(container_tree_fields_wf);
        };
        assert({
            &&& container_perms.dom().contains(next_parent_ptr)
            &&& container_perms.spec_index(next_parent_ptr).view_rodata().view().depth
                == depth - i - 1
        }) by {
            reveal(container_uppertree_seq_wf);
        };
        current_c_ptr = next_parent_ptr;
    }
    assert(container_perms.spec_index(child_ptr).view().uppertree_seq.view()
        .contains(container_perms.spec_index(child_ptr).view().uppertree_seq.view()
            .spec_index(0))) by {
        reveal(container_tree_fields_wf);
    };
    assert({
        &&& container_perms.dom().contains(container_perms.spec_index(child_ptr)
            .view().uppertree_seq.view().spec_index(0))
        &&& container_perms.spec_index(container_perms.spec_index(child_ptr).view()
            .uppertree_seq.view().spec_index(0)).view_rodata().view().depth == 0
    }) by {
        reveal(container_uppertree_seq_wf);
    };
    assert(container_perms.spec_index(child_ptr).view().uppertree_seq.view()
        .spec_index(0) == root_container) by {
        reveal(container_root_wf);
    };
    if root_container == a_ptr{
        return true;
    }
    return false;
}

}
