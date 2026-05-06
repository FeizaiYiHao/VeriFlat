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
    pub open spec fn container_perms_wf(container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>) -> bool{
        &&&
        container_perms.perms_wf()
        &&&
        containers_inv(container_perms)
        &&&
        container_tree_fields_wf(container_perms)
    }
    pub open spec fn container_ro_perms_wf(container_ro_map: Tracked<Map<usize, PointsTo<ReadOnlyNode<ContainerRO>>>>) -> bool{
        &&&
        forall|ro_c_ptr:usize|
            #![auto]
            container_ro_map.view().dom().contains(ro_c_ptr)
            ==>
            container_ro_map.view().spec_index(ro_c_ptr).is_init() &&
                container_ro_map.view().spec_index(ro_c_ptr).addr() == ro_c_ptr
    }

    pub proof fn container_ro_perms_match_container_perms_proof()
        ensures
        forall|container_map: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,
            container_ro_map: Tracked<Map<usize, PointsTo<ReadOnlyNode<ContainerRO>>>>|
            container_ro_perms_match_container_perms(container_map, container_ro_map)
            <==>
            container_ro_perms_match_container_perms_inner(container_map, container_ro_map)
    {}

    pub closed spec fn container_ro_perms_match_container_perms(container_map: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,
            container_ro_map: Tracked<Map<usize, PointsTo<ReadOnlyNode<ContainerRO>>>>) -> bool 
    {
        &&&
        container_ro_perms_match_container_perms_inner(container_map, container_ro_map)
    }
    pub open spec fn container_ro_perms_match_container_perms_inner(container_map: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,
            container_ro_map: Tracked<Map<usize, PointsTo<ReadOnlyNode<ContainerRO>>>>) -> bool 
    {
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![auto]
            container_map.dom().contains(c_ptr)
            ==>
            container_map.spec_index(c_ptr).view().read_only_external_node.is_init() == false
            &&
            container_ro_map.dom().contains(container_map.spec_index(c_ptr).view().read_only_external_node.addr())
            &&
            container_ro_map.spec_index(
                container_map.spec_index(c_ptr).view().read_only_external_node.addr()).value()
                .owner_addr() == c_ptr
            &&
            container_ro_map.spec_index(
                container_map.spec_index(c_ptr).view().read_only_external_node.addr()).value().view()
                .parent == container_map.spec_index(c_ptr).view().parent
        &&&
        forall|c_ro_ptr:usize|
            #![auto]
            container_ro_map.dom().contains(c_ro_ptr)
            ==>
            container_map.dom().contains(container_ro_map.spec_index(c_ro_ptr).value().owner_addr())
            &&
            container_map.spec_index(container_ro_map.spec_index(c_ro_ptr).value().owner_addr()).view().read_only_external_node.addr() 
                == c_ro_ptr
            
    }

    pub open spec fn containers_inv(container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>) -> bool{
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![auto]
            container_perms.dom().contains(c_ptr)
            ==>
            container_perms.spec_index(c_ptr).inv()
            &&
            container_perms.spec_index(c_ptr).view_rodata() == container_perms.spec_index(c_ptr).view().to_rodata()
    }

    pub closed spec fn container_tree_fields_wf(
        container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,
    ) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children]
            #![trigger container_perms.spec_index(c_ptr).view().uppertree_seq]
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set]
            #![trigger container_perms.spec_index(c_ptr).view().depth]
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
                container_perms.spec_index(c_ptr).view().subtree_set.view().finite()
                &&&
                container_perms.spec_index(c_ptr).view().uppertree_seq.view().len()
                    ==
                    container_perms.spec_index(c_ptr).view().depth
            }
    }

    pub proof fn container_root_wf_imply_container_root_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_root_wf(root_container, container_perms) <==> container_root_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_root_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_root_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_root_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        container_perms.dom().contains(root_container)
        &&& 
        container_perms.spec_index(root_container).view().depth == 0
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && c_ptr != root_container
            ==> 
            container_perms.spec_index(c_ptr).view().depth != 0
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && c_ptr != root_container
            ==>
            container_perms.spec_index(c_ptr).view().parent is Some
    }

    pub proof fn container_childern_parent_wf_imply_container_childern_parent_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_childern_parent_wf(root_container, container_perms) <==> container_childern_parent_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_childern_parent_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_childern_parent_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_childern_parent_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        forall|c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.spec_index(c_ptr).view().children@.contains(child_c_ptr)
            ==> 
            container_perms.dom().contains(child_c_ptr)
        &&& 
        forall|c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children@.contains(child_c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view().children@.contains(child_c_ptr) 
            ==> 
            container_perms.spec_index(child_c_ptr).view().parent.unwrap() == c_ptr
            &&
            container_perms.spec_index(child_c_ptr).view().depth == container_perms.spec_index(c_ptr).view().depth + 1
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.spec_index(c_ptr).view().parent is Some
            ==>
            container_perms.dom().contains(container_perms.spec_index(c_ptr).view().parent.unwrap())
            &&
            container_perms.spec_index(container_perms.spec_index(c_ptr).view().parent.unwrap()).view().children.view().contains(c_ptr)
    }

    pub proof fn containers_linkedlist_wf_imply_containers_linkedlist_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>)
        ensures
            containers_linkedlist_wf(root_container, container_perms) <==> containers_linkedlist_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn containers_linkedlist_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        containers_linkedlist_wf_inner(root_container, container_perms)
    }

    pub open spec fn containers_linkedlist_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().parent]
            container_perms.dom().contains(c_ptr) 
            && 
            c_ptr != root_container
            ==>
            container_perms.spec_index(c_ptr).view().parent is Some 
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container
            &&
            container_perms.dom().contains(container_perms.spec_index(c_ptr).view().parent.unwrap())
            ==> 
            {
                container_perms[container_perms.spec_index(c_ptr).view().parent.unwrap()].view().children@.contains(c_ptr)
                && 
                container_perms[container_perms.spec_index(c_ptr).view().parent.unwrap()].view().children.map()[c_ptr] 
                    == container_perms.spec_index(c_ptr).view().parent_linkedlist_node.addr()
            }
    }

    pub proof fn container_childern_depth_wf_imply_container_childern_depth_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_childern_depth_wf(root_container, container_perms) <==> container_childern_depth_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_childern_depth_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_childern_depth_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_childern_depth_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            c_ptr != root_container
            ==> 
            container_perms.spec_index(c_ptr).view().uppertree_seq@[container_perms.spec_index(c_ptr).view().depth - 1] 
                == container_perms.spec_index(c_ptr).view().parent.unwrap()
    }

    pub proof fn container_subtree_set_wf_imply_container_subtree_set_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_subtree_set_wf(root_container, container_perms) <==> container_subtree_set_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_subtree_set_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_subtree_set_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_subtree_set_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set@.contains(sub_c_ptr)]
            container_perms.dom().contains(c_ptr)
            && 
            container_perms.spec_index(c_ptr).view().subtree_set@.contains(sub_c_ptr)
            ==> 
            {
                &&&
                container_perms.dom().contains(sub_c_ptr)
                &&&
                container_perms[sub_c_ptr].view().uppertree_seq@.len() > container_perms.spec_index(c_ptr).view().depth
                &&& 
                container_perms[sub_c_ptr].view().uppertree_seq@[container_perms.spec_index(c_ptr).view().depth as int] == c_ptr

            }
    }

    pub proof fn container_uppertree_seq_wf_imply_container_uppertree_seq_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_uppertree_seq_wf(root_container, container_perms) <==> container_uppertree_seq_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_uppertree_seq_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_uppertree_seq_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_uppertree_seq_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, u_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().uppertree_seq@.contains(u_ptr)]
            container_perms.dom().contains(c_ptr)
            && 
            container_perms.spec_index(c_ptr).view().uppertree_seq@.contains(u_ptr)
            ==> 
            container_perms.dom().contains(u_ptr)
            &&
            container_perms.spec_index(c_ptr).view().uppertree_seq@[container_perms[u_ptr].view().depth as int] == u_ptr 
            &&
            container_perms[u_ptr].view().depth == container_perms.spec_index(c_ptr).view().uppertree_seq@.index_of(u_ptr)
            &&
            container_perms[u_ptr].view().subtree_set@.contains(c_ptr)
            &&
            container_perms[u_ptr].view().uppertree_seq@ =~= container_perms.spec_index(c_ptr).view().uppertree_seq@.subrange(0, container_perms[u_ptr].view().depth as int)
    }

    
    pub proof fn container_subtree_set_exclusive_imply_container_subtree_set_exclusive_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_subtree_set_exclusive(root_container, container_perms) <==> container_subtree_set_exclusive_inner(root_container, container_perms),
    {}

    pub closed spec fn container_subtree_set_exclusive(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_subtree_set_exclusive_inner(root_container, container_perms)
    }

    pub open spec fn container_subtree_set_exclusive_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set@.contains(sub_c_ptr), container_perms[sub_c_ptr].view().uppertree_seq@.contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.dom().contains(sub_c_ptr) 
            ==> 
            container_perms.spec_index(c_ptr).view().subtree_set@.contains(sub_c_ptr) == container_perms[sub_c_ptr].view().uppertree_seq@.contains(c_ptr)
    }

    pub open spec fn container_tree_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& container_root_wf(root_container, container_perms)
        &&& container_childern_parent_wf(root_container, container_perms)
        &&& containers_linkedlist_wf(root_container, container_perms)
        &&& container_childern_depth_wf(root_container, container_perms)
        &&& container_subtree_set_wf(root_container, container_perms)
        &&& container_uppertree_seq_wf(root_container, container_perms)
        &&& container_subtree_set_exclusive(root_container, container_perms)
    }

// #[verifier::loop_isolation(false)]
// pub fn container_tree_check_is_ancestor_1(Tracked(lctx): Tracked<&LocalContext>, root_container: RwLockContainerPtr, container_perms: &LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>, 
//         a_ptr: RwLockContainerPtr, Tracked(child_lock_perm):Tracked<&LockPerm>, child_ptr: RwLockContainerPtr) -> (ret: bool)
//     requires
//         container_perms_wf(*container_perms),
//         container_tree_wf(root_container, *container_perms),
//         container_perms@.dom().contains(a_ptr),
//         container_perms@.dom().contains(child_ptr),

//         container_perms.spec_index(child_ptr).locked_by(lctx),
//         container_perms.spec_index(a_ptr).locked_by(lctx) == false,
//         container_perms.spec_index(child_ptr).inv(),

//         child_lock_perm.thread_id() == lctx.thread_id(),
//         child_lock_perm.state() is WriteLock ==> container_perms.spec_index(child_ptr).write_lock_perm_match(child_lock_perm),
//         child_lock_perm.state() is ReadLock ==> container_perms.spec_index(child_ptr).read_lock_perm_match(child_lock_perm),
//     ensures
//         ret == container_perms[child_ptr].view().uppertree_seq@.contains(a_ptr),
//         ret == container_perms[a_ptr].view().subtree_set@.contains(child_ptr),
// {
//     let child_container_ref = container_perms.borrow(child_ptr, Tracked(lctx), Tracked(child_lock_perm));
//     let mut ret = false;
//     for i in 0..child_container_ref.uppertree_seq.len()
//         invariant
//             0 <= i <= child_container_ref.uppertree_seq.len(),
//             forall|j: usize|
//                 #![auto]
//                 0<= j < i ==> child_container_ref.uppertree_seq@[j as int] != a_ptr,
//     {
//         if *child_container_ref.uppertree_seq.get(i) == a_ptr {
//             return true;
//         }
//     }
//     return false;
// }

#[verifier::loop_isolation(false)]
pub fn container_tree_check_is_ancestor(root_container: RwLockContainerPtr, container_perms: &LockedMap<RwLockContainerPtr, Container, ContainerRO, CONTAINER_HAS_KILL_STATE>, 
        a_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr) -> (ret: bool)
    requires
        container_perms_wf(*container_perms),
        container_tree_wf(root_container, *container_perms),
        container_perms@.dom().contains(a_ptr),
        container_perms@.dom().contains(child_ptr),
        a_ptr != child_ptr,
    ensures
        ret == container_perms[child_ptr].view().uppertree_seq@.contains(a_ptr),
        ret == container_perms[a_ptr].view().subtree_set@.contains(child_ptr),
{
    let current_child_ro = container_perms.borrow_rodata(child_ptr);
    let current_c_ptr_op = current_child_ro.parent;
    let depth = current_child_ro.depth;
    if depth == 0 {
        assert(child_ptr == root_container);
        assert(container_perms[child_ptr].view().uppertree_seq@.contains(a_ptr) == false);
        return false;
    }
    let mut current_c_ptr = child_ptr;
    for i in 0..(depth-1)
        invariant
            container_perms.dom().contains(current_c_ptr),
            container_perms.spec_index(current_c_ptr).view().depth == depth - i,
            i == 0 ==> current_c_ptr == child_ptr,
            i != 0 ==> current_c_ptr == container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i),
            forall|j:int|
                depth - i <= j < depth ==>
                container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(j) != a_ptr
            
    {
        assert(depth - i >= 0);
        let current_ro = container_perms.borrow_rodata(current_c_ptr);
        assert(container_perms.spec_index(current_c_ptr).view().depth == depth - i);
        assert(current_ro.parent is Some);
        assert(container_perms.spec_index(current_ro.parent.unwrap()).view().depth == depth - i - 1);
        let next_parent_ptr = current_ro.parent.unwrap();
        assert(container_perms.spec_index(current_c_ptr).view().uppertree_seq.view().spec_index(depth - i - 1) == next_parent_ptr);
        assert(next_parent_ptr == container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i - 1)) by {
            if i == 0{
                assert(next_parent_ptr == container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i - 1));
            }else{
                assert(container_perms.spec_index(child_ptr).view().uppertree_seq.view().contains(current_c_ptr));
                assert(container_perms.spec_index(current_c_ptr).view().uppertree_seq.view() == container_perms.spec_index(child_ptr).view().uppertree_seq.view().subrange(0, depth - i));
                assert(next_parent_ptr == container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(depth - i - 1));
            }
        };
        if next_parent_ptr == a_ptr {
            return true;
        }
        current_c_ptr = next_parent_ptr;
    }
    assert(container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(0) == root_container) by {
        assert(container_perms.spec_index(child_ptr).view().uppertree_seq.view().contains((container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(0))));
        assert(container_perms.dom().contains(container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(0)));
        assert(container_perms.spec_index(container_perms.spec_index(child_ptr).view().uppertree_seq.view().spec_index(0)).view().depth == 0);
    };
    if root_container == a_ptr{
        return true;
    }
    return false;
}

}