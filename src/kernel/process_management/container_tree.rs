use vstd::prelude::*;
use crate::*;

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
    pub open spec fn container_perms_wf(container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>) -> bool{
        &&&
        container_perms.perms_wf()
        &&&
        containers_wlocked_or_inv(container_perms)
    }
    pub open spec fn containers_wlocked_or_inv(container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>) -> bool{
        &&&
        forall|container_p:RwLockContainerPtr|
            #![auto]
            container_perms.dom().contains(container_p)
            ==>
            container_perms[container_p].wlocked() || container_perms[container_p].inv()
    }

    pub open spec fn container_tree_fields_wf(
        container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,
    ) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children]
            #![trigger container_perms.spec_index(c_ptr).view().uppertree_seq]
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set]
            #![trigger container_perms.spec_index(c_ptr).view().depth]
            container_perms.dom().contains(c_ptr) 
            ==> 
            container_perms.spec_index(c_ptr).wlocked()
            ||
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

    pub proof fn container_root_wf_imply_container_root_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_root_wf(root_container, container_perms) <==> container_root_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_root_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_root_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_root_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
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
            container_perms.spec_index(c_ptr).wlocked()
            ||
            container_perms.spec_index(c_ptr).view().depth != 0
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && c_ptr != root_container
            ==>
            container_perms.spec_index(c_ptr).wlocked()
            || 
            container_perms.spec_index(root_container).view().parent is Some
    }

    pub proof fn container_childern_parent_wf_imply_container_childern_parent_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_childern_parent_wf(root_container, container_perms) <==> container_childern_parent_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_childern_parent_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_childern_parent_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_childern_parent_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        forall|c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.spec_index(c_ptr).view().children@.contains(child_c_ptr)
            ==> 
            container_perms.spec_index(c_ptr).wlocked()
            ||
            container_perms.dom().contains(child_c_ptr)
        &&& 
        forall|c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children@.contains(child_c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view().children@.contains(child_c_ptr) 
            &&
            container_perms.dom().contains(child_c_ptr) 
            ==> 
            write_locked_by_same_thread(container_perms.spec_index(c_ptr), container_perms.spec_index(child_c_ptr))
            ||
            {
                &&&
                container_perms.spec_index(child_c_ptr).view().parent.unwrap() == c_ptr
                &&&
                container_perms.spec_index(child_c_ptr).view().depth == container_perms.spec_index(root_container).view().depth + 1
            }
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.spec_index(c_ptr).view().parent is Some
            ==>
            container_perms.spec_index(c_ptr).wlocked()
            ||
            {
                &&&
                container_perms.dom().contains(container_perms.spec_index(c_ptr).view().parent.unwrap())
                &&&
                {
                    |||
                    write_locked_by_same_thread(container_perms.spec_index(c_ptr), container_perms.spec_index(container_perms.spec_index(root_container).view().parent.unwrap()))
                    |||
                    container_perms.spec_index(container_perms.spec_index(root_container).view().parent.unwrap()).view().children.view().contains(c_ptr)
                }
            }
    }

    pub proof fn containers_linkedlist_wf_imply_containers_linkedlist_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>)
        ensures
            containers_linkedlist_wf(root_container, container_perms) <==> containers_linkedlist_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn containers_linkedlist_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        containers_linkedlist_wf_inner(root_container, container_perms)
    }

    pub open spec fn containers_linkedlist_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().parent]
            container_perms.dom().contains(c_ptr) 
            && 
            c_ptr != root_container
            ==>
            container_perms.spec_index(c_ptr).wlocked()
            ||
            container_perms.spec_index(c_ptr).view().parent is Some 
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container
            &&
            container_perms.dom().contains(container_perms.spec_index(c_ptr).view().parent.unwrap())
            ==> 
            write_locked_by_same_thread(container_perms.spec_index(c_ptr), container_perms.spec_index(container_perms.spec_index(c_ptr).view().parent.unwrap()))
            ||
            {
                container_perms[container_perms.spec_index(c_ptr).view().parent.unwrap()].view().children@.contains(c_ptr)
                && 
                container_perms[container_perms.spec_index(c_ptr).view().parent.unwrap()].view().children.map()[c_ptr] 
                    == container_perms.spec_index(root_container).view().parent_linkedlist_node.addr()
            }
    }

    pub proof fn container_childern_depth_wf_imply_container_childern_depth_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_childern_depth_wf(root_container, container_perms) <==> container_childern_depth_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_childern_depth_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_childern_depth_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_childern_depth_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            c_ptr != root_container
            ==> 
            container_perms.spec_index(c_ptr).wlocked()
            ||
            container_perms.spec_index(c_ptr).view().uppertree_seq@[container_perms.spec_index(c_ptr).view().depth - 1] 
                == container_perms.spec_index(c_ptr).view().parent.unwrap()
    }

    pub proof fn container_subtree_set_wf_imply_container_subtree_set_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_subtree_set_wf(root_container, container_perms) <==> container_subtree_set_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_subtree_set_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_subtree_set_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_subtree_set_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set@.contains(sub_c_ptr)]
            container_perms.dom().contains(c_ptr)
            && 
            container_perms.spec_index(c_ptr).view().subtree_set@.contains(sub_c_ptr)
            ==> 
            {
                container_perms.spec_index(c_ptr).wlocked()
                ||
                container_perms.dom().contains(sub_c_ptr)
            }
            &&
            {
                container_perms.dom().contains(sub_c_ptr)
                ==>
                write_locked_by_same_thread(container_perms.spec_index(c_ptr), container_perms.spec_index(sub_c_ptr))
                ||
                {
                    container_perms[sub_c_ptr].view().uppertree_seq@.len() > container_perms.spec_index(c_ptr).view().depth
                    && 
                    container_perms[sub_c_ptr].view().uppertree_seq@[container_perms.spec_index(c_ptr).view().depth as int] == c_ptr
                }
            }
    }

    pub proof fn container_uppertree_seq_wf_imply_container_uppertree_seq_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_uppertree_seq_wf(root_container, container_perms) <==> container_uppertree_seq_wf_inner(root_container, container_perms),
    {}

    pub closed spec fn container_uppertree_seq_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_uppertree_seq_wf_inner(root_container, container_perms)
    }

    pub open spec fn container_uppertree_seq_wf_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, u_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().uppertree_seq@.contains(u_ptr)]
            container_perms.dom().contains(c_ptr)
            && 
            container_perms.spec_index(c_ptr).view().uppertree_seq@.contains(u_ptr)
            ==> 
            {
                container_perms.spec_index(c_ptr).wlocked()
                ||
                container_perms.dom().contains(u_ptr)
            }
            && 
            {
                container_perms.dom().contains(u_ptr)
                ==>
                write_locked_by_same_thread(container_perms.spec_index(c_ptr), container_perms[u_ptr])
                ||
                {
                    container_perms.spec_index(root_container).view().uppertree_seq@[container_perms[u_ptr].view().depth as int] == u_ptr 
                    && 
                    container_perms[u_ptr].view().depth == container_perms.spec_index(root_container).view().uppertree_seq@.index_of(u_ptr)
                    && 
                    container_perms[u_ptr].view().subtree_set@.contains(c_ptr)
                    && 
                    container_perms[u_ptr].view().uppertree_seq@ =~= container_perms.spec_index(root_container).view().uppertree_seq@.subrange(0, container_perms[u_ptr].view().depth as int)
                }
            }
    }

    
    pub proof fn container_subtree_set_exclusive_imply_container_subtree_set_exclusive_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>)
        ensures
            container_subtree_set_exclusive(root_container, container_perms) <==> container_subtree_set_exclusive_inner(root_container, container_perms),
    {}

    pub closed spec fn container_subtree_set_exclusive(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&&
        container_subtree_set_exclusive_inner(root_container, container_perms)
    }

    pub open spec fn container_subtree_set_exclusive_inner(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().subtree_set@.contains(sub_c_ptr), container_perms[sub_c_ptr].view().uppertree_seq@.contains(c_ptr)]
            container_perms.dom().contains(c_ptr) 
            && 
            container_perms.dom().contains(sub_c_ptr) 
            ==> 
            write_locked_by_same_thread(container_perms.spec_index(c_ptr), container_perms.spec_index(sub_c_ptr))
            ||
            container_perms.spec_index(c_ptr).view().subtree_set@.contains(sub_c_ptr) == container_perms[sub_c_ptr].view().uppertree_seq@.contains(c_ptr)
    }

    pub open spec fn container_tree_wf(root_container: RwLockContainerPtr, container_perms: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,) -> bool {
        &&& container_root_wf(root_container, container_perms)
        &&& container_childern_parent_wf(root_container, container_perms)
        &&& containers_linkedlist_wf(root_container, container_perms)
        &&& container_childern_depth_wf(root_container, container_perms)
        &&& container_subtree_set_wf(root_container, container_perms)
        &&& container_uppertree_seq_wf(root_container, container_perms)
        &&& container_subtree_set_exclusive(root_container, container_perms)
    }

#[verifier::loop_isolation(false)]
pub fn container_tree_check_is_ancestor(Tracked(lctx): Tracked<&LocalContext>, root_container: RwLockContainerPtr, container_perms: &LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>, 
        a_ptr: RwLockContainerPtr, Tracked(child_lock_perm):Tracked<&LockPerm>, child_ptr: RwLockContainerPtr) -> (ret: bool)
    requires
        container_perms_wf(*container_perms),
        container_tree_wf(root_container, *container_perms),
        container_perms@.dom().contains(a_ptr),
        container_perms@.dom().contains(child_ptr),

        container_perms.spec_index(child_ptr).locked_by(lctx),
        container_perms.spec_index(a_ptr).locked_by(lctx) == false,
        container_perms.spec_index(child_ptr).inv(),

        child_lock_perm.thread_id() == lctx.thread_id(),
        child_lock_perm.state() is WriteLock ==> container_perms.spec_index(child_ptr).write_lock_perm_match(child_lock_perm),
        child_lock_perm.state() is ReadLock ==> container_perms.spec_index(child_ptr).read_lock_perm_match(child_lock_perm),
    ensures
        ret == container_perms[child_ptr].view().uppertree_seq@.contains(a_ptr),
        ret == container_perms[a_ptr].view().subtree_set@.contains(child_ptr),
{
    let child_container_ref = container_perms.borrow(child_ptr, Tracked(lctx), Tracked(child_lock_perm));
    let mut ret = false;
    for i in 0..child_container_ref.uppertree_seq.len()
        invariant
            0 <= i <= child_container_ref.uppertree_seq.len(),
            forall|j: usize|
                #![auto]
                0<= j < i ==> child_container_ref.uppertree_seq@[j as int] != a_ptr,
    {
        if *child_container_ref.uppertree_seq.get(i) == a_ptr {
            return true;
        }
    }
    return false;
}
}