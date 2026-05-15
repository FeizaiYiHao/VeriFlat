use vstd::prelude::*;
use crate::*;

verus! {
    pub open spec fn process_perms_wf(process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>) -> bool{
        &&&
        process_perms.perms_wf()
        &&&
        process_tree_fields_wf(process_perms)
        &&&
        forall|p_ptr:RwLockProcessPtr|
            #![auto]
            process_perms.dom().contains(p_ptr)
            ==>
            process_perms[p_ptr].inv()
    }

    pub open spec fn process_tree_fields_wf(
        process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,
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
                process_perms.spec_index(p_ptr).view().subtree_set.view().finite()
                &&&
                process_perms.spec_index(p_ptr).view().uppertree_seq.view().len()
                    ==
                    process_perms.spec_index(p_ptr).view_rodata().view().depth
            }
    }

    pub proof fn process_root_wf_imply_process_root_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>)
        ensures
            process_root_wf(root_process, process_tree_dom, process_perms) <==> process_root_wf_inner(root_process, process_tree_dom, process_perms),
    {}

    pub closed spec fn process_root_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&&
        process_root_wf_inner(root_process, process_tree_dom, process_perms)
    }

    pub open spec fn process_root_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
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

    pub proof fn process_childern_parent_wf_imply_process_childern_parent_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>)
        ensures
            process_childern_parent_wf(root_process, process_tree_dom, process_perms) <==> process_childern_parent_wf_inner(root_process, process_tree_dom, process_perms),
    {}

    pub closed spec fn process_childern_parent_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&&
        process_childern_parent_wf_inner(root_process, process_tree_dom, process_perms)
    }

    pub open spec fn process_childern_parent_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&&
        forall|p_ptr: RwLockProcessPtr, child_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().children.view().contains(child_p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && 
            process_perms.spec_index(p_ptr).view().children@.contains(child_p_ptr) 
            ==> 
            process_tree_dom.contains(child_p_ptr)
        &&& 
        forall|p_ptr: RwLockProcessPtr, child_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().children@.contains(child_p_ptr)]
            process_tree_dom.contains(p_ptr) && process_perms.spec_index(p_ptr).view().children@.contains(child_p_ptr) 
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

    pub proof fn processs_linkedlist_wf_imply_processs_linkedlist_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>)
        ensures
            processs_linkedlist_wf(root_process, process_tree_dom, process_perms) <==> processs_linkedlist_wf_inner(root_process, process_tree_dom, process_perms),
    {}

    pub closed spec fn processs_linkedlist_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&&
        processs_linkedlist_wf_inner(root_process, process_tree_dom, process_perms)
    }

    pub open spec fn processs_linkedlist_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
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
                process_perms[process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()].view().children@.contains(p_ptr)
                &&& 
                process_perms[process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()].view().children.map()[p_ptr] 
                    == process_perms.spec_index(p_ptr).view().parent_linkedlist_node.addr()
            }
    }

    pub proof fn process_childern_depth_wf_imply_process_childern_depth_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>)
        ensures
            process_childern_depth_wf(root_process, process_tree_dom, process_perms) <==> process_childern_depth_wf_inner(root_process, process_tree_dom, process_perms),
    {}

    pub closed spec fn process_childern_depth_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&&
        process_childern_depth_wf_inner(root_process, process_tree_dom, process_perms)
    }

    pub open spec fn process_childern_depth_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr|
            #![trigger process_tree_dom.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && 
            p_ptr != root_process
            ==> 
            process_perms.spec_index(p_ptr).view().uppertree_seq@[process_perms.spec_index(p_ptr).view_rodata().view().depth - 1] 
                == process_perms.spec_index(p_ptr).view_rodata().view().parent.unwrap()
    }

    pub proof fn process_subtree_set_wf_imply_process_subtree_set_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>)
        ensures
            process_subtree_set_wf(root_process, process_tree_dom, process_perms) <==> process_subtree_set_wf_inner(root_process, process_tree_dom, process_perms),
    {}

    pub closed spec fn process_subtree_set_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&&
        process_subtree_set_wf_inner(root_process, process_tree_dom, process_perms)
    }

    pub open spec fn process_subtree_set_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().subtree_set@.contains(sub_p_ptr)]
            process_tree_dom.contains(p_ptr)
            && 
            process_perms.spec_index(p_ptr).view().subtree_set@.contains(sub_p_ptr)
            ==> 
            {
                &&&
                process_tree_dom.contains(sub_p_ptr)
                &&&
                process_perms[sub_p_ptr].view().uppertree_seq@.len() > process_perms.spec_index(p_ptr).view_rodata().view().depth
                &&&
                process_perms[sub_p_ptr].view().uppertree_seq@[process_perms.spec_index(p_ptr).view_rodata().view().depth as int] == p_ptr
            }
    }

    pub proof fn process_uppertree_seq_wf_imply_process_uppertree_seq_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>)
        ensures
            process_uppertree_seq_wf(root_process, process_tree_dom, process_perms) <==> process_uppertree_seq_wf_inner(root_process, process_tree_dom, process_perms),
    {}

    pub closed spec fn process_uppertree_seq_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&&
        process_uppertree_seq_wf_inner(root_process, process_tree_dom, process_perms)
    }

    pub open spec fn process_uppertree_seq_wf_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, u_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().uppertree_seq@.contains(u_ptr)]
            process_tree_dom.contains(p_ptr)
            && 
            process_perms.spec_index(p_ptr).view().uppertree_seq@.contains(u_ptr)
            ==> 
            {
                &&&
                process_tree_dom.contains(u_ptr)
                &&&
                process_perms.spec_index(p_ptr).view().uppertree_seq@[process_perms[u_ptr].view_rodata().view().depth as int] == u_ptr 
                &&&
                process_perms[u_ptr].view_rodata().view().depth == process_perms.spec_index(p_ptr).view().uppertree_seq@.index_of(u_ptr)
                &&&
                process_perms[u_ptr].view().subtree_set@.contains(p_ptr)
                &&&
                process_perms[u_ptr].view().uppertree_seq@ =~= process_perms.spec_index(p_ptr).view().uppertree_seq@.subrange(0, process_perms[u_ptr].view_rodata().view().depth as int)
            }
    }

    
    pub proof fn process_subtree_set_exclusive_imply_process_subtree_set_exclusive_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>)
        ensures
            process_subtree_set_exclusive(root_process, process_tree_dom, process_perms) <==> process_subtree_set_exclusive_inner(root_process, process_tree_dom, process_perms),
    {}

    pub closed spec fn process_subtree_set_exclusive(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&&
        process_subtree_set_exclusive_inner(root_process, process_tree_dom, process_perms)
    }

    pub open spec fn process_subtree_set_exclusive_inner(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&& 
        forall|p_ptr: RwLockProcessPtr, sub_p_ptr: RwLockProcessPtr|
            #![trigger process_perms.spec_index(p_ptr).view().subtree_set@.contains(sub_p_ptr), process_perms[sub_p_ptr].view().uppertree_seq@.contains(p_ptr)]
            process_tree_dom.contains(p_ptr) 
            && 
            process_tree_dom.contains(sub_p_ptr) 
            ==> 
            process_perms.spec_index(p_ptr).view().subtree_set@.contains(sub_p_ptr) == process_perms[sub_p_ptr].view().uppertree_seq@.contains(p_ptr)
    }

    pub open spec fn process_tree_wf(root_process: RwLockProcessPtr, process_tree_dom: Set<RwLockProcessPtr>, process_perms: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>,) -> bool {
        &&& process_root_wf(root_process, process_tree_dom, process_perms)
        &&& process_childern_parent_wf(root_process, process_tree_dom, process_perms)
        &&& processs_linkedlist_wf(root_process, process_tree_dom, process_perms)
        &&& process_childern_depth_wf(root_process, process_tree_dom, process_perms)
        &&& process_subtree_set_wf(root_process, process_tree_dom, process_perms)
        &&& process_uppertree_seq_wf(root_process, process_tree_dom, process_perms)
        &&& process_subtree_set_exclusive(root_process, process_tree_dom, process_perms)
    }

// #[verifier::loop_isolation(false)]
// pub fn process_tree_check_is_ancestor(Tracked(lctx): Tracked<&LocalContext>, root_process: RwLockProcessPtr, process_tree_dom: Ghost<Set<RwLockProcessPtr>>, process_perms: &LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>, 
//         a_ptr: RwLockProcessPtr, Tracked(child_lock_perm):Tracked<&LockPerm>, child_ptr: RwLockProcessPtr) -> (ret: bool)
//     requires
//         process_perms_wf(*process_perms),
//         process_tree_wf(root_process, process_tree_dom@, *process_perms),
//         process_tree_dom@.contains(a_ptr),
//         process_tree_dom@.contains(child_ptr),

//         process_perms.spec_index(child_ptr).locked_by(lctx),
//         process_perms.spec_index(a_ptr).locked_by(lctx) == false,
//         process_perms.spec_index(child_ptr).inv(),

//         child_lock_perm.thread_id() == lctx.thread_id(),
//         child_lock_perm.state() is WriteLock ==> process_perms.spec_index(child_ptr).write_lock_perm_match(child_lock_perm),
//         child_lock_perm.state() is ReadLock ==> process_perms.spec_index(child_ptr).read_lock_perm_match(child_lock_perm),
//     ensures
//         ret == process_perms[child_ptr].view().uppertree_seq@.contains(a_ptr),
//         ret == process_perms[a_ptr].view().subtree_set@.contains(child_ptr),
// {
//     let child_process_ref = process_perms.borrow(child_ptr, Tracked(lctx), Tracked(child_lock_perm));
//     let mut ret = false;
//     for i in 0..child_process_ref.uppertree_seq.len()
//         invariant
//             0 <= i <= child_process_ref.uppertree_seq.len(),
//             forall|j: usize|
//                 #![auto]
//                 0<= j < i ==> child_process_ref.uppertree_seq@[j as int] != a_ptr,
//     {
//         if *child_process_ref.uppertree_seq.get(i) == a_ptr {
//             return true;
//         }
//     }
//     return false;
// }

#[verifier::loop_isolation(false)]
pub fn process_tree_check_is_ancestor(root_process: RwLockProcessPtr, process_tree_dom: Ghost<Set<RwLockProcessPtr>>, process_perms: &LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, (), PROCESS_HAS_KILL_STATE>, 
        a_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr) -> (ret: bool)
    requires
        process_perms_wf(*process_perms),
        process_tree_wf(root_process, process_tree_dom@, *process_perms),
        process_tree_dom@.contains(a_ptr),
        process_tree_dom@.contains(child_ptr),
        
        a_ptr != child_ptr,
    ensures
        ret == process_perms[child_ptr].view().uppertree_seq@.contains(a_ptr),
        ret == process_perms[a_ptr].view().subtree_set@.contains(child_ptr),
{
    let current_child_ro = process_perms.borrow_rodata(child_ptr);
    let current_p_ptr_op = current_child_ro.borrow().parent;
    let depth = current_child_ro.borrow().depth;
    if depth == 0 {
        assert(child_ptr == root_process);
        assert(process_perms.dom().contains(child_ptr));
        assert(process_perms[child_ptr].view_rodata().view().depth == 0);
        assert(process_perms[child_ptr].view().uppertree_seq.view().len() == 0);
        assert(process_perms[child_ptr].view().uppertree_seq@.contains(a_ptr) == false);
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