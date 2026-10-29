use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::PointsTo;

verus! {
    // Proof dependencies (confirmed): container_tree_fields_wf.
    #[verifier::opaque]
    pub open spec fn container_perms_wf(container_perms: ContainerLockedMap) -> bool {
        &&& container_perms.perms_wf()
        &&& containers_inv(container_perms)
        &&& container_tree_fields_wf(container_perms)
    }

    pub open spec fn containers_inv(container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr| #![trigger container_perms.dom().contains(c_ptr)] #![trigger container_perms.spec_index(c_ptr)] container_perms.dom().contains(c_ptr) ==> container_perms.spec_index(c_ptr).inv()
    }

    pub proof fn container_perms_wf_at(container_perms: ContainerLockedMap, container_ptr: RwLockContainerPtr)
        requires
            container_perms_wf(container_perms),
            container_perms.dom().contains(container_ptr),
        ensures
            container_perms.view().spec_index(container_ptr).is_init(),
            container_perms.view().spec_index(container_ptr).addr() == container_ptr,
            container_perms.spec_index(container_ptr).inv(),
            container_perms.spec_index(container_ptr).is_init(),
            container_perms.spec_index(container_ptr).view().inv(),
            container_perms.spec_index(container_ptr).view_ghost().uppertree_seq.view().no_duplicates(),
            container_perms.spec_index(container_ptr).view_ghost().uppertree_seq.view().len() == container_perms.spec_index(container_ptr).view_rodata().view().depth,
            container_perms.spec_index(container_ptr).view_rodata().view().depth <= MAX_CONTAINER_TREE_DEPTH,
            container_perms.spec_index(container_ptr).view().children.view().no_duplicates(),
            !container_perms.spec_index(container_ptr).view().children.view().contains(container_ptr),
    { reveal(container_perms_wf); reveal(container_tree_fields_wf); }

    pub proof fn container_perms_wf_map(container_perms: ContainerLockedMap)
        requires container_perms_wf(container_perms)
        ensures container_perms.perms_wf()
    { reveal(container_perms_wf); }

    #[verifier::opaque]
    pub open spec fn container_tree_fields_wf(container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children]
            #![trigger container_perms.spec_index(c_ptr).view_ghost().uppertree_seq]
            #![trigger container_perms.spec_index(c_ptr).view_ghost().subtree_set]
            #![trigger container_perms.spec_index(c_ptr).view_rodata().view().depth]
            container_perms.dom().contains(c_ptr) ==> {
                &&& container_perms.spec_index(c_ptr).view().children.view().no_duplicates()
                &&& container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().no_duplicates()
                &&& container_perms.spec_index(c_ptr).view().children.view().contains(c_ptr) == false
                &&& container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().len() == container_perms.spec_index(c_ptr).view_rodata().view().depth
                &&& container_perms.spec_index(c_ptr).view_rodata().view().depth <= MAX_CONTAINER_TREE_DEPTH
            }
    }

    #[verifier::opaque]
    pub open spec fn container_root_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        &&& container_perms.dom().contains(root_container)
        &&& container_perms.spec_index(root_container).view_rodata().view().depth == 0
        &&& container_perms.spec_index(root_container).view().parent_linkedlist_node.is_init()
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container ==> {
                &&& container_perms.spec_index(c_ptr).view_rodata().view().depth != 0
                &&& container_perms.spec_index(c_ptr).view().parent_linkedlist_node.is_init() == false
            }
        &&& forall|c_ptr: RwLockContainerPtr| #![trigger container_perms.dom().contains(c_ptr)] container_perms.dom().contains(c_ptr) && c_ptr != root_container ==> container_perms.spec_index(c_ptr).view_rodata().view().parent is Some
    }

    #[verifier::opaque]
    pub open spec fn container_children_parent_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        &&& forall|c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr) ==> container_perms.dom().contains(child_c_ptr)
        &&& forall|c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr) ==> {
                &&& container_perms.spec_index(child_c_ptr).view_rodata().view().parent.unwrap() == c_ptr
                &&& container_perms.spec_index(child_c_ptr).view_rodata().view().depth == container_perms.spec_index(c_ptr).view_rodata().view().depth + 1
            }
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view_rodata().view().parent is Some ==> {
                &&& container_perms.dom().contains(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap())
                &&& container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(c_ptr)
            }
    }

    pub proof fn container_root_wf_at(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, c_ptr: RwLockContainerPtr)
        requires container_root_wf(root_container, container_perms)
        ensures
            c_ptr == root_container ==> container_perms.spec_index(c_ptr).view_rodata().view().depth == 0,
            container_perms.dom().contains(c_ptr) && c_ptr != root_container ==> {
                &&& container_perms.spec_index(c_ptr).view_rodata().view().depth != 0
                &&& container_perms.spec_index(c_ptr).view().parent_linkedlist_node.is_init() == false
                &&& container_perms.spec_index(c_ptr).view_rodata().view().parent is Some
            },
    { reveal(container_root_wf); }

    pub proof fn container_children_parent_wf_at(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, c_ptr: RwLockContainerPtr, child_c_ptr: RwLockContainerPtr)
        requires container_children_parent_wf(root_container, container_perms)
        ensures
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view().children.view().contains(child_c_ptr) ==> {
                &&& container_perms.dom().contains(child_c_ptr)
                &&& container_perms.spec_index(child_c_ptr).view_rodata().view().parent.unwrap() == c_ptr
                &&& container_perms.spec_index(child_c_ptr).view_rodata().view().depth == container_perms.spec_index(c_ptr).view_rodata().view().depth + 1
            },
    { reveal(container_children_parent_wf); }

    /// Container `c_ptr`'s duplicate-free child list holds only 2M-aligned container pointers, so its length is below the pointer bound.
    pub proof fn container_children_len_bounded_at(root_container: RwLockContainerPtr, page_array: PageLockedArray, container_perms: ContainerLockedMap, c_ptr: RwLockContainerPtr)
        requires
            container_perms_wf(container_perms),
            container_children_parent_wf(root_container, container_perms),
            container_pages_wf(page_array, container_perms),
            container_perms.dom().contains(c_ptr),
        ensures container_perms.spec_index(c_ptr).view().children.view().len() <= NUM_PAGES * 4096,
    { container_perms_wf_at(container_perms, c_ptr); reveal(container_children_parent_wf); reveal(container_pages_wf); seq_unique_bounded_usize_len(container_perms.spec_index(c_ptr).view().children.view(), (NUM_PAGES * 4096) as usize); }

    /// A non-root container `c_ptr` whose parent is in the map sits in its parent's child list at its own list node.
    pub proof fn containers_linkedlist_wf_at(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, c_ptr: RwLockContainerPtr)
        requires
            containers_linkedlist_wf(root_container, container_perms),
            container_perms.dom().contains(c_ptr),
            c_ptr != root_container,
        ensures
            container_perms.spec_index(c_ptr).view_rodata().view().parent is Some,
            container_perms.dom().contains(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()) ==> {
                let parent = container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view();
                &&& parent.children.view().contains(c_ptr)
                &&& parent.children.map().dom().contains(container_perms.spec_index(c_ptr).view().parent_linkedlist_node.addr())
                &&& parent.children.map().spec_index(container_perms.spec_index(c_ptr).view().parent_linkedlist_node.addr()) == c_ptr
            },
    { reveal(containers_linkedlist_wf); }

    #[verifier::opaque]
    pub open spec fn containers_linkedlist_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view_rodata().view().parent]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container ==> container_perms.spec_index(c_ptr).view_rodata().view().parent is Some
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container
                && container_perms.dom().contains(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()) ==> {
                &&& container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.view().contains(c_ptr)
                &&& container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.map().dom().contains(container_perms.spec_index(c_ptr).view().parent_linkedlist_node.addr())
                &&& container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.map().spec_index(container_perms.spec_index(c_ptr).view().parent_linkedlist_node.addr()) == c_ptr
            }
    }

    #[verifier::opaque]
    pub open spec fn container_children_depth_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container
                ==> container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().spec_index(container_perms.spec_index(c_ptr).view_rodata().view().depth - 1) == container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()
    }

    /// The last entry of non-root container `c_ptr`'s upper-tree sequence is its parent.
    pub proof fn container_children_depth_wf_at(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, c_ptr: RwLockContainerPtr)
        requires
            container_children_depth_wf(root_container, container_perms),
            container_perms.dom().contains(c_ptr),
            c_ptr != root_container,
        ensures
            container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().spec_index(container_perms.spec_index(c_ptr).view_rodata().view().depth - 1) == container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap(),
    { reveal(container_children_depth_wf); }

    #[verifier::opaque]
    pub open spec fn container_subtree_set_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().contains(sub_c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().contains(sub_c_ptr) ==> {
                &&& container_perms.dom().contains(sub_c_ptr)
                &&& container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().len() > container_perms.spec_index(c_ptr).view_rodata().view().depth
                &&& container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().spec_index(container_perms.spec_index(c_ptr).view_rodata().view().depth as int) == c_ptr
            }
    }

    #[verifier::opaque]
    pub open spec fn container_uppertree_seq_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr, u_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().contains(u_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().contains(u_ptr) ==> {
                &&& container_perms.dom().contains(u_ptr)
                &&& container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().spec_index(container_perms.spec_index(u_ptr).view_rodata().view().depth as int) == u_ptr
                &&& container_perms.spec_index(u_ptr).view_rodata().view().depth == container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().index_of(u_ptr)
                &&& container_perms.spec_index(u_ptr).view_ghost().subtree_set.view().contains(c_ptr)
                &&& container_perms.spec_index(u_ptr).view_ghost().uppertree_seq.view() =~= container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().subrange(0, container_perms.spec_index(u_ptr).view_rodata().view().depth as int)
            }
    }

    /// Ancestor `u_ptr` of container `c_ptr` is a container at its own depth in `c_ptr`'s upper-tree sequence, whose subtree holds `c_ptr`.
    pub proof fn container_uppertree_seq_wf_at(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, c_ptr: RwLockContainerPtr, u_ptr: RwLockContainerPtr)
        requires
            container_uppertree_seq_wf(root_container, container_perms),
            container_perms.dom().contains(c_ptr),
        ensures
            container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().contains(u_ptr) ==> {
                &&& container_perms.dom().contains(u_ptr)
                &&& container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().spec_index(container_perms.spec_index(u_ptr).view_rodata().view().depth as int) == u_ptr
                &&& container_perms.spec_index(u_ptr).view_rodata().view().depth == container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().index_of(u_ptr)
                &&& container_perms.spec_index(u_ptr).view_ghost().subtree_set.view().contains(c_ptr)
                &&& container_perms.spec_index(u_ptr).view_ghost().uppertree_seq.view() =~= container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().subrange(0, container_perms.spec_index(u_ptr).view_rodata().view().depth as int)
            },
    { reveal(container_uppertree_seq_wf); }

    pub proof fn container_uppertree_seq_in_dom(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, container_ptr: RwLockContainerPtr)
        requires
            container_uppertree_seq_wf(root_container, container_perms),
            container_perms.dom().contains(container_ptr),
        ensures forall|u_ptr: RwLockContainerPtr| #[trigger] container_perms.spec_index(container_ptr).view_ghost().uppertree_seq.view().contains(u_ptr) ==> container_perms.dom().contains(u_ptr),
    { reveal(container_uppertree_seq_wf); }

    pub proof fn container_uppertree_seq_not_self(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, container_ptr: RwLockContainerPtr)
        requires
            container_perms_wf(container_perms),
            container_uppertree_seq_wf(root_container, container_perms),
            container_perms.dom().contains(container_ptr),
        ensures !container_perms.spec_index(container_ptr).view_ghost().uppertree_seq.view().contains(container_ptr),
    { reveal(container_perms_wf); reveal(container_tree_fields_wf); reveal(container_uppertree_seq_wf); reveal(Seq::contains); }

    #[verifier::opaque]
    pub open spec fn container_subtree_set_exclusive(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().contains(sub_c_ptr), container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.dom().contains(sub_c_ptr)
                ==> container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().contains(sub_c_ptr) == container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().contains(c_ptr)
    }

    pub proof fn container_subtree_set_exclusive_at(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap, c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr)
        requires
            container_subtree_set_exclusive(root_container, container_perms),
            container_perms.dom().contains(c_ptr),
            container_perms.dom().contains(sub_c_ptr),
        ensures
            container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().contains(sub_c_ptr) == container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().contains(c_ptr),
    { reveal(container_subtree_set_exclusive); }

    pub open spec fn container_tree_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        &&& container_root_wf(root_container, container_perms)
        &&& container_children_parent_wf(root_container, container_perms)
        &&& containers_linkedlist_wf(root_container, container_perms)
        &&& container_children_depth_wf(root_container, container_perms)
        &&& container_subtree_set_wf(root_container, container_perms)
        &&& container_uppertree_seq_wf(root_container, container_perms)
        &&& container_subtree_set_exclusive(root_container, container_perms)
    }

    /// Framing lemma: if every container's tree-relevant payload, rodata, and
    /// tree ghost fields are unchanged and the domain is the same,
    /// then `container_tree_wf` is preserved. Lets callers that only changed
    /// lock-state (not payload) re-establish the tree invariant with a single
    /// cheap call instead of revealing all seven parts inline.
    pub proof fn container_no_change_to_tree_fields_imply_wf(root_container: RwLockContainerPtr, old_container_perms: ContainerLockedMap, new_container_perms: ContainerLockedMap)
        requires
            container_tree_wf(root_container, old_container_perms),
            old_container_perms.dom() =~= new_container_perms.dom(),
            forall|c_ptr: RwLockContainerPtr| #![trigger new_container_perms.spec_index(c_ptr)]
                old_container_perms.dom().contains(c_ptr)
                    ==> new_container_perms.spec_index(c_ptr).view().children == old_container_perms.spec_index(c_ptr).view().children
                    && new_container_perms.spec_index(c_ptr).view().parent_linkedlist_node == old_container_perms.spec_index(c_ptr).view().parent_linkedlist_node
                    && new_container_perms.spec_index(c_ptr).view_rodata() == old_container_perms.spec_index(c_ptr).view_rodata()
                    && new_container_perms.spec_index(c_ptr).view_ghost().uppertree_seq == old_container_perms.spec_index(c_ptr).view_ghost().uppertree_seq
                    && new_container_perms.spec_index(c_ptr).view_ghost().subtree_set == old_container_perms.spec_index(c_ptr).view_ghost().subtree_set,
        ensures
            container_tree_wf(root_container, new_container_perms),
    {
        reveal(container_root_wf); reveal(container_children_parent_wf); reveal(containers_linkedlist_wf); reveal(container_children_depth_wf);
        reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive);
    }

    pub proof fn container_insert_child_into_ancestor_subtree_sets(tracked container_map: &mut ContainerLockedMap, ancestors: Seq<RwLockContainerPtr>, child_ptr: RwLockContainerPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId)
        requires
            old(container_map).perms_wf(),
            ancestors.to_set().subset_of(old(container_map).dom()),
            ancestors.no_duplicates(),
            !ancestors.to_set().contains(child_ptr),
            old(container_map).typed_lock_map_aligned(held_locks, thread_id),
        ensures
            final(container_map).perms_wf(),
            final(container_map).dom() == old(container_map).dom(),
            final(container_map).typed_lock_map_aligned(held_locks, thread_id),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().subtree_set]
                ancestors.to_set().contains(c) ==> final(container_map).spec_index(c).view_ghost().subtree_set == Ghost(old(container_map).spec_index(c).view_ghost().subtree_set.view().insert(child_ptr)),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().subtree_set]
                old(container_map).dom().contains(c) && !ancestors.to_set().contains(c) ==> final(container_map).spec_index(c).view_ghost().subtree_set == old(container_map).spec_index(c).view_ghost().subtree_set,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_rodata()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().uppertree_seq]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().uppertree_seq == old(container_map).spec_index(c).view_ghost().uppertree_seq,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().owned_threads]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().owned_threads == old(container_map).spec_index(c).view_ghost().owned_threads,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().owned_processes]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().owned_processes == old(container_map).spec_index(c).view_ghost().owned_processes,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().owned_indirect_threads]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().owned_indirect_threads == old(container_map).spec_index(c).view_ghost().owned_indirect_threads,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().owned_endpoints]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().owned_endpoints == old(container_map).spec_index(c).view_ghost().owned_endpoints,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).locking_thread()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).being_killed()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).killer_info()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).killer_info() == old(container_map).spec_index(c).killer_info(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).control()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).control() == old(container_map).spec_index(c).control(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().retire_ready]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().retire_ready == old(container_map).spec_index(c).view_ghost().retire_ready,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).is_init()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init(),
        decreases ancestors.len(),
    {
        if ancestors.len() > 0 {
            let c0 = ancestors.spec_index(0);
            assert(ancestors.to_set().contains(c0)) by { ancestors.to_set_ensures(); };
            container_map.update_ghost(c0, ContainerGhost { uppertree_seq: container_map.spec_index(c0).view_ghost().uppertree_seq,
                subtree_set: Ghost(container_map.spec_index(c0).view_ghost().subtree_set.view().insert(child_ptr)), owned_processes: container_map.spec_index(c0).view_ghost().owned_processes,
                owned_threads: container_map.spec_index(c0).view_ghost().owned_threads, owned_indirect_threads: container_map.spec_index(c0).view_ghost().owned_indirect_threads,
                owned_endpoints: container_map.spec_index(c0).view_ghost().owned_endpoints, retire_ready: container_map.spec_index(c0).view_ghost().retire_ready });
            assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(ancestors.drop_first().to_set().subset_of(container_map.dom())) by { ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures(); };
            container_insert_child_into_ancestor_subtree_sets(container_map, ancestors.drop_first(), child_ptr, held_locks, thread_id);
            assert({
                &&& !ancestors.drop_first().to_set().contains(c0)
                &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(c0)
            }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        }
    }

    /// Removes `child_ptr` from the ghost subtree set of every container in `ancestors`; nothing else changes.
    pub proof fn container_remove_child_from_ancestor_subtree_sets(tracked container_map: &mut ContainerLockedMap, ancestors: Seq<RwLockContainerPtr>, child_ptr: RwLockContainerPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId)
        requires
            old(container_map).perms_wf(),
            ancestors.to_set().subset_of(old(container_map).dom()),
            ancestors.no_duplicates(),
            old(container_map).typed_lock_map_aligned(held_locks, thread_id),
        ensures
            final(container_map).perms_wf(),
            final(container_map).dom() == old(container_map).dom(),
            final(container_map).typed_lock_map_aligned(held_locks, thread_id),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().subtree_set]
                ancestors.to_set().contains(c) ==> final(container_map).spec_index(c).view_ghost().subtree_set == Ghost(old(container_map).spec_index(c).view_ghost().subtree_set.view().remove(child_ptr)),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().subtree_set]
                old(container_map).dom().contains(c) && !ancestors.to_set().contains(c) ==> final(container_map).spec_index(c).view_ghost().subtree_set == old(container_map).spec_index(c).view_ghost().subtree_set,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_rodata()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().uppertree_seq]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().uppertree_seq == old(container_map).spec_index(c).view_ghost().uppertree_seq,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().owned_threads]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().owned_threads == old(container_map).spec_index(c).view_ghost().owned_threads,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().owned_processes]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().owned_processes == old(container_map).spec_index(c).view_ghost().owned_processes,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().owned_indirect_threads]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().owned_indirect_threads == old(container_map).spec_index(c).view_ghost().owned_indirect_threads,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().owned_endpoints]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().owned_endpoints == old(container_map).spec_index(c).view_ghost().owned_endpoints,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).locking_thread()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).being_killed()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).killer_info()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).killer_info() == old(container_map).spec_index(c).killer_info(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).control()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).control() == old(container_map).spec_index(c).control(),
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).view_ghost().retire_ready]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).view_ghost().retire_ready == old(container_map).spec_index(c).view_ghost().retire_ready,
            forall|c: RwLockContainerPtr| #![trigger final(container_map).spec_index(c).is_init()]
                old(container_map).dom().contains(c) ==> final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init(),
        decreases ancestors.len(),
    {
        if ancestors.len() > 0 {
            let c0 = ancestors.spec_index(0);
            assert(ancestors.to_set().contains(c0)) by { ancestors.to_set_ensures(); };
            container_map.update_ghost(c0, ContainerGhost { uppertree_seq: container_map.spec_index(c0).view_ghost().uppertree_seq,
                subtree_set: Ghost(container_map.spec_index(c0).view_ghost().subtree_set.view().remove(child_ptr)), owned_processes: container_map.spec_index(c0).view_ghost().owned_processes,
                owned_threads: container_map.spec_index(c0).view_ghost().owned_threads, owned_indirect_threads: container_map.spec_index(c0).view_ghost().owned_indirect_threads,
                owned_endpoints: container_map.spec_index(c0).view_ghost().owned_endpoints, retire_ready: container_map.spec_index(c0).view_ghost().retire_ready });
            assert(container_map.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
            assert(ancestors.drop_first().to_set().subset_of(container_map.dom())) by { ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures(); };
            container_remove_child_from_ancestor_subtree_sets(container_map, ancestors.drop_first(), child_ptr, held_locks, thread_id);
            assert({
                &&& !ancestors.drop_first().to_set().contains(c0)
                &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(c0)
            }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        }
    }

#[verifier::loop_isolation(false)]
pub fn container_tree_check_is_ancestor(root_container: RwLockContainerPtr, container_perms: &ContainerLockedMap, a_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr) -> (ret: bool)
    requires
        container_perms_wf(*container_perms),
        container_tree_wf(root_container, *container_perms),
        container_perms.view().dom().contains(a_ptr),
        container_perms.view().dom().contains(child_ptr),
        a_ptr != child_ptr,
    ensures
        ret == container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(a_ptr),
        ret == container_perms.spec_index(a_ptr).view_ghost().subtree_set.view().contains(child_ptr),
{
    hide(Seq::no_duplicates);
    assert({
        &&& container_perms.view().spec_index(child_ptr).is_init()
        &&& container_perms.view().spec_index(child_ptr).addr() == child_ptr
        &&& container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(a_ptr) == container_perms.spec_index(a_ptr).view_ghost().subtree_set.view().contains(child_ptr)
    }) by { container_perms_wf_at(*container_perms, child_ptr); container_subtree_set_exclusive_at(root_container, *container_perms, a_ptr, child_ptr); };
    let current_child_ro = container_perms.borrow_rodata(child_ptr);
    let depth = current_child_ro.borrow().depth;
    assert({
        &&& container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().len() == depth
        &&& container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().no_duplicates()
    }) by { container_perms_wf_at(*container_perms, child_ptr); };
    assert((depth == 0) == (child_ptr == root_container)) by { container_root_wf_at(root_container, *container_perms, child_ptr); };
    if depth == 0 {
        return false;
    }
    let mut current_c_ptr = child_ptr;
    for i in 0..(depth-1)
        invariant
            container_perms.dom().contains(current_c_ptr),
            container_perms.spec_index(current_c_ptr).view_rodata().view().depth == depth - i,
            i == 0 ==> current_c_ptr == child_ptr,
            i != 0 ==> current_c_ptr == container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i),
            forall|j:int| depth - i <= j < depth ==> container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(j) != a_ptr
    {
        assert({
            &&& container_perms.view().spec_index(current_c_ptr).is_init()
            &&& container_perms.view().spec_index(current_c_ptr).addr() == current_c_ptr
        }) by { container_perms_wf_at(*container_perms, current_c_ptr); };
        let current_ro = container_perms.borrow_rodata(current_c_ptr);
        assert({
            &&& current_ro.view().parent is Some
            &&& current_c_ptr != root_container
        }) by { container_root_wf_at(root_container, *container_perms, current_c_ptr); };
        let next_parent_ptr = current_ro.borrow().parent.unwrap();
        if i == 0 {
            assert(next_parent_ptr == container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i - 1)) by { container_children_depth_wf_at(root_container, *container_perms, current_c_ptr); };
        } else {
            assert(container_perms.spec_index(current_c_ptr).view_ghost().uppertree_seq.view() == container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().subrange(0, depth - i)) by {
                container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().lemma_index_contains(depth - i); container_uppertree_seq_wf_at(root_container, *container_perms, child_ptr, current_c_ptr);
            };
            assert(next_parent_ptr == container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i - 1)) by { container_children_depth_wf_at(root_container, *container_perms, current_c_ptr); };
        }
        if next_parent_ptr == a_ptr {
            return true;
        }
        assert({
            &&& container_perms.dom().contains(next_parent_ptr)
            &&& container_perms.spec_index(next_parent_ptr).view_rodata().view().depth == depth - i - 1
        }) by {
            reveal(Seq::no_duplicates); container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().lemma_index_contains(depth - i - 1);
            container_uppertree_seq_wf_at(root_container, *container_perms, child_ptr, next_parent_ptr);
        };
        current_c_ptr = next_parent_ptr;
    }
    assert({
        &&& container_perms.dom().contains(container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0))
        &&& container_perms.spec_index(container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0)).view_rodata().view().depth == 0
    }) by {
        reveal(Seq::no_duplicates); container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().lemma_index_contains(0);
        container_uppertree_seq_wf_at(root_container, *container_perms, child_ptr, container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0));
    };
    assert(container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0) == root_container) by {
        container_root_wf_at(root_container, *container_perms, container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0));
    };
    if root_container == a_ptr {
        return true;
    }
    return false;
}
}
