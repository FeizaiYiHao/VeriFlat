use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::PointsTo;

verus! {
    pub struct NumContainers {
        pub inner: usize,
    }
    impl NumContainers {
        pub open spec fn view(&self) -> usize {
            self.inner
        }
    }
    impl LockInvTrait for NumContainers {
        open spec fn inv(&self) -> bool {
            true
        }
    }
    #[verifier::opaque]
    pub open spec fn container_perms_wf(container_perms: ContainerLockedMap) -> bool {
        &&& container_perms.perms_wf()
        &&& containers_inv(container_perms)
        &&& container_tree_fields_wf(container_perms)
    }

    pub open spec fn containers_inv(container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr|
            #![auto]
            container_perms.dom().contains(c_ptr) ==> container_perms.spec_index(c_ptr).inv()
    }

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
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container ==> container_perms.spec_index(c_ptr).view_rodata().view().parent is Some
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
                &&& container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.map().dom().contains(
                    container_perms.spec_index(c_ptr).view().parent_linkedlist_node.addr(),
                )
                &&& container_perms.spec_index(container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()).view().children.map().spec_index(
                    container_perms.spec_index(c_ptr).view().parent_linkedlist_node.addr(),
                ) == c_ptr
            }
    }

    #[verifier::opaque]
    pub open spec fn container_children_depth_wf(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr|
            #![trigger container_perms.dom().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && c_ptr != root_container ==>
            container_perms.spec_index(c_ptr).view_ghost().uppertree_seq.view().spec_index(container_perms.spec_index(c_ptr).view_rodata().view().depth - 1)
                == container_perms.spec_index(c_ptr).view_rodata().view().parent.unwrap()
    }

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

    #[verifier::opaque]
    pub open spec fn container_subtree_set_exclusive(root_container: RwLockContainerPtr, container_perms: ContainerLockedMap) -> bool {
        forall|c_ptr: RwLockContainerPtr, sub_c_ptr: RwLockContainerPtr|
            #![trigger container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().contains(sub_c_ptr), container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().contains(c_ptr)]
            container_perms.dom().contains(c_ptr) && container_perms.dom().contains(sub_c_ptr) ==>
            container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().contains(sub_c_ptr) == container_perms.spec_index(sub_c_ptr).view_ghost().uppertree_seq.view().contains(c_ptr)
    }

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
                    && new_container_perms.spec_index(c_ptr).view_rodata() == old_container_perms.spec_index(c_ptr).view_rodata()
                    && new_container_perms.spec_index(c_ptr).view_ghost().uppertree_seq
                        == old_container_perms.spec_index(c_ptr).view_ghost().uppertree_seq
                    && new_container_perms.spec_index(c_ptr).view_ghost().subtree_set
                        == old_container_perms.spec_index(c_ptr).view_ghost().subtree_set,
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

    pub open spec fn container_add_child_ensures(
        root_container: RwLockContainerPtr,
        old_container_perms: ContainerLockedMap,
        new_container_perms: ContainerLockedMap,
        parent_ptr: RwLockContainerPtr,
        child_ptr: RwLockContainerPtr,
    ) -> bool {
        &&& container_perms_wf(old_container_perms)
        &&& container_perms_wf(new_container_perms)
        &&& container_tree_wf(root_container, old_container_perms)
        &&& old_container_perms.dom().contains(parent_ptr)
        &&& !old_container_perms.dom().contains(child_ptr)
        &&& old_container_perms.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX
        &&& new_container_perms.dom() == old_container_perms.dom().insert(child_ptr)
        &&& new_container_perms.spec_index(child_ptr).view_rodata().view().parent == Some(parent_ptr)
        &&& new_container_perms.spec_index(child_ptr).view_rodata().view().depth == old_container_perms.spec_index(parent_ptr).view_rodata().view().depth + 1
        &&& new_container_perms.spec_index(child_ptr).view().children.view() == Seq::<RwLockContainerPtr>::empty()
        &&& !new_container_perms.spec_index(child_ptr).view().parent_linkedlist_node.is_init()
        &&& new_container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view() == old_container_perms.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr)
        &&& new_container_perms.spec_index(child_ptr).view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty()
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger old_container_perms.dom().contains(c_ptr)]
            old_container_perms.dom().contains(c_ptr) ==>
                new_container_perms.spec_index(c_ptr).view_rodata() == old_container_perms.spec_index(c_ptr).view_rodata()
                && new_container_perms.spec_index(c_ptr).view().parent_linkedlist_node == old_container_perms.spec_index(c_ptr).view().parent_linkedlist_node
                && (c_ptr != parent_ptr ==> new_container_perms.spec_index(c_ptr).view().children == old_container_perms.spec_index(c_ptr).view().children)
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger old_container_perms.spec_index(c_ptr).view_ghost().uppertree_seq]
            #![trigger new_container_perms.spec_index(c_ptr).view_ghost().uppertree_seq]
            old_container_perms.dom().contains(c_ptr) ==>
                new_container_perms.spec_index(c_ptr).view_ghost().uppertree_seq == old_container_perms.spec_index(c_ptr).view_ghost().uppertree_seq
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger new_container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(c_ptr)]
            new_container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(c_ptr) ==>
                new_container_perms.spec_index(c_ptr).view_ghost().subtree_set.view() == old_container_perms.spec_index(c_ptr).view_ghost().subtree_set.view().insert(child_ptr)
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger old_container_perms.dom().contains(c_ptr)]
            old_container_perms.dom().contains(c_ptr) && !new_container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(c_ptr) ==>
                new_container_perms.spec_index(c_ptr).view_ghost().subtree_set == old_container_perms.spec_index(c_ptr).view_ghost().subtree_set
        &&& new_container_perms.spec_index(parent_ptr).view().children.view() == old_container_perms.spec_index(parent_ptr).view().children.view().push(child_ptr)
        &&& new_container_perms.spec_index(parent_ptr).view().children.map().dom().contains(new_container_perms.spec_index(child_ptr).view().parent_linkedlist_node.addr())
        &&& new_container_perms.spec_index(parent_ptr).view().children.map().spec_index(new_container_perms.spec_index(child_ptr).view().parent_linkedlist_node.addr()) == child_ptr
        &&& forall|node_addr: usize|
            #![trigger old_container_perms.spec_index(parent_ptr).view().children.map().dom().contains(node_addr)]
            old_container_perms.spec_index(parent_ptr).view().children.map().dom().contains(node_addr) ==> {
                &&& new_container_perms.spec_index(parent_ptr).view().children.map().dom().contains(node_addr)
                &&& new_container_perms.spec_index(parent_ptr).view().children.map().spec_index(node_addr) == old_container_perms.spec_index(parent_ptr).view().children.map().spec_index(node_addr)
            }
    }

    pub proof fn container_add_child_preserves_tree_wf(
        root_container: RwLockContainerPtr,
        old_container_perms: ContainerLockedMap,
        new_container_perms: ContainerLockedMap,
        parent_ptr: RwLockContainerPtr,
        child_ptr: RwLockContainerPtr,
    )
        requires
            container_add_child_ensures(root_container, old_container_perms, new_container_perms, parent_ptr, child_ptr),
        ensures
            container_tree_wf(root_container, new_container_perms),
    {
        assert(container_root_wf(root_container, new_container_perms)) by { reveal(container_root_wf); };
        assert(container_children_parent_wf(root_container, new_container_perms)) by {
            reveal(container_children_parent_wf);
            seq_push_lemma::<RwLockContainerPtr>();
        };
        assert(containers_linkedlist_wf(root_container, new_container_perms)) by {
            reveal(container_root_wf); reveal(container_children_parent_wf); reveal(containers_linkedlist_wf);
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
            seq_push_lemma::<RwLockContainerPtr>();
        };
        assert(
            old_container_perms.spec_index(parent_ptr).view_ghost().uppertree_seq.view().len()
                == old_container_perms.spec_index(parent_ptr).view_rodata().view().depth
            && new_container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().len()
                == new_container_perms.spec_index(child_ptr).view_rodata().view().depth
            && new_container_perms.spec_index(child_ptr).view_rodata().view().depth > 0
        ) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
        assert(
            new_container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(
                new_container_perms.spec_index(child_ptr).view_rodata().view().depth - 1,
            ) == parent_ptr
        ) by { seq_push_lemma::<RwLockContainerPtr>(); };
        assert(container_children_depth_wf(root_container, new_container_perms)) by {
            reveal(container_children_depth_wf);
            assert(container_tree_fields_wf(old_container_perms)) by { reveal(container_perms_wf); };
            assert(container_tree_fields_wf(new_container_perms)) by { reveal(container_perms_wf); };
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
            seq_push_lemma::<RwLockContainerPtr>();
            seq_push_unique_lemma::<RwLockContainerPtr>();
        };
        let parent_uppers = old_container_perms.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
        let child_uppers = new_container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view();
        let parent_depth = old_container_perms.spec_index(parent_ptr).view_rodata().view().depth;
        assert(
            parent_uppers.len() == parent_depth
            && child_uppers == parent_uppers.push(parent_ptr)
            && child_uppers.no_duplicates()
        ) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
        assert(!parent_uppers.contains(parent_ptr)) by { reveal(container_uppertree_seq_wf); };
        assert(
            child_uppers.contains(parent_ptr)
            && child_uppers.spec_index(parent_depth as int) == parent_ptr
            && child_uppers.index_of(parent_ptr) == parent_depth
            && child_uppers.subrange(0, parent_depth as int) =~= parent_uppers
        ) by {
            seq_push_lemma::<RwLockContainerPtr>();
            seq_push_unique_lemma::<RwLockContainerPtr>();
        };
        assert(container_uppertree_seq_wf(root_container, new_container_perms)) by {
            seq_push_lemma::<RwLockContainerPtr>();
            seq_push_unique_lemma::<RwLockContainerPtr>();
            reveal(container_uppertree_seq_wf);
            assert(container_tree_fields_wf(old_container_perms)) by { reveal(container_perms_wf); };
            assert(container_tree_fields_wf(new_container_perms)) by { reveal(container_perms_wf); };
            broadcast use vstd::set::lemma_set_insert_same;
            broadcast use vstd::set::lemma_set_insert_different;
        };
        assert(container_subtree_set_wf(root_container, new_container_perms)) by {
            reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf);
            assert(container_tree_fields_wf(old_container_perms)) by { reveal(container_perms_wf); };
            assert(container_tree_fields_wf(new_container_perms)) by { reveal(container_perms_wf); };
            seq_push_lemma::<RwLockContainerPtr>();
            seq_push_unique_lemma::<RwLockContainerPtr>();
        };
        assert(container_subtree_set_exclusive(root_container, new_container_perms)) by {
            reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_set_exclusive);
            assert(container_tree_fields_wf(old_container_perms)) by { reveal(container_perms_wf); };
            assert(container_tree_fields_wf(new_container_perms)) by { reveal(container_perms_wf); };
            seq_push_lemma::<RwLockContainerPtr>();
            seq_push_unique_lemma::<RwLockContainerPtr>();
        };
    }

    pub proof fn container_insert_child_into_ancestor_subtree_sets(
        tracked container_map: &mut ContainerLockedMap,
        ancestors: Seq<RwLockContainerPtr>,
        child_ptr: RwLockContainerPtr,
    )
        requires
            old(container_map).perms_wf(),
            ancestors.to_set().subset_of(old(container_map).dom()),
            ancestors.no_duplicates(),
            !ancestors.to_set().contains(child_ptr),
        ensures
            final(container_map).perms_wf(),
            final(container_map).dom() == old(container_map).dom(),
            forall|c: RwLockContainerPtr| #![auto]
                ancestors.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_ghost().subtree_set.view()
                        =~= old(container_map).spec_index(c).view_ghost().subtree_set.view().insert(child_ptr),
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) && !ancestors.to_set().contains(c) ==>
                    final(container_map).spec_index(c).view_ghost() == old(container_map).spec_index(c).view_ghost(),
            forall|c: RwLockContainerPtr| #![auto]
                old(container_map).dom().contains(c) ==>
                    final(container_map).spec_index(c).view() == old(container_map).spec_index(c).view()
                    && final(container_map).spec_index(c).view_rodata() == old(container_map).spec_index(c).view_rodata()
                    && final(container_map).spec_index(c).view_ghost().uppertree_seq == old(container_map).spec_index(c).view_ghost().uppertree_seq
                    && final(container_map).spec_index(c).view_ghost().owned_threads == old(container_map).spec_index(c).view_ghost().owned_threads
                    && final(container_map).spec_index(c).view_ghost().owned_indirect_threads == old(container_map).spec_index(c).view_ghost().owned_indirect_threads
                    && final(container_map).spec_index(c).is_init() == old(container_map).spec_index(c).is_init()
                    && final(container_map).spec_index(c).locking_thread() == old(container_map).spec_index(c).locking_thread()
                    && final(container_map).spec_index(c).being_killed() == old(container_map).spec_index(c).being_killed(),
        decreases ancestors.len(),
    {
        if ancestors.len() > 0 {
            let c0 = ancestors.spec_index(0);
            assert(ancestors.to_set().contains(c0)) by { ancestors.to_set_ensures(); };
            container_map.update_ghost(c0, ContainerGhost {
                uppertree_seq: container_map.spec_index(c0).view_ghost().uppertree_seq,
                subtree_set: Ghost(container_map.spec_index(c0).view_ghost().subtree_set.view().insert(child_ptr)),
                owned_threads: container_map.spec_index(c0).view_ghost().owned_threads,
                owned_indirect_threads: container_map.spec_index(c0).view_ghost().owned_indirect_threads,
            });
            assert(ancestors.drop_first().to_set().subset_of(container_map.dom())) by {
                ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures();
                broadcast use vstd::seq_lib::lemma_seq_subrange_elements;
            };
            container_insert_child_into_ancestor_subtree_sets(container_map, ancestors.drop_first(), child_ptr);
            assert({
                &&& !ancestors.drop_first().to_set().contains(c0)
                &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(c0)
            }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
        }
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
        ret == container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(a_ptr),
        ret == container_perms.spec_index(a_ptr).view_ghost().subtree_set.view().contains(child_ptr),
{
    assert({
        &&& container_perms.view().spec_index(child_ptr).is_init()
        &&& container_perms.view().spec_index(child_ptr).addr() == child_ptr
        &&& container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view()
            .contains(a_ptr) == container_perms.spec_index(a_ptr).view_ghost()
                .subtree_set.view().contains(child_ptr)
    }) by {
        reveal(container_perms_wf);
        reveal(container_subtree_set_exclusive);
    };
    let current_child_ro = container_perms.borrow_rodata(child_ptr);
    let depth = current_child_ro.borrow().depth;
    assert({
        &&& container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().len()
            == depth
        &&& container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view()
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
            i != 0 ==> current_c_ptr == container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i),
            forall|j:int|
                depth - i <= j < depth ==>
                container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(j) != a_ptr

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
            assert(next_parent_ptr == container_perms.spec_index(child_ptr).view_ghost()
                .uppertree_seq.view().spec_index(depth - i - 1)) by {
                reveal(container_children_depth_wf);
            };
        } else {
            assert(container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view()
                .contains(current_c_ptr)) by {
                reveal(container_tree_fields_wf);
            };
            assert(container_perms.spec_index(current_c_ptr).view_ghost().uppertree_seq.view()
                == container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view()
                    .subrange(0, depth - i)) by {
                reveal(container_uppertree_seq_wf);
            };
            assert(next_parent_ptr == container_perms.spec_index(child_ptr).view_ghost()
                .uppertree_seq.view().spec_index(depth - i - 1)) by {
                reveal(container_children_depth_wf);
            };
        }
        if next_parent_ptr == a_ptr {
            return true;
        }
        assert(container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view()
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
    assert(container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view()
        .contains(container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view()
            .spec_index(0))) by {
        reveal(container_tree_fields_wf);
    };
    assert({
        &&& container_perms.dom().contains(container_perms.spec_index(child_ptr)
            .view_ghost().uppertree_seq.view().spec_index(0))
        &&& container_perms.spec_index(container_perms.spec_index(child_ptr).view_ghost()
            .uppertree_seq.view().spec_index(0)).view_rodata().view().depth == 0
    }) by {
        reveal(container_uppertree_seq_wf);
    };
    assert(container_perms.spec_index(child_ptr).view_ghost().uppertree_seq.view()
        .spec_index(0) == root_container) by {
        reveal(container_root_wf);
    };
    if root_container == a_ptr{
        return true;
    }
    return false;
}

}
