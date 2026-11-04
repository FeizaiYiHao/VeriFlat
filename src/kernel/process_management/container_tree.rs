use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::PointsTo;

verus! {
// Container tree ghost fields: `children` is the direct child list; `uppertree_seq` lists the ancestors from the root,
// indexed by depth; `subtree_set` holds all descendants; `parent_linkedlist_node` is the node in the parent's child list.

/// The container map's permissions are well formed, every container satisfies its own invariant, and its tree fields are well formed.
#[verifier::opaque]
pub open spec fn container_perms_wf(ctn_mp: ContainerLockedMap) -> bool {
    &&& ctn_mp.perms_wf()
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        #![trigger ctn_mp.spec_index(c)]
        ctn_mp.dom().contains(c) ==> ctn_mp.spec_index(c).inv()
    &&& container_tree_fields_wf(ctn_mp)
}

pub proof fn container_perms_wf_at(ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_perms_wf(ctn_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        ctn_mp.view().spec_index(ctn_ptr).is_init(),
        ctn_mp.view().spec_index(ctn_ptr).addr() == ctn_ptr,
        ctn_mp.spec_index(ctn_ptr).inv(),
        ctn_mp.spec_index(ctn_ptr).is_init(),
        ctn_mp.spec_index(ctn_ptr).view().inv(),
        ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().no_duplicates(),
        ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().len() == ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth,
        ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth <= MAX_CONTAINER_TREE_DEPTH,
        ctn_mp.spec_index(ctn_ptr).view().children.view().no_duplicates(),
        !ctn_mp.spec_index(ctn_ptr).view().children.view().contains(ctn_ptr),
{ reveal(container_perms_wf); reveal(container_tree_fields_wf); }

pub proof fn container_perms_wf_map(ctn_mp: ContainerLockedMap)
    requires container_perms_wf(ctn_mp)
    ensures ctn_mp.perms_wf()
{ reveal(container_perms_wf); }

/// Each container's child list and upper-tree sequence are duplicate-free, it is not its own child, and its depth is the
/// length of its upper-tree sequence and at most `MAX_CONTAINER_TREE_DEPTH`.
#[verifier::opaque]
pub open spec fn container_tree_fields_wf(ctn_mp: ContainerLockedMap) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view().children]
        #![trigger ctn_mp.spec_index(c).view_ghost().uppertree_seq]
        #![trigger ctn_mp.spec_index(c).view_ghost().subtree_set]
        #![trigger ctn_mp.spec_index(c).view_rodata().view().depth]
        ctn_mp.dom().contains(c) ==> {
            &&& ctn_mp.spec_index(c).view().children.view().no_duplicates()
            &&& ctn_mp.spec_index(c).view_ghost().uppertree_seq.view().no_duplicates()
            &&& !ctn_mp.spec_index(c).view().children.view().contains(c)
            &&& ctn_mp.spec_index(c).view_ghost().uppertree_seq.view().len() == ctn_mp.spec_index(c).view_rodata().view().depth
            &&& ctn_mp.spec_index(c).view_rodata().view().depth <= MAX_CONTAINER_TREE_DEPTH
        }
}

/// The root container is at depth 0 and keeps its own list node; every other container has a parent and a nonzero depth.
#[verifier::opaque]
pub open spec fn container_root_wf(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap) -> bool {
    &&& ctn_mp.dom().contains(root_container)
    &&& ctn_mp.spec_index(root_container).view_rodata().view().depth == 0
    // the root's list node is not linked into any child list
    &&& ctn_mp.spec_index(root_container).view().parent_linkedlist_node.is_init()
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c) && c != root_container ==> {
            &&& ctn_mp.spec_index(c).view_rodata().view().depth != 0
            // a non-root container's list node is linked into its parent's child list
            &&& !ctn_mp.spec_index(c).view().parent_linkedlist_node.is_init()
        }
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c) && c != root_container ==> ctn_mp.spec_index(c).view_rodata().view().parent is Some
}

/// A container's children are containers one level deeper that name it as parent; a container's parent lists it as a child.
#[verifier::opaque]
pub open spec fn container_children_parent_wf(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap) -> bool {
    // Container -> children.
    &&& forall|c: RwLockContainerPtr, child: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view().children.view().contains(child)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view().children.view().contains(child) ==> ctn_mp.dom().contains(child)
    &&& forall|c: RwLockContainerPtr, child: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view().children.view().contains(child)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view().children.view().contains(child) ==> {
            &&& ctn_mp.spec_index(child).view_rodata().view().parent.unwrap() == c
            &&& ctn_mp.spec_index(child).view_rodata().view().depth == ctn_mp.spec_index(c).view_rodata().view().depth + 1
        }
    // Container -> parent.
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view_rodata().view().parent is Some ==> {
            &&& ctn_mp.dom().contains(ctn_mp.spec_index(c).view_rodata().view().parent.unwrap())
            &&& ctn_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().parent.unwrap()).view().children.view().contains(c)
        }
}

pub proof fn container_root_wf_at(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr)
    requires container_root_wf(root_container, ctn_mp)
    ensures
        ctn_ptr == root_container ==> ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth == 0,
        ctn_mp.dom().contains(ctn_ptr) && ctn_ptr != root_container ==> {
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth != 0
            &&& !ctn_mp.spec_index(ctn_ptr).view().parent_linkedlist_node.is_init()
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent is Some
        },
{ reveal(container_root_wf); }

pub proof fn container_children_parent_wf_at(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr, child_ctn_ptr: RwLockContainerPtr)
    requires container_children_parent_wf(root_container, ctn_mp)
    ensures
        ctn_mp.dom().contains(ctn_ptr) && ctn_mp.spec_index(ctn_ptr).view().children.view().contains(child_ctn_ptr) ==> {
            &&& ctn_mp.dom().contains(child_ctn_ptr)
            &&& ctn_mp.spec_index(child_ctn_ptr).view_rodata().view().parent.unwrap() == ctn_ptr
            &&& ctn_mp.spec_index(child_ctn_ptr).view_rodata().view().depth == ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth + 1
        },
{ reveal(container_children_parent_wf); }

/// Container `ctn_ptr`'s duplicate-free child list holds only 2M-aligned container pointers, so its length is below the pointer bound.
pub proof fn container_children_len_bounded_at(root_container: RwLockContainerPtr, pg_arr: PageLockedArray, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_perms_wf(ctn_mp),
        container_children_parent_wf(root_container, ctn_mp),
        container_pages_wf(ctn_mp, pg_arr),
        ctn_mp.dom().contains(ctn_ptr),
    ensures ctn_mp.spec_index(ctn_ptr).view().children.view().len() <= NUM_PAGES * 4096,
{ container_perms_wf_at(ctn_mp, ctn_ptr); reveal(container_children_parent_wf); reveal(container_pages_wf); seq_unique_bounded_usize_len(ctn_mp.spec_index(ctn_ptr).view().children.view(), (NUM_PAGES * 4096) as usize); }

/// Every non-root container has a parent, and sits in its parent's child list at its own list node.
#[verifier::opaque]
pub open spec fn container_linkedlist_wf(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap) -> bool {
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_rodata().view().parent]
        ctn_mp.dom().contains(c) && c != root_container ==> ctn_mp.spec_index(c).view_rodata().view().parent is Some
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c)
            && c != root_container
            && ctn_mp.dom().contains(ctn_mp.spec_index(c).view_rodata().view().parent.unwrap())
            ==> {
                &&& ctn_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().parent.unwrap()).view().children.view().contains(c)
                &&& ctn_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().parent.unwrap()).view().children.map().dom().contains(ctn_mp.spec_index(c).view().parent_linkedlist_node.addr())
                &&& ctn_mp.spec_index(ctn_mp.spec_index(c).view_rodata().view().parent.unwrap()).view().children.map().spec_index(ctn_mp.spec_index(c).view().parent_linkedlist_node.addr()) == c
            }
}

/// A non-root container `ctn_ptr` whose parent is in the map sits in its parent's child list at its own list node.
pub proof fn container_linkedlist_wf_at(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_linkedlist_wf(root_container, ctn_mp),
        ctn_mp.dom().contains(ctn_ptr),
        ctn_ptr != root_container,
    ensures
        ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent is Some,
        ctn_mp.dom().contains(ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent.unwrap()) ==> {
            let parent = ctn_mp.spec_index(ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent.unwrap()).view();
            &&& parent.children.view().contains(ctn_ptr)
            &&& parent.children.map().dom().contains(ctn_mp.spec_index(ctn_ptr).view().parent_linkedlist_node.addr())
            &&& parent.children.map().spec_index(ctn_mp.spec_index(ctn_ptr).view().parent_linkedlist_node.addr()) == ctn_ptr
        },
{ reveal(container_linkedlist_wf); }

/// The last entry of a non-root container's upper-tree sequence is its parent.
#[verifier::opaque]
pub open spec fn container_uppertree_seq_parent_wf(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap) -> bool {
    forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c) && c != root_container
            ==> ctn_mp.spec_index(c).view_ghost().uppertree_seq.view().spec_index(ctn_mp.spec_index(c).view_rodata().view().depth - 1) == ctn_mp.spec_index(c).view_rodata().view().parent.unwrap()
}

/// The last entry of non-root container `ctn_ptr`'s upper-tree sequence is its parent.
pub proof fn container_uppertree_seq_parent_wf_at(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_uppertree_seq_parent_wf(root_container, ctn_mp),
        ctn_mp.dom().contains(ctn_ptr),
        ctn_ptr != root_container,
    ensures
        ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().spec_index(ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth - 1) == ctn_mp.spec_index(ctn_ptr).view_rodata().view().parent.unwrap(),
{ reveal(container_uppertree_seq_parent_wf); }

/// A member `sub` of the subtree of container `c` lists `c` at `c`'s depth in its upper-tree sequence.
#[verifier::opaque]
pub open spec fn container_subtree_set_wf(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap) -> bool {
    forall|c: RwLockContainerPtr, sub: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_ghost().subtree_set.view().contains(sub)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view_ghost().subtree_set.view().contains(sub) ==> {
            &&& ctn_mp.dom().contains(sub)
            &&& ctn_mp.spec_index(sub).view_ghost().uppertree_seq.view().len() > ctn_mp.spec_index(c).view_rodata().view().depth
            &&& ctn_mp.spec_index(sub).view_ghost().uppertree_seq.view().spec_index(ctn_mp.spec_index(c).view_rodata().view().depth as int) == c
        }
}

/// A member `sub_ctn_ptr` of the subtree of container `ctn_ptr` lists `ctn_ptr` at `ctn_ptr`'s depth in its upper tree.
pub proof fn container_subtree_set_wf_at(rt_ctn: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr, sub_ctn_ptr: RwLockContainerPtr)
    requires
        container_subtree_set_wf(rt_ctn, ctn_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        ctn_mp.spec_index(ctn_ptr).view_ghost().subtree_set.view().contains(sub_ctn_ptr) ==> {
            let ro = ctn_mp.spec_index(ctn_ptr).view_rodata().view();
            &&& ctn_mp.dom().contains(sub_ctn_ptr)
            &&& ctn_mp.spec_index(sub_ctn_ptr).view_ghost().uppertree_seq.view().len() > ro.depth
            &&& ctn_mp.spec_index(sub_ctn_ptr).view_ghost().uppertree_seq.view().spec_index(ro.depth as int) == ctn_ptr
        },
{ reveal(container_subtree_set_wf); }

/// An ancestor `u` of container `c` is a container at its own depth in `c`'s upper-tree sequence, whose subtree holds `c`.
#[verifier::opaque]
pub open spec fn container_uppertree_seq_wf(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap) -> bool {
    forall|c: RwLockContainerPtr, u: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_ghost().uppertree_seq.view().contains(u)]
        ctn_mp.dom().contains(c) && ctn_mp.spec_index(c).view_ghost().uppertree_seq.view().contains(u) ==> {
            &&& ctn_mp.dom().contains(u)
            &&& ctn_mp.spec_index(c).view_ghost().uppertree_seq.view().spec_index(ctn_mp.spec_index(u).view_rodata().view().depth as int) == u
            &&& ctn_mp.spec_index(u).view_rodata().view().depth == ctn_mp.spec_index(c).view_ghost().uppertree_seq.view().index_of(u)
            &&& ctn_mp.spec_index(u).view_ghost().subtree_set.view().contains(c)
            &&& ctn_mp.spec_index(u).view_ghost().uppertree_seq.view() =~= ctn_mp.spec_index(c).view_ghost().uppertree_seq.view().subrange(0, ctn_mp.spec_index(u).view_rodata().view().depth as int)
        }
}

/// Ancestor `upper_ctn_ptr` of container `ctn_ptr` is a container at its own depth in `ctn_ptr`'s upper-tree sequence, whose subtree holds `ctn_ptr`.
pub proof fn container_uppertree_seq_wf_at(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr, upper_ctn_ptr: RwLockContainerPtr)
    requires
        container_uppertree_seq_wf(root_container, ctn_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures
        ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().contains(upper_ctn_ptr) ==> {
            &&& ctn_mp.dom().contains(upper_ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().spec_index(ctn_mp.spec_index(upper_ctn_ptr).view_rodata().view().depth as int) == upper_ctn_ptr
            &&& ctn_mp.spec_index(upper_ctn_ptr).view_rodata().view().depth == ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().index_of(upper_ctn_ptr)
            &&& ctn_mp.spec_index(upper_ctn_ptr).view_ghost().subtree_set.view().contains(ctn_ptr)
            &&& ctn_mp.spec_index(upper_ctn_ptr).view_ghost().uppertree_seq.view() =~= ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().subrange(0, ctn_mp.spec_index(upper_ctn_ptr).view_rodata().view().depth as int)
        },
{ reveal(container_uppertree_seq_wf); }

pub proof fn container_uppertree_seq_wf_implies_ancestors_in_dom(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_uppertree_seq_wf(root_container, ctn_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures forall|u: RwLockContainerPtr| #[trigger] ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().contains(u) ==> ctn_mp.dom().contains(u),
{ reveal(container_uppertree_seq_wf); }

pub proof fn container_uppertree_seq_not_self(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_perms_wf(ctn_mp),
        container_uppertree_seq_wf(root_container, ctn_mp),
        ctn_mp.dom().contains(ctn_ptr),
    ensures !ctn_mp.spec_index(ctn_ptr).view_ghost().uppertree_seq.view().contains(ctn_ptr),
{ reveal(container_perms_wf); reveal(container_tree_fields_wf); reveal(container_uppertree_seq_wf); reveal(Seq::contains); }

/// Container `sub` is in the subtree of container `c` iff `c` is in `sub`'s upper-tree sequence.
#[verifier::opaque]
pub open spec fn container_subtree_uppertree_agree_wf(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap) -> bool {
    forall|c: RwLockContainerPtr, sub: RwLockContainerPtr|
        #![trigger ctn_mp.spec_index(c).view_ghost().subtree_set.view().contains(sub), ctn_mp.spec_index(sub).view_ghost().uppertree_seq.view().contains(c)]
        ctn_mp.dom().contains(c) && ctn_mp.dom().contains(sub)
            ==> ctn_mp.spec_index(c).view_ghost().subtree_set.view().contains(sub) == ctn_mp.spec_index(sub).view_ghost().uppertree_seq.view().contains(c)
}

pub proof fn container_subtree_uppertree_agree_wf_at(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap, ctn_ptr: RwLockContainerPtr, sub_ctn_ptr: RwLockContainerPtr)
    requires
        container_subtree_uppertree_agree_wf(root_container, ctn_mp),
        ctn_mp.dom().contains(ctn_ptr),
        ctn_mp.dom().contains(sub_ctn_ptr),
    ensures
        ctn_mp.spec_index(ctn_ptr).view_ghost().subtree_set.view().contains(sub_ctn_ptr) == ctn_mp.spec_index(sub_ctn_ptr).view_ghost().uppertree_seq.view().contains(ctn_ptr),
{ reveal(container_subtree_uppertree_agree_wf); }

/// The container tree rooted at `root_container` is well formed.
pub open spec fn container_tree_wf(root_container: RwLockContainerPtr, ctn_mp: ContainerLockedMap) -> bool {
    &&& container_root_wf(root_container, ctn_mp)
    &&& container_children_parent_wf(root_container, ctn_mp)
    &&& container_linkedlist_wf(root_container, ctn_mp)
    &&& container_uppertree_seq_parent_wf(root_container, ctn_mp)
    &&& container_subtree_set_wf(root_container, ctn_mp)
    &&& container_uppertree_seq_wf(root_container, ctn_mp)
    &&& container_subtree_uppertree_agree_wf(root_container, ctn_mp)
}

/// If the domain and every container's children, parent list node, rodata, upper-tree sequence, and subtree set are
/// unchanged, `container_tree_wf` is preserved.
pub proof fn container_no_change_to_tree_fields_imply_wf(root_container: RwLockContainerPtr, old_ctn_mp: ContainerLockedMap, new_ctn_mp: ContainerLockedMap)
    requires
        container_tree_wf(root_container, old_ctn_mp),
        old_ctn_mp.dom() =~= new_ctn_mp.dom(),
        forall|c: RwLockContainerPtr|
            #![trigger new_ctn_mp.spec_index(c)]
            old_ctn_mp.dom().contains(c)
                ==> new_ctn_mp.spec_index(c).view().children == old_ctn_mp.spec_index(c).view().children
                && new_ctn_mp.spec_index(c).view().parent_linkedlist_node == old_ctn_mp.spec_index(c).view().parent_linkedlist_node
                && new_ctn_mp.spec_index(c).view_rodata() == old_ctn_mp.spec_index(c).view_rodata()
                && new_ctn_mp.spec_index(c).view_ghost().uppertree_seq == old_ctn_mp.spec_index(c).view_ghost().uppertree_seq
                && new_ctn_mp.spec_index(c).view_ghost().subtree_set == old_ctn_mp.spec_index(c).view_ghost().subtree_set,
    ensures
        container_tree_wf(root_container, new_ctn_mp),
{
    reveal(container_root_wf); reveal(container_children_parent_wf); reveal(container_linkedlist_wf); reveal(container_uppertree_seq_parent_wf);
    reveal(container_subtree_set_wf); reveal(container_uppertree_seq_wf); reveal(container_subtree_uppertree_agree_wf);
}

pub proof fn container_insert_child_into_ancestor_subtree_sets(tracked ctn_mp: &mut ContainerLockedMap, ancestors: Seq<RwLockContainerPtr>, child_ptr: RwLockContainerPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId)
    requires
        old(ctn_mp).perms_wf(),
        ancestors.to_set().subset_of(old(ctn_mp).dom()),
        ancestors.no_duplicates(),
        !ancestors.to_set().contains(child_ptr),
        old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        final(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().subtree_set]
            ancestors.to_set().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().subtree_set == Ghost(old(ctn_mp).spec_index(c).view_ghost().subtree_set.view().insert(child_ptr)),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().subtree_set]
            old(ctn_mp).dom().contains(c) && !ancestors.to_set().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().subtree_set == old(ctn_mp).spec_index(c).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view() == old(ctn_mp).spec_index(c).view(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_rodata()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_rodata() == old(ctn_mp).spec_index(c).view_rodata(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().uppertree_seq]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().uppertree_seq == old(ctn_mp).spec_index(c).view_ghost().uppertree_seq,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().owned_threads]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().owned_threads == old(ctn_mp).spec_index(c).view_ghost().owned_threads,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().owned_processes]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().owned_processes == old(ctn_mp).spec_index(c).view_ghost().owned_processes,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads == old(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().owned_endpoints]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().owned_endpoints == old(ctn_mp).spec_index(c).view_ghost().owned_endpoints,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).locking_thread()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).locking_thread() == old(ctn_mp).spec_index(c).locking_thread(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).being_killed()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).being_killed() == old(ctn_mp).spec_index(c).being_killed(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).killer_info()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).killer_info() == old(ctn_mp).spec_index(c).killer_info(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).control()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).control() == old(ctn_mp).spec_index(c).control(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().retire_ready]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().retire_ready == old(ctn_mp).spec_index(c).view_ghost().retire_ready,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).is_init()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).is_init() == old(ctn_mp).spec_index(c).is_init(),
    decreases ancestors.len(),
{
    if ancestors.len() > 0 {
        let c0 = ancestors.spec_index(0);
        assert(ancestors.to_set().contains(c0)) by { ancestors.to_set_ensures(); };
        ctn_mp.update_ghost(c0, ContainerGhost { uppertree_seq: ctn_mp.spec_index(c0).view_ghost().uppertree_seq,
            subtree_set: Ghost(ctn_mp.spec_index(c0).view_ghost().subtree_set.view().insert(child_ptr)), owned_processes: ctn_mp.spec_index(c0).view_ghost().owned_processes,
            owned_threads: ctn_mp.spec_index(c0).view_ghost().owned_threads, owned_indirect_threads: ctn_mp.spec_index(c0).view_ghost().owned_indirect_threads,
            owned_endpoints: ctn_mp.spec_index(c0).view_ghost().owned_endpoints, retire_ready: ctn_mp.spec_index(c0).view_ghost().retire_ready });
        assert(ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(ancestors.drop_first().to_set().subset_of(ctn_mp.dom())) by { ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures(); };
        container_insert_child_into_ancestor_subtree_sets(ctn_mp, ancestors.drop_first(), child_ptr, held_locks, thread_id);
        assert({
            &&& !ancestors.drop_first().to_set().contains(c0)
            &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(c0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    }
}

/// Removes `child_ptr` from the ghost subtree set of every container in `ancestors`; nothing else changes.
pub proof fn container_remove_child_from_ancestor_subtree_sets(tracked ctn_mp: &mut ContainerLockedMap, ancestors: Seq<RwLockContainerPtr>, child_ptr: RwLockContainerPtr, held_locks: Map<RwLockContainerPtr, TypedHeldLock>, thread_id: LockThreadId)
    requires
        old(ctn_mp).perms_wf(),
        ancestors.to_set().subset_of(old(ctn_mp).dom()),
        ancestors.no_duplicates(),
        old(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
    ensures
        final(ctn_mp).perms_wf(),
        final(ctn_mp).dom() == old(ctn_mp).dom(),
        final(ctn_mp).typed_lock_map_aligned(held_locks, thread_id),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().subtree_set]
            ancestors.to_set().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().subtree_set == Ghost(old(ctn_mp).spec_index(c).view_ghost().subtree_set.view().remove(child_ptr)),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().subtree_set]
            old(ctn_mp).dom().contains(c) && !ancestors.to_set().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().subtree_set == old(ctn_mp).spec_index(c).view_ghost().subtree_set,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view() == old(ctn_mp).spec_index(c).view(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_rodata()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_rodata() == old(ctn_mp).spec_index(c).view_rodata(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().uppertree_seq]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().uppertree_seq == old(ctn_mp).spec_index(c).view_ghost().uppertree_seq,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().owned_threads]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().owned_threads == old(ctn_mp).spec_index(c).view_ghost().owned_threads,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().owned_processes]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().owned_processes == old(ctn_mp).spec_index(c).view_ghost().owned_processes,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads == old(ctn_mp).spec_index(c).view_ghost().owned_indirect_threads,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().owned_endpoints]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().owned_endpoints == old(ctn_mp).spec_index(c).view_ghost().owned_endpoints,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).locking_thread()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).locking_thread() == old(ctn_mp).spec_index(c).locking_thread(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).being_killed()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).being_killed() == old(ctn_mp).spec_index(c).being_killed(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).killer_info()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).killer_info() == old(ctn_mp).spec_index(c).killer_info(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).control()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).control() == old(ctn_mp).spec_index(c).control(),
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).view_ghost().retire_ready]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).view_ghost().retire_ready == old(ctn_mp).spec_index(c).view_ghost().retire_ready,
        forall|c: RwLockContainerPtr| #![trigger final(ctn_mp).spec_index(c).is_init()]
            old(ctn_mp).dom().contains(c) ==> final(ctn_mp).spec_index(c).is_init() == old(ctn_mp).spec_index(c).is_init(),
    decreases ancestors.len(),
{
    if ancestors.len() > 0 {
        let c0 = ancestors.spec_index(0);
        assert(ancestors.to_set().contains(c0)) by { ancestors.to_set_ensures(); };
        ctn_mp.update_ghost(c0, ContainerGhost { uppertree_seq: ctn_mp.spec_index(c0).view_ghost().uppertree_seq,
            subtree_set: Ghost(ctn_mp.spec_index(c0).view_ghost().subtree_set.view().remove(child_ptr)), owned_processes: ctn_mp.spec_index(c0).view_ghost().owned_processes,
            owned_threads: ctn_mp.spec_index(c0).view_ghost().owned_threads, owned_indirect_threads: ctn_mp.spec_index(c0).view_ghost().owned_indirect_threads,
            owned_endpoints: ctn_mp.spec_index(c0).view_ghost().owned_endpoints, retire_ready: ctn_mp.spec_index(c0).view_ghost().retire_ready });
        assert(ctn_mp.typed_lock_map_aligned(held_locks, thread_id)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(ancestors.drop_first().to_set().subset_of(ctn_mp.dom())) by { ancestors.to_set_ensures(); ancestors.drop_first().to_set_ensures(); };
        container_remove_child_from_ancestor_subtree_sets(ctn_mp, ancestors.drop_first(), child_ptr, held_locks, thread_id);
        assert({
            &&& !ancestors.drop_first().to_set().contains(c0)
            &&& ancestors.to_set() =~= ancestors.drop_first().to_set().insert(c0)
        }) by { broadcast use vstd::seq_lib::lemma_seq_subrange_elements; };
    }
}

#[verifier::loop_isolation(false)]
pub fn container_tree_check_is_ancestor(root_container: RwLockContainerPtr, ctn_mp: &ContainerLockedMap, a_ptr: RwLockContainerPtr, child_ptr: RwLockContainerPtr) -> (ret: bool)
    requires
        container_perms_wf(*ctn_mp),
        container_tree_wf(root_container, *ctn_mp),
        ctn_mp.view().dom().contains(a_ptr),
        ctn_mp.view().dom().contains(child_ptr),
        a_ptr != child_ptr,
    ensures
        ret == ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(a_ptr),
        ret == ctn_mp.spec_index(a_ptr).view_ghost().subtree_set.view().contains(child_ptr),
{
    hide(Seq::no_duplicates);
    assert({
        &&& ctn_mp.view().spec_index(child_ptr).is_init()
        &&& ctn_mp.view().spec_index(child_ptr).addr() == child_ptr
        &&& ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().contains(a_ptr) == ctn_mp.spec_index(a_ptr).view_ghost().subtree_set.view().contains(child_ptr)
    }) by { container_perms_wf_at(*ctn_mp, child_ptr); container_subtree_uppertree_agree_wf_at(root_container, *ctn_mp, a_ptr, child_ptr); };
    let current_child_ro = ctn_mp.borrow_rodata(child_ptr);
    let depth = current_child_ro.borrow().depth;
    assert({
        &&& ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().len() == depth
        &&& ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().no_duplicates()
    }) by { container_perms_wf_at(*ctn_mp, child_ptr); };
    assert((depth == 0) == (child_ptr == root_container)) by { container_root_wf_at(root_container, *ctn_mp, child_ptr); };
    if depth == 0 {
        return false;
    }
    let mut current_c_ptr = child_ptr;
    for i in 0..(depth-1)
        invariant
            ctn_mp.dom().contains(current_c_ptr),
            ctn_mp.spec_index(current_c_ptr).view_rodata().view().depth == depth - i,
            i == 0 ==> current_c_ptr == child_ptr,
            i != 0 ==> current_c_ptr == ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i),
            forall|j:int| depth - i <= j < depth ==> ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(j) != a_ptr
    {
        assert({
            &&& ctn_mp.view().spec_index(current_c_ptr).is_init()
            &&& ctn_mp.view().spec_index(current_c_ptr).addr() == current_c_ptr
        }) by { container_perms_wf_at(*ctn_mp, current_c_ptr); };
        let current_ro = ctn_mp.borrow_rodata(current_c_ptr);
        assert({
            &&& current_ro.view().parent is Some
            &&& current_c_ptr != root_container
        }) by { container_root_wf_at(root_container, *ctn_mp, current_c_ptr); };
        let next_parent_ptr = current_ro.borrow().parent.unwrap();
        if i == 0 {
            assert(next_parent_ptr == ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i - 1)) by { container_uppertree_seq_parent_wf_at(root_container, *ctn_mp, current_c_ptr); };
        } else {
            assert(ctn_mp.spec_index(current_c_ptr).view_ghost().uppertree_seq.view() == ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().subrange(0, depth - i)) by {
                ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().lemma_index_contains(depth - i); container_uppertree_seq_wf_at(root_container, *ctn_mp, child_ptr, current_c_ptr);
            };
            assert(next_parent_ptr == ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(depth - i - 1)) by { container_uppertree_seq_parent_wf_at(root_container, *ctn_mp, current_c_ptr); };
        }
        if next_parent_ptr == a_ptr {
            return true;
        }
        assert({
            &&& ctn_mp.dom().contains(next_parent_ptr)
            &&& ctn_mp.spec_index(next_parent_ptr).view_rodata().view().depth == depth - i - 1
        }) by {
            reveal(Seq::no_duplicates); ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().lemma_index_contains(depth - i - 1);
            container_uppertree_seq_wf_at(root_container, *ctn_mp, child_ptr, next_parent_ptr);
        };
        current_c_ptr = next_parent_ptr;
    }
    assert({
        &&& ctn_mp.dom().contains(ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0))
        &&& ctn_mp.spec_index(ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0)).view_rodata().view().depth == 0
    }) by {
        reveal(Seq::no_duplicates); ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().lemma_index_contains(0);
        container_uppertree_seq_wf_at(root_container, *ctn_mp, child_ptr, ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0));
    };
    assert(ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0) == root_container) by {
        container_root_wf_at(root_container, *ctn_mp, ctn_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view().spec_index(0));
    };
    if root_container == a_ptr {
        return true;
    }
    return false;
}
}
