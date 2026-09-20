use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
pub(super) fn consume_new_container_thread_staging(
    threads: &mut ThreadLockedMap, current_thread_ptr: RwLockThreadPtr, thread_page: PagePtr, funding_page_count: usize,
    Ghost(consumed_4k_pages): Ghost<Set<PagePtr>>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(threads).perms_wf(),
        old(threads).dom().contains(current_thread_ptr),
        old(threads).spec_index(current_thread_ptr).is_init(),
        old(threads).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id(),),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), current_thread_ptr, TypedLockMode::Write,),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == lctx.thread_id(),
        current_thread_lock_perm.lock_id() == old(threads).spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(threads).spec_index(current_thread_ptr).view().temp_alloc_cache_4k.view() == consumed_4k_pages.insert(thread_page),
        !consumed_4k_pages.contains(thread_page),
        consumed_4k_pages.len() == 8 + funding_page_count,
        old(threads).spec_index(current_thread_ptr).view().quota_4k >= 8,
        funding_page_count < old(threads).spec_index(current_thread_ptr).view().quota_4k - 8,
        old(threads).spec_index(current_thread_ptr).view().temp_alloc_cache_2m.view().len() == 2,
        old(threads).spec_index(current_thread_ptr).view().quota_2m >= 2,
    ensures
        thread_perms_wf(*old(threads)) ==> thread_perms_wf(*final(threads)),
        final(threads).unchanged_except(old(threads), current_thread_ptr),
        final(threads).typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id(),),
        final(threads).spec_index(current_thread_ptr).locking_thread() == old(threads).spec_index(current_thread_ptr).locking_thread(),
        final(threads).spec_index(current_thread_ptr).being_killed() == old(threads).spec_index(current_thread_ptr).being_killed(),
        thread_quota_4k_fields_unchanged(*old(threads), *final(threads)),
        thread_quota_2m_fields_unchanged(*old(threads), *final(threads)),
        thread_quota_1g_fields_unchanged(*old(threads), *final(threads)),
        final(threads).spec_index(current_thread_ptr).view() == (Thread {
            temp_alloc_cache_4k: Ghost(set![thread_page]),
            temp_alloc_cache_2m: Ghost(Set::empty()),
            quota_4k: (old(threads).spec_index(current_thread_ptr).view().quota_4k as int - 8 - funding_page_count as int) as usize,
            quota_2m: (old(threads).spec_index(current_thread_ptr).view().quota_2m as int - 2) as usize,
            ..old(threads).spec_index(current_thread_ptr).view()
        }),
{
    let thread = threads.borrow_mut_typed(
        current_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), Tracked(current_thread_lock_perm),
    );
    thread.temp_alloc_cache_4k = Ghost(Set::empty().insert(thread_page));
    thread.temp_alloc_cache_2m = Ghost(Set::empty());
    thread.quota_4k = thread.quota_4k - 8 - funding_page_count;
    thread.quota_2m = thread.quota_2m - 2;
    proof {
        if thread_perms_wf(*old(threads)) {
            assert(thread_perms_wf(*threads)) by { reveal(LockedMap::unchanged_except); reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); reveal(thread_temp_alloc_empty_unless_wlocked); };
        }
        assert(threads.typed_lock_map_aligned(lctx.thread_lock_map(), lctx.thread_id(),)) by { reveal(LockedMap::typed_lock_map_aligned); };
        assert(thread_quota_4k_fields_unchanged(*old(threads), *threads)) by {
            vstd::set::lemma_set_insert_len(consumed_4k_pages, thread_page,); reveal(thread_quota_4k_fields_unchanged);
            reveal(thread_effective_quota_4k); reveal(LockedMap::unchanged_except);
        };
        assert(thread_quota_2m_fields_unchanged(*old(threads), *threads)) by { reveal(thread_quota_2m_fields_unchanged); reveal(thread_effective_quota_2m); reveal(LockedMap::unchanged_except); };
        assert(thread_quota_1g_fields_unchanged(*old(threads), *threads)) by { reveal(thread_quota_1g_fields_unchanged); reveal(thread_effective_quota_1g); reveal(LockedMap::unchanged_except); };
    }
}

pub(super) fn link_new_container_into_tree(
    containers: &mut ContainerLockedMap, root_container: RwLockContainerPtr, parent_container_ptr: RwLockContainerPtr,
    child_container_ptr: RwLockContainerPtr, child_process_ptr: RwLockProcessPtr, child_scheduler_ptr: RwLockSchedulerPtr,
    child_pcid_allocator_ptr: RwLockPcidAllocatorPtr, child_cpu_set_ptr: RwLockCpuSetPtr, child_allocator_4k_ptr: RwLockPageAllocatorPtr,
    child_allocator_2m_ptr: RwLockPageAllocatorPtr, child_allocator_1g_ptr: RwLockPageAllocatorPtr, child_depth: usize,
    thread_page: PagePtr, Ghost(child_uppers): Ghost<Seq<RwLockContainerPtr>>, Ghost(moved_pages): Ghost<Set<PagePtr>>,
    Ghost(base_containers): Ghost<ContainerLockedMap>, Ghost(base_pages): Ghost<PageLockedArray>, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(parent_container_lock_perm): Tracked<&LockPerm>, Tracked(child_container_lock_perm): Tracked<&LockPerm>,
)
    requires
        container_perms_wf(base_containers),
        container_tree_wf(root_container, base_containers),
        container_pages_wf(base_pages, base_containers),
        base_containers.dom().contains(parent_container_ptr),
        !base_containers.dom().contains(child_container_ptr),
        base_containers.spec_index(parent_container_ptr).view_rodata().view().depth < MAX_CONTAINER_TREE_DEPTH,
        old(containers).perms_wf(),
        old(containers).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),),
        old(containers).dom() == base_containers.dom().insert(child_container_ptr),
        forall|container_ptr: RwLockContainerPtr|
            #![trigger old(containers).spec_index(container_ptr)]
            base_containers.dom().contains(container_ptr) ==> old(containers).spec_index(container_ptr) == base_containers.spec_index(container_ptr),
        old(containers).spec_index(child_container_ptr).is_init(),
        old(containers).spec_index(child_container_ptr).inv(),
        !old(containers).spec_index(child_container_ptr).being_killed(),
        old(containers).spec_index(child_container_ptr).view().parent_linkedlist_node.is_init(),
        old(containers).spec_index(child_container_ptr).view().children.view() == Seq::<RwLockContainerPtr>::empty(),
        old(containers).spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        old(containers).spec_index(child_container_ptr).view_rodata().view().depth == child_depth,
        old(containers).spec_index(child_container_ptr).view_rodata().view().scheduler == child_scheduler_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().pcid_allocator == child_pcid_allocator_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().cpu_set == child_cpu_set_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_2m == child_allocator_2m_ptr,
        old(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_1g == child_allocator_1g_ptr,
        old(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq.view() == child_uppers,
        old(containers).spec_index(child_container_ptr).view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty(),
        old(containers).spec_index(child_container_ptr).view().owned_pages.view() == moved_pages,
        old(containers).spec_index(child_container_ptr).view().root_process == child_process_ptr,
        old(containers).spec_index(child_container_ptr).view().owned_processes.view() == set![child_process_ptr],
        child_depth == base_containers.spec_index(parent_container_ptr).view_rodata().view().depth + 1,
        child_uppers == base_containers.spec_index(parent_container_ptr).view_ghost().uppertree_seq.view().push(parent_container_ptr),
        child_uppers.no_duplicates(),
        child_uppers.to_set().subset_of(base_containers.dom()),
        !child_uppers.to_set().contains(child_container_ptr),
        moved_pages.subset_of(base_containers.spec_index(parent_container_ptr).view().owned_pages.view()),
        !moved_pages.contains(thread_page),
        base_containers.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        typed_lock_map_contains_mode(lctx.container_lock_map(), parent_container_ptr, TypedLockMode::Write,),
        typed_lock_map_contains_mode(lctx.container_lock_map(), child_container_ptr, TypedLockMode::Write,),
        parent_container_lock_perm.state() is WriteLock,
        parent_container_lock_perm.thread_id() == lctx.thread_id(),
        parent_container_lock_perm.lock_id() == old(containers).spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.state() is WriteLock,
        child_container_lock_perm.thread_id() == lctx.thread_id(),
        child_container_lock_perm.lock_id() == old(containers).spec_index(child_container_ptr).locking_thread()->Write_lock_id,
    ensures
        final(containers).perms_wf(),
        final(containers).dom() == old(containers).dom(),
        final(containers).typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),),
        container_perms_wf(*final(containers)),
        container_add_child_ensures(root_container, base_containers, *final(containers), parent_container_ptr, child_container_ptr,),
        final(containers).spec_index(parent_container_ptr).view().owned_pages.view() == base_containers.spec_index(parent_container_ptr).view().owned_pages.view().difference(moved_pages),
        final(containers).spec_index(parent_container_ptr).view() == (Container {
            children: final(containers).spec_index(parent_container_ptr).view().children,
            owned_pages: final(containers).spec_index(parent_container_ptr).view().owned_pages,
            ..base_containers.spec_index(parent_container_ptr).view()
        }),
        final(containers).spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page),
        final(containers).spec_index(child_container_ptr).view().owned_pages.view() == moved_pages,
        !final(containers).spec_index(child_container_ptr).being_killed(),
        final(containers).spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr),
        final(containers).spec_index(child_container_ptr).view_rodata().view().depth == child_depth,
        final(containers).spec_index(child_container_ptr).view_rodata().view().scheduler == child_scheduler_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().pcid_allocator == child_pcid_allocator_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().cpu_set == child_cpu_set_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_4k == child_allocator_4k_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_2m == child_allocator_2m_ptr,
        final(containers).spec_index(child_container_ptr).view_rodata().view().allocator_ptr_1g == child_allocator_1g_ptr,
        final(containers).spec_index(child_container_ptr).view().root_process == child_process_ptr,
        final(containers).spec_index(child_container_ptr).view().owned_processes.view() == set![child_process_ptr],
        final(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq == old(containers).spec_index(child_container_ptr).view_ghost().uppertree_seq,
        final(containers).spec_index(child_container_ptr).view().owned_endpoints == old(containers).spec_index(child_container_ptr).view().owned_endpoints,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_threads == old(containers).spec_index(child_container_ptr).view_ghost().owned_threads,
        final(containers).spec_index(child_container_ptr).view_ghost().owned_indirect_threads == old(containers).spec_index(child_container_ptr).view_ghost().owned_indirect_threads,
        parent_container_lock_perm.lock_id() == final(containers).spec_index(parent_container_ptr).locking_thread()->Write_lock_id,
        child_container_lock_perm.lock_id() == final(containers).spec_index(child_container_ptr).locking_thread()->Write_lock_id,
        forall|container_ptr: RwLockContainerPtr|
            #![trigger final(containers).spec_index(container_ptr)]
            base_containers.dom().contains(container_ptr) ==> {
                &&& final(containers).spec_index(container_ptr).is_init() == base_containers.spec_index(container_ptr).is_init()
                &&& final(containers).spec_index(container_ptr).view_rodata() == base_containers.spec_index(container_ptr).view_rodata()
                &&& final(containers).spec_index(container_ptr).locking_thread() == base_containers.spec_index(container_ptr).locking_thread()
                &&& final(containers).spec_index(container_ptr).being_killed() == base_containers.spec_index(container_ptr).being_killed()
                &&& final(containers).spec_index(container_ptr).view().parent_linkedlist_node == base_containers.spec_index(container_ptr).view().parent_linkedlist_node
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_threads == base_containers.spec_index(container_ptr).view_ghost().owned_threads
                &&& final(containers).spec_index(container_ptr).view_ghost().owned_indirect_threads == base_containers.spec_index(container_ptr).view_ghost().owned_indirect_threads
                &&& container_ptr != parent_container_ptr ==> final(containers).spec_index(container_ptr).view() == base_containers.spec_index(container_ptr).view()
            },
{
    proof {
        assert(old(containers).spec_index(parent_container_ptr).is_init()) by { reveal(container_perms_wf); };
    }
    let (node_addr, node_perm) = {
        let child = containers.borrow_mut_typed(
            child_container_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(child_container_lock_perm),
        );
        let (node_addr, mut node_perm) = child.parent_linkedlist_node.take();
        node_update_value(node_addr, &mut node_perm, child_container_ptr);
        (node_addr, node_perm)
    };
    proof {
        assert(containers.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    let parent = containers.borrow_mut_typed(
        parent_container_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(parent_container_lock_perm),
    );
    proof {
        assert(parent.inv()) by { reveal(container_perms_wf); reveal(containers_inv); };
        assert(parent.children.wf()) by { reveal(Container::wf); };
        let ghost original_children = base_containers.spec_index(parent_container_ptr).view().children.view();
        assert(parent.children.view() == original_children);
        assert(original_children.no_duplicates()) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
        let ghost child_indices = original_children.map_values(|child_ptr: PagePtr| page_ptr2page_index(child_ptr));
        assert(child_indices.len() == original_children.len()) by { reveal(Seq::map_values); };
        assert(child_indices.no_duplicates()) by {
            reveal(Seq::no_duplicates);
            assert forall|i: int, j: int|
                0 <= i < j < child_indices.len() implies
                    child_indices.spec_index(i) != child_indices.spec_index(j)
            by {
                assert(original_children.spec_index(i) != original_children.spec_index(j)) by { reveal(Seq::no_duplicates); };
                let left_child = original_children.spec_index(i);
                let right_child = original_children.spec_index(j);
                assert(original_children.contains(left_child)) by { reveal(Seq::contains); };
                assert(original_children.contains(right_child)) by { reveal(Seq::contains); };
                assert(base_containers.dom().contains(left_child)) by { reveal(container_children_parent_wf); };
                assert(base_containers.dom().contains(right_child)) by { reveal(container_children_parent_wf); };
                assert(page_ptr_2m_valid(left_child)) by { reveal(container_pages_wf); };
                assert(page_ptr_2m_valid(right_child)) by { reveal(container_pages_wf); };
                assert(page_ptr_valid(left_child)) by { reveal(page_ptr_valid); reveal(page_ptr_2m_valid); };
                assert(page_ptr_valid(right_child)) by { reveal(page_ptr_valid); reveal(page_ptr_2m_valid); };
                page_ptr2page_index_injective();
                reveal(Seq::map_values);
            };
        };
        assert(child_indices.len() <= NUM_PAGES) by {
            assert forall|child_index: usize|
                #![trigger child_indices.contains(child_index)]
                child_indices.contains(child_index) implies
                    child_index < NUM_PAGES
            by {
                child_indices.index_of_first_ensures(child_index);
                let i = child_indices.index_of_first(child_index).unwrap();
                reveal(Seq::map_values);
                let child_ptr = original_children.spec_index(i);
                assert(original_children.contains(child_ptr)) by { reveal(Seq::contains); };
                assert(base_containers.dom().contains(child_ptr)) by { reveal(container_children_parent_wf); };
                assert(page_ptr_2m_valid(child_ptr)) by { reveal(container_pages_wf); };
                assert(page_ptr_valid(child_ptr)) by { reveal(page_ptr_valid); reveal(page_ptr_2m_valid); };
                page_ptr_valid_imply_page_index_valid();
            };
            seq_unique_bounded_usize_len(child_indices, NUM_PAGES,);
        };
        assert(parent.children.length == parent.children.view().len()) by { reveal(LinkedList::wf_value_list); };
        assert(NUM_PAGES < usize::MAX) by (compute);
        assert(!original_children.contains(child_container_ptr)) by {
            if original_children.contains(child_container_ptr) {
                assert(base_containers.dom().contains(child_container_ptr)) by { reveal(container_children_parent_wf); };
            }
        };
    }
    parent.children.push_tail(node_addr, node_perm);
    proof {
        container_insert_child_into_ancestor_subtree_sets(containers, child_uppers, child_container_ptr, lctx.container_lock_map(), lctx.thread_id(),);
        assert(containers.typed_lock_map_aligned(lctx.container_lock_map(), lctx.thread_id(),)) by { reveal(LockedMap::typed_lock_map_aligned); };
    }
    {
        let parent = containers.borrow_mut_typed(
            parent_container_ptr, Ghost(lctx.container_lock_map()), Tracked(lctx), Tracked(parent_container_lock_perm),
        );
        parent.owned_pages = Ghost(parent.owned_pages.view().difference(moved_pages));
    }
    proof {
        assert(containers.spec_index(parent_container_ptr).view().owned_pages.view().contains(thread_page)) by { broadcast use vstd::set::lemma_set_difference; };
        assert(!containers.spec_index(child_container_ptr).view().owned_pages.view().contains(thread_page));
        assert(containers.spec_index(child_container_ptr).inv()) by { reveal(RwLock::inv); reveal(Container::wf); };
        assert(containers.spec_index(parent_container_ptr).inv()) by { reveal(RwLock::inv); reveal(Container::wf); };
        assert(containers_inv(*containers)) by {
            reveal(containers_inv);
            reveal(container_perms_wf);
            reveal(RwLock::inv);
            broadcast use vstd::map::lemma_map_insert_domain;
            assert forall|container_ptr: RwLockContainerPtr|
                #![trigger containers.dom().contains(container_ptr)]
                #![trigger containers.spec_index(container_ptr)]
                containers.dom().contains(container_ptr)
                    implies containers.spec_index(container_ptr).inv()
            by {
                if container_ptr != child_container_ptr && container_ptr != parent_container_ptr
                {
                    assert(base_containers.dom().contains(container_ptr)) by { broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                    assert(base_containers.spec_index(container_ptr).inv()) by { reveal(container_perms_wf); reveal(containers_inv); };
                    assert(containers.spec_index(container_ptr).view() == base_containers.spec_index(container_ptr).view());
                    assert(containers.spec_index(container_ptr).is_init() == base_containers.spec_index(container_ptr).is_init());
                }
            };
        };
        assert(container_tree_fields_wf(base_containers)) by { reveal(container_perms_wf); };
        assert(container_tree_fields_wf(*containers)) by {
            reveal(container_tree_fields_wf);
            assert forall|container_ptr: RwLockContainerPtr|
                #![trigger containers.spec_index(container_ptr).view().children]
                #![trigger containers.spec_index(container_ptr).view_ghost().uppertree_seq]
                #![trigger containers.spec_index(container_ptr).view_ghost().subtree_set]
                #![trigger containers.spec_index(container_ptr).view_rodata().view().depth]
                containers.dom().contains(container_ptr) implies {
                    &&& containers.spec_index(container_ptr).view().children.view().no_duplicates()
                    &&& containers.spec_index(container_ptr).view_ghost().uppertree_seq.view().no_duplicates()
                    &&& !containers.spec_index(container_ptr).view().children.view().contains(container_ptr)
                    &&& containers.spec_index(container_ptr).view_ghost().uppertree_seq.view().len() == containers.spec_index(container_ptr).view_rodata().view().depth
                    &&& containers.spec_index(container_ptr).view_rodata().view().depth <= MAX_CONTAINER_TREE_DEPTH
            } by {
                if container_ptr == child_container_ptr {
                    assert(containers.spec_index(container_ptr).view().children.view() == Seq::<RwLockContainerPtr>::empty());
                    assert(containers.spec_index(container_ptr).view_ghost().uppertree_seq.view() == child_uppers);
                    assert(containers.spec_index(container_ptr).view_rodata().view().depth == child_depth);
                    assert(child_uppers.len() == child_depth);
                    assert(child_depth <= MAX_CONTAINER_TREE_DEPTH);
                    reveal(Seq::no_duplicates);
                    reveal(Seq::contains);
                } else {
                    assert(base_containers.dom().contains(container_ptr)) by { broadcast use vstd::set::lemma_set_insert_same; broadcast use vstd::set::lemma_set_insert_different; };
                    assert({
                        &&& base_containers.spec_index(container_ptr).view().children.view().no_duplicates()
                        &&& base_containers.spec_index(container_ptr).view_ghost().uppertree_seq.view().no_duplicates()
                        &&& !base_containers.spec_index(container_ptr).view().children.view().contains(container_ptr)
                        &&& base_containers.spec_index(container_ptr).view_ghost().uppertree_seq.view().len() == base_containers.spec_index(container_ptr).view_rodata().view().depth
                        &&& base_containers.spec_index(container_ptr).view_rodata().view().depth <= MAX_CONTAINER_TREE_DEPTH
                    });
                    if container_ptr == parent_container_ptr {
                        assert(!base_containers.spec_index(parent_container_ptr).view().children.view().contains(child_container_ptr)) by {
                            if base_containers.spec_index(parent_container_ptr).view().children.view().contains(child_container_ptr)
                            {
                                assert(base_containers.dom().contains(child_container_ptr)) by { reveal(container_children_parent_wf); };
                            }
                        };
                        assert(child_container_ptr != parent_container_ptr);
                        assert(containers.spec_index(container_ptr).view().children.view() == base_containers.spec_index(container_ptr).view().children.view().push(child_container_ptr));
                        assert(containers.spec_index(container_ptr).view_ghost().uppertree_seq == base_containers.spec_index(container_ptr).view_ghost().uppertree_seq);
                        assert(containers.spec_index(container_ptr).view_rodata() == base_containers.spec_index(container_ptr).view_rodata());
                        seq_push_lemma::<RwLockContainerPtr>();
                        seq_push_unique_lemma::<RwLockContainerPtr>();
                    } else {
                        assert(containers.spec_index(container_ptr).view() == base_containers.spec_index(container_ptr).view());
                        assert(containers.spec_index(container_ptr).view_ghost().uppertree_seq == base_containers.spec_index(container_ptr).view_ghost().uppertree_seq);
                        assert(containers.spec_index(container_ptr).view_rodata() == base_containers.spec_index(container_ptr).view_rodata());
                    }
                }
            };
        };
        assert(container_perms_wf(*containers)) by { reveal(container_perms_wf); };
        assert(containers.dom() == base_containers.dom().insert(child_container_ptr));
        assert({
            &&& containers.spec_index(child_container_ptr).view_rodata().view().parent == Some(parent_container_ptr)
            &&& containers.spec_index(child_container_ptr).view_rodata().view().depth == child_depth
            &&& containers.spec_index(child_container_ptr).view().children.view() == Seq::<RwLockContainerPtr>::empty()
            &&& !containers.spec_index(child_container_ptr).view().parent_linkedlist_node.is_init()
            &&& containers.spec_index(child_container_ptr).view_ghost().uppertree_seq.view() == child_uppers
            &&& containers.spec_index(child_container_ptr).view_ghost().subtree_set.view() == Set::<RwLockContainerPtr>::empty()
        });
        assert(containers.spec_index(parent_container_ptr).view().children.view() == base_containers.spec_index(parent_container_ptr).view().children.view().push(child_container_ptr));
        assert(containers.spec_index(parent_container_ptr).view().children.map().dom().contains(containers.spec_index(child_container_ptr).view().parent_linkedlist_node.addr(),));
        assert(containers.spec_index(parent_container_ptr).view().children.map().spec_index(containers.spec_index(child_container_ptr).view().parent_linkedlist_node.addr(),) == child_container_ptr);
        assert(container_add_child_ensures(root_container, base_containers, *containers, parent_container_ptr, child_container_ptr,)) by {
            child_uppers.to_set_ensures();
            reveal(container_add_child_ensures);
            reveal(container_perms_wf);
            reveal(LinkedList::wf_value_list);
            reveal(Seq::contains);
            seq_push_lemma::<RwLockContainerPtr>();
            seq_push_unique_lemma::<RwLockContainerPtr>();
            broadcast use vstd::map::lemma_map_insert_domain;
            broadcast use vstd::map::lemma_map_new_index;
        };
    }
}
}
