use vstd::prelude::*;
use vstd::assert_sets_equal;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::free_4k_page::kill_container_quota_fold::{lemma_container_allocator_quota_eq_total_free_without_users, lemma_container_allocator_2m_quota_bounded};
#[cfg(verus_keep_ghost)]
use super::kill_container_move_free_page_2m_eof::{kill_container_move_free_page_2m_eof, kill_container_move_free_page_2m_eof_transition_framing};

verus! {
/// Moves the head 2M page `page_ptr` of the 2M global pool of `src`, which owns no process, thread, or indirect thread,
/// to the head of the 2M global pool of `dst`: the page with its 511 tails, one page of 2M quota, and the 512 4K pages
/// of the region among the containers' owned pages leave `src` for `dst`. The caller write-holds both containers, both
/// pools, both quotas, the head page, and the tails through `tail_perms`, and every lock stays held.
pub fn kill_container_move_free_page_2m(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, src: RwLockContainerPtr, dst: RwLockContainerPtr, src_allocator: RwLockPageAllocatorPtr,
    dst_allocator: RwLockPageAllocatorPtr, page_ptr: PagePtr, Tracked(src_perm): Tracked<&LockPerm>, Tracked(dst_perm): Tracked<&LockPerm>,
    Tracked(src_pool_perm): Tracked<&LockPerm>, Tracked(dst_pool_perm): Tracked<&LockPerm>, Tracked(src_quota_perm): Tracked<&LockPerm>,
    Tracked(dst_quota_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>, Tracked(tail_perms): Tracked<&Map<PageIndex, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        src != dst,
        page_ptr_valid(page_ptr),
        old(krnl).ctn_mp.dom().contains(src),
        old(krnl).ctn_mp.dom().contains(dst),
        old(krnl).ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_2m == src_allocator,
        old(krnl).ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_2m == dst_allocator,
        old(krnl).ctn_mp.spec_index(src).view_ghost().uppertree_seq.view().contains(dst),
        old(krnl).ctn_mp.spec_index(src).view_ghost().owned_processes.view() =~= Set::<RwLockProcessPtr>::empty(),
        old(krnl).ctn_mp.spec_index(src).view_ghost().owned_threads.view() =~= Set::<RwLockThreadPtr>::empty(),
        old(krnl).ctn_mp.spec_index(src).view_ghost().owned_indirect_threads.view() =~= Set::<RwLockThreadPtr>::empty(),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), src, TypedLockMode::Write),
        src_perm.state() is WriteLock,
        src_perm.thread_id() == old(lctx).thread_id(),
        src_perm.lock_id() == old(krnl).ctn_mp.spec_index(src).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), dst, TypedLockMode::Write),
        dst_perm.state() is WriteLock,
        dst_perm.thread_id() == old(lctx).thread_id(),
        dst_perm.lock_id() == old(krnl).ctn_mp.spec_index(dst).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), src_allocator, TypedLockMode::Write),
        src_pool_perm.state() is WriteLock,
        src_pool_perm.thread_id() == old(lctx).thread_id(),
        src_pool_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(src_allocator).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), dst_allocator, TypedLockMode::Write),
        dst_pool_perm.state() is WriteLock,
        dst_pool_perm.thread_id() == old(lctx).thread_id(),
        dst_pool_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(dst_allocator).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_2m_lock_map(), src_allocator, TypedLockMode::Write),
        src_quota_perm.state() is WriteLock,
        src_quota_perm.thread_id() == old(lctx).thread_id(),
        src_quota_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(src_allocator).quota.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_2m_lock_map(), dst_allocator, TypedLockMode::Write),
        dst_quota_perm.state() is WriteLock,
        dst_quota_perm.thread_id() == old(lctx).thread_id(),
        dst_quota_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(dst_allocator).quota.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).allc_2m_mp.spec_index(src_allocator).global_pool.view().view().len() > 0,
        old(krnl).allc_2m_mp.spec_index(src_allocator).global_pool.view().view().spec_index(0) == page_ptr,
        page_index_2m_valid(page_ptr2page_index(page_ptr)),
        owned_2m_tail_lock_perms_wf(*tail_perms, old(krnl).pg_arr, old(lctx), page_ptr2page_index(page_ptr)),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)]
            index_valid(NUM_PAGES, i) && i != page_ptr2page_index(page_ptr) && !page_2m_tail_indices(page_ptr2page_index(page_ptr)).contains(i)
                ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
        owned_2m_tail_lock_perms_wf(*tail_perms, final(krnl).pg_arr, final(lctx), page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            old(krnl).ctn_mp.dom().contains(c) && c != src && c != dst ==> final(krnl).ctn_mp.spec_index(c) == old(krnl).ctn_mp.spec_index(c),
        forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
            c == src || c == dst ==> {
                &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(c).view_ghost() == old(krnl).ctn_mp.spec_index(c).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(c).control() == old(krnl).ctn_mp.spec_index(c).control()
                &&& final(krnl).ctn_mp.spec_index(c).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(c).view().owned_pages, ..old(krnl).ctn_mp.spec_index(c).view() })
            },
        final(krnl).ctn_mp.spec_index(src).view().owned_pages.view() == old(krnl).ctn_mp.spec_index(src).view().owned_pages.view().difference(page_2m_all_ptrs(page_ptr2page_index(page_ptr))),
        final(krnl).ctn_mp.spec_index(dst).view().owned_pages.view() == old(krnl).ctn_mp.spec_index(dst).view().owned_pages.view().union(page_2m_all_ptrs(page_ptr2page_index(page_ptr))),
        page_2m_all_ptrs(page_ptr2page_index(page_ptr)).subset_of(old(krnl).ctn_mp.spec_index(src).view().owned_pages.view()),
        page_2m_all_ptrs(page_ptr2page_index(page_ptr)).len() == 512,
        final(krnl).allc_2m_mp.dom() == old(krnl).allc_2m_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_2m_mp.spec_index(a)]
            old(krnl).allc_2m_mp.dom().contains(a) && a != src_allocator && a != dst_allocator ==> final(krnl).allc_2m_mp.spec_index(a) == old(krnl).allc_2m_mp.spec_index(a),
        0 < old(krnl).allc_2m_mp.spec_index(src_allocator).quota.view().value,
        final(krnl).allc_2m_mp.spec_index(src_allocator).quota.view().value == old(krnl).allc_2m_mp.spec_index(src_allocator).quota.view().value - 1,
        final(krnl).allc_2m_mp.spec_index(dst_allocator).quota.view().value == old(krnl).allc_2m_mp.spec_index(dst_allocator).quota.view().value + 1,
        final(krnl).allc_2m_mp.spec_index(src_allocator).quota.locking_thread() == old(krnl).allc_2m_mp.spec_index(src_allocator).quota.locking_thread(),
        final(krnl).allc_2m_mp.spec_index(dst_allocator).quota.locking_thread() == old(krnl).allc_2m_mp.spec_index(dst_allocator).quota.locking_thread(),
        final(krnl).allc_2m_mp.spec_index(src_allocator).global_pool.locking_thread() == old(krnl).allc_2m_mp.spec_index(src_allocator).global_pool.locking_thread(),
        final(krnl).allc_2m_mp.spec_index(dst_allocator).global_pool.locking_thread() == old(krnl).allc_2m_mp.spec_index(dst_allocator).global_pool.locking_thread(),
        final(krnl).allc_2m_mp.spec_index(src_allocator).cpu_caches == old(krnl).allc_2m_mp.spec_index(src_allocator).cpu_caches,
        final(krnl).allc_2m_mp.spec_index(src_allocator).global_pool.view().view() == old(krnl).allc_2m_mp.spec_index(src_allocator).global_pool.view().view().skip(1),
        final(krnl).allc_2m_mp.spec_index(src_allocator).total_free_pages.view() == old(krnl).allc_2m_mp.spec_index(src_allocator).total_free_pages.view() - 1,
        final(krnl).allc_2m_mp.spec_index(dst_allocator).global_pool.view().view() == old(krnl).allc_2m_mp.spec_index(dst_allocator).global_pool.view().view().insert(0, page_ptr),
{
    let ghost pre = *krnl;
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, src);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, dst);
        allocator_perms_wf_map(krnl.allc_2m_mp); allocator_perms_wf_at(krnl.allc_2m_mp, src_allocator); allocator_perms_wf_at(krnl.allc_2m_mp, dst_allocator);
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, src); container_perms_wf_at(krnl.ctn_mp, dst);
        container_allocator_free_2m_page_wf_global_at(krnl.allc_2m_mp, krnl.pg_arr, src_allocator, page_ptr);
        container_allocator_free_2m_page_wf_global_at(krnl.allc_2m_mp, krnl.pg_arr, dst_allocator, page_ptr);
        container_allocator_free_2m_page_wf_at(krnl.allc_2m_mp, krnl.pg_arr, page_index);
        krnl.allc_2m_mp.spec_index(src_allocator).global_pool.view().linked_list.lemma_len_view();
        assert(krnl.allc_2m_mp.spec_index(src_allocator).global_pool.view().view().contains(page_ptr));
        owned_2m_all_ptrs_belong_to_container(&*krnl, page_index, src);
        page_2m_all_ptrs_contains_head(page_index);
        lemma_container_allocator_quota_eq_total_free_without_users(*krnl, src);
        lemma_container_allocator_2m_quota_bounded(&*krnl, dst);
        assert(krnl.allc_2m_mp.spec_index(src_allocator).global_pool.view().view().no_duplicates()) by { reveal(LinkedList::value_list_unique); };
        assert(0 < krnl.allc_2m_mp.spec_index(src_allocator).quota.view().value) by { lemma_cache_len_fold_nonneg(krnl.allc_2m_mp.spec_index(src_allocator).cpu_caches.view()); };
    }
    let (node_addr, Tracked(node_perm)) = krnl.allc_2m_mp.pop_global_pool_page_typed(src_allocator, Ghost(lctx.allocator_quota_2m_lock_map()),
        Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(src_pool_perm));
    assert(node_addr == krnl.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr()) by {
        pre.allc_2m_mp.spec_index(src_allocator).global_pool.view().linked_list.lemma_value_addr_unique(node_addr, krnl.pg_arr.spec_index(page_index).view().view().free_list_node_storage.addr());
    };
    krnl.allc_2m_mp.push_global_pool_page_typed(dst_allocator, node_addr, Tracked(node_perm), Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
        Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(dst_pool_perm));
    {
        let quota = krnl.allc_2m_mp.borrow_mut_quota_typed(src_allocator, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
            Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(src_quota_perm));
        quota.value = quota.value - 1;
    }
    {
        let quota = krnl.allc_2m_mp.borrow_mut_quota_typed(dst_allocator, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()),
            Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(dst_quota_perm));
        quota.value = quota.value + 1;
    }
    set_free_2m_page_tails_container(&mut krnl.pg_arr, page_index, dst, Tracked(&*lctx), Tracked(tail_perms));
    {
        let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_perm));
        page.state = PageState::Free2m { allocator_ptr: Ghost(dst_allocator), state: FreePageAllocatorState::GlobalList };
        page.owning_container = dst;
    }
    {
        let container = krnl.ctn_mp.borrow_mut_typed(src, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(src_perm));
        container.owned_pages = Ghost(container.owned_pages.view().difference(page_2m_all_ptrs(page_index)));
    }
    {
        let container = krnl.ctn_mp.borrow_mut_typed(dst, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(dst_perm));
        container.owned_pages = Ghost(container.owned_pages.view().union(page_2m_all_ptrs(page_index)));
    }
    proof {
        lctx.enter_kernel_view_release();
        assert(kill_container_move_free_page_2m_eof_transition_framing(pre, *krnl, src, dst, src_allocator, dst_allocator, page_ptr, node_addr)) by {
            reveal(kill_container_move_free_page_2m_eof_transition_framing);
            seq_skip_lemma::<PagePtr>(); pre.allc_2m_mp.spec_index(dst_allocator).global_pool.view().view().insert_ensures(0, page_ptr);
        };
        kill_container_move_free_page_2m_eof(pre, *krnl, src, dst, src_allocator, dst_allocator, page_ptr, node_addr);
    }
}

/// Gives the 511 merged tails of the 2M page at `head`, write-held through `perms`, to `owner`; every other page stays.
fn set_free_2m_page_tails_container(
    pages: &mut PageLockedArray, head: PageIndex, owner: RwLockContainerPtr, Tracked(lctx): Tracked<&LocalContext>, Tracked(perms): Tracked<&Map<PageIndex, LockPerm>>,
)
    requires
        page_array_wf(*old(pages)),
        page_index_2m_valid(head),
        old(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        owned_2m_tail_lock_perms_wf(*perms, *old(pages), lctx, head),
    ensures
        final(pages).inv(),
        final(pages).typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
        owned_2m_tail_lock_perms_wf(*perms, *final(pages), lctx, head),
        forall|i: PageIndex| #![trigger final(pages).spec_index(i)]
            index_valid(NUM_PAGES, i) && !page_2m_tail_indices(head).contains(i) ==> final(pages).spec_index(i) == old(pages).spec_index(i),
        forall|i: PageIndex| #![trigger final(pages).spec_index(i)]
            page_2m_tail_indices(head).contains(i) ==> {
                &&& final(pages).spec_index(i).view().view() == (Page { owning_container: owner, ..old(pages).spec_index(i).view().view() })
                &&& final(pages).spec_index(i).view().is_init() == old(pages).spec_index(i).view().is_init()
                &&& final(pages).spec_index(i).view().view_rodata() == old(pages).spec_index(i).view().view_rodata()
                &&& final(pages).spec_index(i).view().view_ghost() == old(pages).spec_index(i).view().view_ghost()
                &&& final(pages).spec_index(i).view().locking_thread() == old(pages).spec_index(i).view().locking_thread()
                &&& final(pages).spec_index(i).view().being_killed() == old(pages).spec_index(i).view().being_killed()
            },
{
    proof {
        page_array_wf_map(*pages);
        assert(Set::range((head + 1) as usize, (head + 1) as usize).is_empty()) by { assert_sets_equal!(Set::range((head + 1) as usize, (head + 1) as usize) == Set::<PageIndex>::empty(), index => {}); };
    }
    let mut count: usize = 0;
    while count < 511
        invariant
            page_array_wf(*old(pages)),
            page_index_2m_valid(head),
            0 <= count <= 511,
            pages.inv(),
            pages.typed_lock_map_aligned(lctx.page_lock_map(), lctx.thread_id()),
            owned_2m_tail_lock_perms_wf(*perms, *old(pages), lctx, head),
            forall|i: PageIndex| #![trigger pages.spec_index(i)]
                index_valid(NUM_PAGES, i) && !Set::range((head + 1) as usize, (head + 1 + count) as usize).contains(i) ==> pages.spec_index(i) == old(pages).spec_index(i),
            forall|i: PageIndex| #![trigger pages.spec_index(i)]
                Set::range((head + 1) as usize, (head + 1 + count) as usize).contains(i) ==> {
                    &&& pages.spec_index(i).view().view() == (Page { owning_container: owner, ..old(pages).spec_index(i).view().view() })
                    &&& pages.spec_index(i).view().is_init() == old(pages).spec_index(i).view().is_init()
                    &&& pages.spec_index(i).view().view_rodata() == old(pages).spec_index(i).view().view_rodata()
                    &&& pages.spec_index(i).view().view_ghost() == old(pages).spec_index(i).view().view_ghost()
                    &&& pages.spec_index(i).view().locking_thread() == old(pages).spec_index(i).view().locking_thread()
                    &&& pages.spec_index(i).view().being_killed() == old(pages).spec_index(i).view().being_killed()
                    &&& pages.spec_index(i).lock_id() == old(pages).spec_index(i).lock_id()
                },
        decreases 511 - count,
    {
        let index = head + 1usize + count;
        proof {
            assert(page_2m_tail_indices(head).contains(index) && !Set::range((head + 1) as usize, (head + 1 + count) as usize).contains(index)) by {
                vstd::set_lib::range_set_properties((head + 1) as usize, (head + 512) as usize); vstd::set_lib::range_set_properties((head + 1) as usize, (head + 1 + count) as usize);
            };
        }
        let page = pages.borrow_mut_typed(index, Ghost(lctx.page_lock_map()), Tracked(lctx), Tracked(perms.tracked_borrow(index)));
        page.owning_container = owner;
        proof {
            assert(pages.spec_index(index).view().inv()) by { page_array_wf_at(*old(pages), index); reveal(Page::mappings_va_valid); };
            assert(Set::range((head + 1) as usize, (head + 2 + count) as usize) == Set::range((head + 1) as usize, (head + 1 + count) as usize).insert(index)) by {
                assert_sets_equal!(Set::range((head + 1) as usize, (head + 2 + count) as usize) == Set::range((head + 1) as usize, (head + 1 + count) as usize).insert(index), candidate => {});
            };
        }
        count = count + 1usize;
    }
}
} // verus!
