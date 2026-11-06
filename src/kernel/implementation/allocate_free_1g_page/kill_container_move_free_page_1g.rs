use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::super::free_4k_page::kill_container_quota_fold::lemma_container_allocator_quota_eq_total_free_without_users;
#[cfg(verus_keep_ghost)]
use super::allocate_free_1g_page_lemmas::{allocator_free_1g_pages_wf_at, kernel_inv_implies_container_allocator_1g_quota_bounded};
#[cfg(verus_keep_ghost)]
use super::kill_container_move_free_page_1g_eof::{kill_container_move_free_page_1g_eof, kill_container_move_free_page_1g_eof_transition_framing};

verus! {
/// Moves the head 1G page `pg_ptr` of `src`'s 1G global pool (`src` owns no process or thread) to the head of `dst`'s, with one page of 1G quota and the region's 262144 owned page pointers; tails keep their records and every lock the caller holds stays held.
pub fn kill_container_move_free_page_1g(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, src: RwLockContainerPtr, dst: RwLockContainerPtr, src_allocator: RwLockPageAllocatorPtr,
    dst_allocator: RwLockPageAllocatorPtr, pg_ptr: PagePtr, Tracked(src_perm): Tracked<&LockPerm>, Tracked(dst_perm): Tracked<&LockPerm>,
    Tracked(src_pool_perm): Tracked<&LockPerm>, Tracked(dst_pool_perm): Tracked<&LockPerm>, Tracked(src_quota_perm): Tracked<&LockPerm>,
    Tracked(dst_quota_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        src != dst,
        page_ptr_valid(pg_ptr),
        old(krnl).ctn_mp.dom().contains(src),
        old(krnl).ctn_mp.dom().contains(dst),
        old(krnl).ctn_mp.spec_index(src).view_rodata().view().allocator_ptr_1g == src_allocator,
        old(krnl).ctn_mp.spec_index(dst).view_rodata().view().allocator_ptr_1g == dst_allocator,
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
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_1g_lock_map(), src_allocator, TypedLockMode::Write),
        src_pool_perm.state() is WriteLock,
        src_pool_perm.thread_id() == old(lctx).thread_id(),
        src_pool_perm.lock_id() == old(krnl).allc_1g_mp.spec_index(src_allocator).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_global_pool_1g_lock_map(), dst_allocator, TypedLockMode::Write),
        dst_pool_perm.state() is WriteLock,
        dst_pool_perm.thread_id() == old(lctx).thread_id(),
        dst_pool_perm.lock_id() == old(krnl).allc_1g_mp.spec_index(dst_allocator).global_pool.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_1g_lock_map(), src_allocator, TypedLockMode::Write),
        src_quota_perm.state() is WriteLock,
        src_quota_perm.thread_id() == old(lctx).thread_id(),
        src_quota_perm.lock_id() == old(krnl).allc_1g_mp.spec_index(src_allocator).quota.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_1g_lock_map(), dst_allocator, TypedLockMode::Write),
        dst_quota_perm.state() is WriteLock,
        dst_quota_perm.thread_id() == old(lctx).thread_id(),
        dst_quota_perm.lock_id() == old(krnl).allc_1g_mp.spec_index(dst_allocator).quota.locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).allc_1g_mp.spec_index(src_allocator).global_pool.view().view().len() > 0,
        old(krnl).allc_1g_mp.spec_index(src_allocator).global_pool.view().view().spec_index(0) == pg_ptr,
        page_index_1g_valid(page_ptr2page_index(pg_ptr)),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
        forall|i: PageIndex| #![trigger final(krnl).pg_arr.spec_index(i)]
            index_valid(NUM_PAGES, i) && i != page_ptr2page_index(pg_ptr) ==> final(krnl).pg_arr.spec_index(i) == old(krnl).pg_arr.spec_index(i),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread(),
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
        final(krnl).ctn_mp.spec_index(src).view().owned_pages.view() == old(krnl).ctn_mp.spec_index(src).view().owned_pages.view().difference(page_1g_all_ptrs(page_ptr2page_index(pg_ptr))),
        final(krnl).ctn_mp.spec_index(dst).view().owned_pages.view() == old(krnl).ctn_mp.spec_index(dst).view().owned_pages.view().union(page_1g_all_ptrs(page_ptr2page_index(pg_ptr))),
        page_1g_all_ptrs(page_ptr2page_index(pg_ptr)).subset_of(old(krnl).ctn_mp.spec_index(src).view().owned_pages.view()),
        page_1g_all_ptrs(page_ptr2page_index(pg_ptr)).len() == 262144,
        final(krnl).allc_1g_mp.dom() == old(krnl).allc_1g_mp.dom(),
        forall|a: RwLockPageAllocatorPtr| #![trigger final(krnl).allc_1g_mp.spec_index(a)]
            old(krnl).allc_1g_mp.dom().contains(a) && a != src_allocator && a != dst_allocator ==> final(krnl).allc_1g_mp.spec_index(a) == old(krnl).allc_1g_mp.spec_index(a),
        0 < old(krnl).allc_1g_mp.spec_index(src_allocator).quota.view().value,
        final(krnl).allc_1g_mp.spec_index(src_allocator).quota.view().value == old(krnl).allc_1g_mp.spec_index(src_allocator).quota.view().value - 1,
        final(krnl).allc_1g_mp.spec_index(dst_allocator).quota.view().value == old(krnl).allc_1g_mp.spec_index(dst_allocator).quota.view().value + 1,
        final(krnl).allc_1g_mp.spec_index(src_allocator).quota.locking_thread() == old(krnl).allc_1g_mp.spec_index(src_allocator).quota.locking_thread(),
        final(krnl).allc_1g_mp.spec_index(dst_allocator).quota.locking_thread() == old(krnl).allc_1g_mp.spec_index(dst_allocator).quota.locking_thread(),
        final(krnl).allc_1g_mp.spec_index(src_allocator).global_pool.locking_thread() == old(krnl).allc_1g_mp.spec_index(src_allocator).global_pool.locking_thread(),
        final(krnl).allc_1g_mp.spec_index(dst_allocator).global_pool.locking_thread() == old(krnl).allc_1g_mp.spec_index(dst_allocator).global_pool.locking_thread(),
        final(krnl).allc_1g_mp.spec_index(src_allocator).cpu_caches == old(krnl).allc_1g_mp.spec_index(src_allocator).cpu_caches,
        final(krnl).allc_1g_mp.spec_index(src_allocator).global_pool.view().view() == old(krnl).allc_1g_mp.spec_index(src_allocator).global_pool.view().view().skip(1),
        final(krnl).allc_1g_mp.spec_index(src_allocator).total_free_pages.view() == old(krnl).allc_1g_mp.spec_index(src_allocator).total_free_pages.view() - 1,
        final(krnl).allc_1g_mp.spec_index(dst_allocator).global_pool.view().view() == old(krnl).allc_1g_mp.spec_index(dst_allocator).global_pool.view().view().insert(0, pg_ptr),
{
    let ghost pre = *krnl;
    let pg_idx = page_ptr2page_index(pg_ptr);
    proof {
        page_ptr_valid_imply_page_index_valid(); page_ptr_roundtrip();
        page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, src);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, dst);
        allocator_perms_wf_map(krnl.allc_1g_mp); allocator_perms_wf_at(krnl.allc_1g_mp, src_allocator); allocator_perms_wf_at(krnl.allc_1g_mp, dst_allocator);
        container_perms_wf_map(krnl.ctn_mp); container_perms_wf_at(krnl.ctn_mp, src); container_perms_wf_at(krnl.ctn_mp, dst);
        allocator_free_1g_pages_wf_global_at(krnl.allc_1g_mp, krnl.pg_arr, src_allocator, pg_ptr);
        allocator_free_1g_pages_wf_global_at(krnl.allc_1g_mp, krnl.pg_arr, dst_allocator, pg_ptr);
        allocator_free_1g_pages_wf_at(krnl.allc_1g_mp, krnl.pg_arr, pg_idx);
        krnl.allc_1g_mp.spec_index(src_allocator).global_pool.view().linked_list.wf_implies_view_len_eq_len();
        assert(krnl.allc_1g_mp.spec_index(src_allocator).global_pool.view().view().contains(pg_ptr));
        container_owned_1g_head_implies_owned_pages_contain_all_ptrs(&*krnl, pg_idx, src);
        page_1g_all_ptrs_contains_head(pg_idx);
        lemma_container_allocator_quota_eq_total_free_without_users(*krnl, src);
        kernel_inv_implies_container_allocator_1g_quota_bounded(&*krnl, dst);
        assert(krnl.allc_1g_mp.spec_index(src_allocator).global_pool.view().view().no_duplicates()) by { reveal(LinkedList::value_list_unique); };
        assert(0 < krnl.allc_1g_mp.spec_index(src_allocator).quota.view().value) by { lemma_cache_len_fold_nonneg(krnl.allc_1g_mp.spec_index(src_allocator).cpu_caches.view()); };
    }
    let (node_addr, Tracked(node_perm)) = krnl.allc_1g_mp.pop_global_pool_page_typed(src_allocator, Ghost(lctx.allocator_quota_1g_lock_map()),
        Ghost(lctx.allocator_cache_1g_lock_map()), Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(src_pool_perm));
    assert(node_addr == krnl.pg_arr.spec_index(pg_idx).view().view().free_list_node_storage.addr()) by {
        pre.allc_1g_mp.spec_index(src_allocator).global_pool.view().linked_list.wf_and_equal_values_implies_equal_addrs(node_addr, krnl.pg_arr.spec_index(pg_idx).view().view().free_list_node_storage.addr());
    };
    krnl.allc_1g_mp.push_global_pool_page_typed(dst_allocator, node_addr, Tracked(node_perm), Ghost(lctx.allocator_quota_1g_lock_map()), Ghost(lctx.allocator_cache_1g_lock_map()),
        Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(dst_pool_perm));
    {
        let quota = krnl.allc_1g_mp.borrow_mut_quota_typed(src_allocator, Ghost(lctx.allocator_quota_1g_lock_map()), Ghost(lctx.allocator_cache_1g_lock_map()),
            Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(src_quota_perm));
        quota.value = quota.value - 1;
    }
    {
        let quota = krnl.allc_1g_mp.borrow_mut_quota_typed(dst_allocator, Ghost(lctx.allocator_quota_1g_lock_map()), Ghost(lctx.allocator_cache_1g_lock_map()),
            Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(dst_quota_perm));
        quota.value = quota.value + 1;
    }
    {
        let page = krnl.pg_arr.borrow_mut_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(page_perm));
        page.state = PageState::Free1g { allocator_ptr: Ghost(dst_allocator), state: FreePageAllocatorState::GlobalList };
        page.owning_container = dst;
    }
    {
        let container = krnl.ctn_mp.borrow_mut_typed(src, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(src_perm));
        container.owned_pages = Ghost(container.owned_pages.view().difference(page_1g_all_ptrs(pg_idx)));
    }
    {
        let container = krnl.ctn_mp.borrow_mut_typed(dst, Ghost(lctx.container_lock_map()), Tracked(&*lctx), Tracked(dst_perm));
        container.owned_pages = Ghost(container.owned_pages.view().union(page_1g_all_ptrs(pg_idx)));
    }
    proof {
        lctx.enter_kernel_view_release();
        assert(kill_container_move_free_page_1g_eof_transition_framing(pre, *krnl, src, dst, src_allocator, dst_allocator, pg_ptr, node_addr)) by {
            reveal(kill_container_move_free_page_1g_eof_transition_framing);
            seq_skip_one_implies_contains_and_index_shift::<PagePtr>(); pre.allc_1g_mp.spec_index(dst_allocator).global_pool.view().view().insert_ensures(0, pg_ptr);
        };
        kill_container_move_free_page_1g_eof(pre, *krnl, src, dst, src_allocator, dst_allocator, pg_ptr, node_addr);
    }
}
} // verus!
