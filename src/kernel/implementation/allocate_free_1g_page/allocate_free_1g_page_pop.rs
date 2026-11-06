#[cfg(verus_keep_ghost)]
use super::allocate_free_1g_page_pop_eof::{pop_stage_1g_page_eof_transition_framing, pop_stage_1g_page_eof};
#[cfg(verus_keep_ghost)]
use super::allocate_free_1g_page_pop_postconditions::pop_stage_1g_page_eof_postconditions;
#[cfg(verus_keep_ghost)]
use super::allocate_free_1g_page_lemmas::{allocator_free_1g_pages_wf_at, thread_staged_1g_pages_wf_at};
use vstd::prelude::*;
use crate::*;

verus! {
    /// Pops the head 1G page of the write-held global pool of `alloc_ptr_1g` and stages it on `thrd_ptr`.
    pub(super) fn pop_stage_1g_page(
        krnl: &mut KernelK, alloc_ptr_1g: RwLockPageAllocatorPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(pool_lock_perm): Tracked<&LockPerm>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).ctn_mp.dom().contains(ctn_ptr),
            old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_1g == alloc_ptr_1g,
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            old(krnl).allc_1g_mp.dom().contains(alloc_ptr_1g),
            pool_lock_perm.state() is WriteLock,
            pool_lock_perm.thread_id() == old(lctx).thread_id(),
            pool_lock_perm.lock_id() == old(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_global_pool_1g_lock_map(), alloc_ptr_1g, TypedLockMode::Write),
            old(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.view().len() > 0,
            old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            thread_effective_quota_1g(old(krnl).thrd_mp.spec_index(thrd_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_allocator_locks(),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            page_ptr_valid(ret.0),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state is Free1g,
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(ret.0),
            final(krnl).allc_1g_mp.unchanged_except(&old(krnl).allc_1g_mp, alloc_ptr_1g),
            final(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).quota == old(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).quota,
            *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, allc_1g_mp: final(krnl).allc_1g_mp, ..*old(krnl) }),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(ret.0)),
            held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), set![page_ptr2page_index(ret.0)]),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            pool_lock_perm.lock_id() == final(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.locking_thread()->Write_lock_id,
            final(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.lock_id() == old(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.lock_id(),
            final(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches == old(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).cpu_caches,
            typed_lock_map_contains_mode(final(lctx).allocator_global_pool_1g_lock_map(), alloc_ptr_1g, TypedLockMode::Write),
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { temp_alloc_cache_1g: final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
            final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
            held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            final(krnl).thrd_mp.lock_id_by_key(thrd_ptr) == old(krnl).thrd_mp.lock_id_by_key(thrd_ptr),
            !old(lctx).page_lock_map().dom().contains(page_ptr2page_index(ret.0)),
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.0), TypedLockMode::Write),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view() =~= old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().insert(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned1g { thread_ptr: thrd_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == ctn_ptr,
    {
        assert(krnl.allc_1g_mp.perms_wf() && krnl.allc_1g_mp.spec_index(alloc_ptr_1g).wf() && krnl.allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.inv() && krnl.thrd_mp.perms_wf() && krnl.pg_arr.inv())
            by { allocator_perms_wf_map(krnl.allc_1g_mp); allocator_perms_wf_at(krnl.allc_1g_mp, alloc_ptr_1g); thread_perms_wf_map(krnl.thrd_mp); page_array_wf_map(krnl.pg_arr); };
        let (node_addr, pg_ptr) = krnl.allc_1g_mp.borrow_global_pool_typed(alloc_ptr_1g, Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(pool_lock_perm)).peek_head();
        assert(page_ptr_valid(pg_ptr)) by { allocator_free_page_ptrs_wf_global_at(krnl.allc_1g_mp, alloc_ptr_1g, pg_ptr); };
        let pg_idx = page_ptr2page_index(pg_ptr);
        assert(krnl.pg_arr.spec_index(pg_idx).view().view().state == PageState::Free1g { allocator_ptr: Ghost(alloc_ptr_1g), state: FreePageAllocatorState::GlobalList }) by {
            allocator_free_1g_pages_wf_global_at(krnl.allc_1g_mp, krnl.pg_arr, alloc_ptr_1g, pg_ptr);
        };
        let Tracked(page_lock_perm) = krnl.wlock_page(pg_idx, Tracked(&mut *lctx));
        let (node_addr2, Tracked(node_perm)) = krnl.allc_1g_mp.pop_global_pool_page_typed(alloc_ptr_1g, Ghost(lctx.allocator_quota_1g_lock_map()), Ghost(lctx.allocator_cache_1g_lock_map()),
            Ghost(lctx.allocator_global_pool_1g_lock_map()), Tracked(&*lctx), Tracked(pool_lock_perm));
        proof { old(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.view().linked_list.wf_and_equal_values_implies_equal_addrs(node_addr, node_addr2); }
        assert(krnl.pg_arr.inv() && krnl.thrd_mp.spec_index(thrd_ptr).is_init()) by {
            assert(krnl.pg_arr.inv()) by { page_array_wf_map(krnl.pg_arr); };
            thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        };
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
        {
            let mut page = krnl.pg_arr.borrow_mut_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(page.owning_container == ctn_ptr && node_addr == page.free_list_node_storage.addr()) by {
                allocator_free_1g_pages_wf_at(old(krnl).allc_1g_mp, old(krnl).pg_arr, pg_idx);
                container_allocator_wf_at(old(krnl).ctn_mp, old(krnl).allc_4k_mp, old(krnl).allc_2m_mp, old(krnl).allc_1g_mp, ctn_ptr);
                old(krnl).allc_1g_mp.spec_index(alloc_ptr_1g).global_pool.view().linked_list.wf_and_equal_values_implies_equal_addrs(node_addr, page.free_list_node_storage.addr());
            };
            page.state = PageState::Owned1g { thread_ptr: thrd_ptr };
            page.free_list_node_storage.put(Tracked(node_perm));
        } {
            let thread_mut = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
            thread_mut.temp_alloc_cache_1g = Ghost(thread_mut.temp_alloc_cache_1g.view().insert(pg_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Page(pg_idx), old_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), pg_idx, TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(pg_idx), mode: TypedLockMode::Write });
        }
        assert(old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr) == false) by {
            if old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().contains(pg_ptr) { thread_staged_1g_pages_wf_at(old(krnl).thrd_mp, old(krnl).pg_arr, thrd_ptr, pg_ptr); }
        };
        proof {
            assert(pop_stage_1g_page_eof_transition_framing(*old(krnl), *krnl, alloc_ptr_1g, thrd_ptr, ctn_ptr, pg_ptr, node_addr)) by { reveal(pop_stage_1g_page_eof_transition_framing); };
            pop_stage_1g_page_eof(*old(krnl), *krnl, alloc_ptr_1g, thrd_ptr, ctn_ptr, pg_ptr, node_addr);
            pop_stage_1g_page_eof_postconditions(*old(krnl), *krnl, *old(lctx), alloc_ptr_1g, thrd_ptr, ctn_ptr, pg_ptr, node_addr);
        }
        (pg_ptr, Tracked(page_lock_perm))
    }
} // verus!
