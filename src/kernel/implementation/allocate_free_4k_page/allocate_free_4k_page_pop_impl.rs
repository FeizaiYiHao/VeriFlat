use super::*;
use super::allocate_free_4k_page_pop_postconditions::eof_pop_4k_postconditions;
use super::allocate_free_4k_page_pop_eof::{eof_pop_4k_inv, pop_stage_4k_page_transition_framing};
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
    /// Pops the head 4k page of the CPU cache (`source` is `Some`) or the global pool (`None`) and stages it on `thread_ptr`.
    #[verifier::spinoff_prover]
    pub(super) fn pop_stage_4k_page(
    krnl: &mut KernelK, alloc_ptr_4k: RwLockPageAllocatorPtr, source: Option<CpuId>, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(source_lock_perm): Tracked<&LockPerm>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            source_lock_perm.state() is WriteLock,
            source_lock_perm.thread_id() == old(lctx).thread_id(),
            source matches Some(cpu_id) ==> {
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& source_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (alloc_ptr_4k, cpu_id), TypedLockMode::Write)
                &&& old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0
            },
            source is None ==> {
                &&& source_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id
                &&& typed_lock_map_contains_mode(old(lctx).allocator_global_pool_4k_lock_map(), alloc_ptr_4k, TypedLockMode::Write)
                &&& old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().len() > 0
            },
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < FREE_PAGE_LOCK_MAJOR,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            page_ptr_valid(ret.0),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state is Free4k,
            !old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(ret.0),
            final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, alloc_ptr_4k),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            *final(krnl) == (KernelK {
                pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp,
                ..*old(krnl)
            }),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(ret.0)),
            held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), set![page_ptr2page_index(ret.0)]),
            kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            source matches Some(cpu_id) ==> {
                &&& source_lock_perm.lock_id() == final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id
                &&& final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).lock_id()
                &&& final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.entries_unchanged_except(&old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches, cpu_id)
                &&& final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().skip(1)
                &&& typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (alloc_ptr_4k, cpu_id), TypedLockMode::Write)
                &&& final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool
            },
            source is None ==> {
                &&& source_lock_perm.lock_id() == final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id
                &&& final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id()
                &&& final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches
                &&& typed_lock_map_contains_mode(final(lctx).allocator_global_pool_4k_lock_map(), alloc_ptr_4k, TypedLockMode::Write)
            },
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
                temp_alloc_cache_4k:
                    final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
                ..old(krnl).thr_mp.spec_index(thread_ptr).view()
            }),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![thread_ptr]),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            !old(lctx).page_lock_map().dom().contains(page_ptr2page_index(ret.0)),
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(ret.0), TypedLockMode::Write),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
    {
        assert(krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf() && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.inv()
            && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.inv() && krnl.thr_mp.perms_wf() && krnl.pg_arr.inv()
        ) by { reveal(allocator_perms_wf); reveal(thread_perms_wf); reveal(page_array_wf); };
        let (node_addr, page_ptr) = match source {
            Some(cpu_id) => krnl.allc_4k_mp.borrow_cache_typed(alloc_ptr_4k, cpu_id, Ghost(lctx.allocator_cache_4k_lock_map()), Tracked(&*lctx), Tracked(source_lock_perm)).linked_list.peek_head(),
            None => krnl.allc_4k_mp.borrow_global_pool_typed(alloc_ptr_4k, Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(source_lock_perm)).peek_head(),
        };
        assert(page_ptr_valid(page_ptr)) by { reveal(allocator_perms_wf); reveal(allocator_free_page_ptrs_wf); };
        let page_index = page_ptr2page_index(page_ptr);
        let ghost free_state = match source { Some(cpu_id) => FreePageAllocatorState::PreCpuCache { cpu_id }, None => FreePageAllocatorState::GlobalList };
        proof {
            page_ptr_valid_imply_page_index_valid();
            if let Some(cpu_id) = source {
                assert({
                    &&& old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)
                    &&& krnl.pg_arr.spec_index(page_index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(alloc_ptr_4k), state: free_state }
                }) by { reveal(LinkedList::wf_value_list); reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); };
            } else {
                assert({
                    &&& old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().view().contains(page_ptr)
                    &&& krnl.pg_arr.spec_index(page_index).view().view().state == PageState::Free4k { allocator_ptr: Ghost(alloc_ptr_4k), state: free_state }
                }) by { reveal(LinkedList::wf_value_list); reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); };
            }
        }
        let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));

        let (node_addr2, Tracked(node_perm)) = match source {
            Some(cpu_id) => krnl.allc_4k_mp.pop_cache_page_typed(
                alloc_ptr_4k, cpu_id, Ghost(lctx.allocator_quota_4k_lock_map()),
                Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()),
                Tracked(&*lctx), Tracked(source_lock_perm),
            ),
            None => krnl.allc_4k_mp.pop_global_pool_page_typed(
                alloc_ptr_4k, Ghost(lctx.allocator_quota_4k_lock_map()),
                Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()),
                Tracked(&*lctx), Tracked(source_lock_perm),
            ),
        };
        proof {
            if let Some(cpu_id) = source {
                old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().linked_list.lemma_value_addr_unique(node_addr, node_addr2);
            } else {
                old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().linked_list.lemma_value_addr_unique(node_addr, node_addr2);
            }
        }
        assert(krnl.pg_arr.inv() && krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(thread_ptr).is_init()
        ) by { page_array_wf_at(krnl.pg_arr, page_index); thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        {
            let mut page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(page.owning_container == container_ptr && node_addr == page.free_list_node_storage.addr()) by {
                reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_wf); reveal(LinkedList::wf_map);
                reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf);
            };
            page.state = PageState::Owned4k { thread_ptr };
            page.free_list_node_storage.put(Tracked(node_perm));
        } {
            let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
            thread_mut.temp_alloc_cache_4k = Ghost(thread_mut.temp_alloc_cache_4k.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index,
                TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        }
        assert(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            if old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Owned4k { thread_ptr }) by { reveal(thread_staged_pages_4k_wf); };
            }
        };
        proof {
            assert(pop_stage_4k_page_transition_framing(*old(krnl), *krnl, alloc_ptr_4k, thread_ptr, container_ptr, page_ptr, node_addr, source)) by { reveal(pop_stage_4k_page_transition_framing); };
            eof_pop_4k_inv(*old(krnl), *krnl, alloc_ptr_4k, thread_ptr, container_ptr, page_ptr, node_addr, source);
            eof_pop_4k_postconditions(*old(krnl), *krnl, *old(lctx), alloc_ptr_4k, thread_ptr, container_ptr, page_ptr, node_addr, source);
        }
        (page_ptr, Tracked(page_lock_perm))
    }
} // verus!
