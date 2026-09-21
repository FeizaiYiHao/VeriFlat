use super::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
    pub(super) fn pop_stage_2m_page(
    krnl: &mut KernelK, alloc_ptr_2m: RwLockPageAllocatorPtr, cpu_id: CpuId, thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(cache_lock_perm): Tracked<&LockPerm>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).allc_2m_mp.dom().contains(alloc_ptr_2m),
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == old(lctx).thread_id(),
            cache_lock_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu_id), TypedLockMode::Write),
            old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_2m(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            page_ptr_valid(ret.0),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state is Free2m,
            !old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(ret.0),
            final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, alloc_ptr_2m),
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
            *final(krnl) == (KernelK {
                pg_arr: final(krnl).pg_arr,
                thr_mp: final(krnl).thr_mp,
                allc_2m_mp: final(krnl).allc_2m_mp,
                ..*old(krnl)
            }),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(ret.0)),
            held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), set![page_ptr2page_index(ret.0)]),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            cache_lock_perm.lock_id() == final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).lock_id() == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).lock_id(),
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.entries_unchanged_except(&old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches, cpu_id),
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().view() == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
            typed_lock_map_contains_mode(final(lctx).allocator_cache_2m_lock_map(), (alloc_ptr_2m, cpu_id), TypedLockMode::Write),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
                temp_alloc_cache_2m:
                    final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
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
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), KernelObjId::Page(page_ptr2page_index(ret.0)))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().insert(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned2m{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool,
    {
        assert(
            krnl.allc_2m_mp.perms_wf()
            && krnl.allc_2m_mp.spec_index(alloc_ptr_2m).wf()
            && krnl.allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.inv()
            && krnl.thr_mp.perms_wf()
            && krnl.pg_arr.inv()
        ) by {
            allocator_perms_wf_at(krnl.allc_2m_mp, alloc_ptr_2m);
            thread_perms_wf_at(krnl.thr_mp, thread_ptr);
            reveal(page_array_wf);
        };
        let cache_ref = krnl.allc_2m_mp.borrow_cache_typed(alloc_ptr_2m, cpu_id, Ghost(lctx.allocator_cache_2m_lock_map()), Tracked(&*lctx), Tracked(cache_lock_perm));
        let (node_addr, page_ptr) = cache_ref.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) by { reveal(allocator_free_page_ptrs_wf); };
        let page_index = page_ptr2page_index(page_ptr);
        assert({
            &&& index_valid(NUM_PAGES, page_index)
            &&& old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m)
                .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)
            &&& lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(page_index))
        }) by {
            page_ptr_valid_imply_page_index_valid();
            reveal(LinkedList::wf_value_list); reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf);
        };
        let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));

        let (node_addr2, Tracked(node_perm)) = krnl.allc_2m_mp.pop_cache_page_typed(
            alloc_ptr_2m, cpu_id, Ghost(lctx.allocator_quota_2m_lock_map()),
            Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()),
            Tracked(&*lctx), Tracked(cache_lock_perm),
        );
        assert(node_addr2 == node_addr) by { old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches.spec_index(cpu_id).view().view().linked_list.lemma_value_addr_unique(node_addr, node_addr2); };
        assert(
            krnl.pg_arr.inv()
            && krnl.thr_mp.perms_wf()
            && krnl.thr_mp.spec_index(thread_ptr).is_init()
        ) by {
            assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
            thread_perms_wf_at(krnl.thr_mp, thread_ptr);
        };
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        {
            let mut page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(
                page.state == PageState::Free2m {
                    allocator_ptr: Ghost(alloc_ptr_2m),
                    state: FreePageAllocatorState::PreCpuCache { cpu_id },
                }
                && page.owning_container == container_ptr
            ) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(container_allocator_wf); };
            page.state = PageState::Owned2m { thread_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(LinkedList::wf_map); };
            page.free_list_node_storage.put(Tracked(node_perm));
        } {
            let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
            thread_mut.temp_alloc_cache_2m = Ghost(thread_mut.temp_alloc_cache_2m.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index,
                TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        }
        assert(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) == false) by {
            if old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) {
                assert(old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned2m { thread_ptr }) by { reveal(thread_staged_pages_2m_wf); };
            }
        };
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
        }
        proof {
            assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_array_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf); reveal(allocator_perms_wf); reveal(process_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
            assert(krnl.memory_management_inv()) by {
                assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by { reveal(cpu_set_pages_wf); };
                assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
                };
                assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
                assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
                assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
                assert(container_process_allocator_quota_2m_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_2m_mp)) by {
                    reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
                    lemma_thread_effective_quota_2m_fold_change_by_forall(thread_ptr, -1);
                    lemma_thread_effective_quota_2m_fold_sum_eq_forall();
                    lemma_thread_pending_2m_folds_eq_forall(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp);
                    lemma_process_effective_quota_2m_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp)) by {
                    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
                        krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_4k_mp,
                    );
                };
                assert(container_process_allocator_quota_1g_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp)) by {
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
                        krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_1g_mp,
                    );
                };
                assert(container_process_allocator_quota_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp));
                assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
                assert(allocator_free_page_ptrs_wf(krnl.allc_2m_mp)) by { reveal(allocator_free_page_ptrs_wf); };
                assert(hugepage_2m_wf(krnl.pg_arr)) by { reveal(hugepage_2m_wf); };
                assert(hugepage_1g_wf(krnl.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
                assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
                assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
                assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by { reveal(scheduler_pages_wf); };
                assert(thread_staged_pages_2m_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
                assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                    thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                    thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                };
                assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
                assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
                assert(krnl.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_global_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by {
                    reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf);
                    page_ptr_valid_imply_page_index_valid();
                };
                assert(container_allocator_cpu_cache_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by {
                    page_ptr_roundtrip();
                    reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); };
                assert(container_allocator_global_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_cpu_cache_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); };
                assert(container_allocator_global_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_cpu_cache_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); };
            };
            assert(krnl.process_management_inv()) by {
                assert(thread_caller_callee_wf(krnl.thr_mp)) by {
                    assert(thread_process_management_fields_unchanged(old(krnl).thr_mp, krnl.thr_mp)) by { reveal(thread_perms_wf); };
                    thread_caller_callee_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp);
                };
                assert(per_container_process_tree_wf(krnl.ctn_mp, krnl.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(krnl.ctn_mp, old(krnl).prc_mp, krnl.prc_mp); };
                thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                container_thread_endpoint_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                container_thread_scheduler_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.sched_mp);
                container_thread_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp);
                process_thread_wf_preserved_for_thread_process_management_fields(krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp);
                thread_cpu_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.cpu_arr);
            };
        }
        proof {
            held_pages_unchanged_except_for_entries_unchanged_except(
                old(krnl).pg_arr, krnl.pg_arr, old(lctx), page_index,
            );
            held_threads_unchanged_except_for_unchanged_except(
                old(krnl).thr_mp, krnl.thr_mp, old(lctx), thread_ptr,
            );
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    #[verifier::spinoff_prover]
    pub(super) fn pop_stage_global_2m_page(
    krnl: &mut KernelK, alloc_ptr_2m: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_2m == alloc_ptr_2m,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).allc_2m_mp.dom().contains(alloc_ptr_2m),
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedLockMode::Write),
            old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().len() > 0,
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_2m(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            page_ptr_valid(ret.0),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state is Free2m,
            !old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(ret.0),
            final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, alloc_ptr_2m),
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).quota,
            *final(krnl) == (KernelK {
                pg_arr: final(krnl).pg_arr,
                thr_mp: final(krnl).thr_mp,
                allc_2m_mp: final(krnl).allc_2m_mp,
                ..*old(krnl)
            }),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(ret.0)),
            held_pages_unchanged_except(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx), set![page_ptr2page_index(ret.0)]),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            global_pool_lock_perm.lock_id() == final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.locking_thread()->Write_lock_id,
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id() == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.lock_id(),
            final(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches == old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).cpu_caches,
            typed_lock_map_contains_mode(final(lctx).allocator_global_pool_2m_lock_map(), alloc_ptr_2m, TypedLockMode::Write),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread {
                temp_alloc_cache_2m:
                    final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
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
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), KernelObjId::Page(page_ptr2page_index(ret.0)))),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(ret.0)), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), mode: TypedLockMode::Write,
            }),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().insert(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned2m{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
    {
        proof {
            allocator_perms_wf_at(krnl.allc_2m_mp, alloc_ptr_2m);
            thread_perms_wf_at(krnl.thr_mp, thread_ptr);
            assert(
                krnl.allc_2m_mp.spec_index(alloc_ptr_2m).wf()
                && krnl.allc_2m_mp.spec_index(alloc_ptr_2m)
                    .global_pool.inv()
                && krnl.pg_arr.inv()
            ) by {
                reveal(page_array_wf);
            };
        }
        let poll_ref = krnl.allc_2m_mp.borrow_global_pool_typed(alloc_ptr_2m, Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), Tracked(global_pool_lock_perm));
        let (node_addr, page_ptr) = poll_ref.peek_head();
        assert(page_ptr_valid(page_ptr)) by { reveal(allocator_free_page_ptrs_wf); };
        let page_index = page_ptr2page_index(page_ptr);
        assert(index_valid(NUM_PAGES, page_index)) by { page_ptr_valid_imply_page_index_valid(); };
        assert(old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m)
            .global_pool.view().view().contains(page_ptr)) by {
            reveal(LinkedList::wf_value_list);
        };
        assert(krnl.pg_arr.spec_index(page_index).view().view().state
            == PageState::Free2m {
                allocator_ptr: Ghost(alloc_ptr_2m),
                state: FreePageAllocatorState::GlobalList,
            }) by {
            reveal(container_allocator_free_2m_page_wf);
            reveal(container_allocator_global_free_2m_page_wf);
        };
        assert(lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(page_index)));
        let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));

        let (node_addr2, Tracked(node_perm)) = krnl.allc_2m_mp.pop_global_pool_page_typed(
            alloc_ptr_2m, Ghost(lctx.allocator_quota_2m_lock_map()),
            Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()),
            Tracked(&*lctx), Tracked(global_pool_lock_perm),
        );
        assert(node_addr2 == node_addr) by { old(krnl).allc_2m_mp.spec_index(alloc_ptr_2m).global_pool.view().linked_list.lemma_value_addr_unique(node_addr, node_addr2); };
        proof {
            thread_perms_wf_at(old(krnl).thr_mp, thread_ptr);
            page_array_wf_at(krnl.pg_arr, page_index);
        }
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);

        {
            let mut page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(
                page.state == PageState::Free2m {
                    allocator_ptr: Ghost(alloc_ptr_2m),
                    state: FreePageAllocatorState::GlobalList,
                }
                && page.owning_container == container_ptr
            ) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_wf); };
            page.state = PageState::Owned2m { thread_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(LinkedList::wf_map); };
            page.free_list_node_storage.put(Tracked(node_perm));
        } {
            let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
            thread_mut.temp_alloc_cache_2m = Ghost(thread_mut.temp_alloc_cache_2m.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index,
                TypedHeldLock { lock_id: old_page_lock_id, mode: TypedLockMode::Write },
                TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        }
        assert(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) == false) by {
            if old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m.view().contains(page_ptr) {
                assert(old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned2m { thread_ptr }) by { reveal(thread_staged_pages_2m_wf); };
            }
        };
        proof {
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
        }
        proof {
            assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_array_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf); reveal(allocator_perms_wf); reveal(process_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
            assert(krnl.memory_management_inv()) by {
                assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by { reveal(cpu_set_pages_wf); };
                assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
                };
                assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
                assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
                assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
                assert(container_process_allocator_quota_2m_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_2m_mp)) by {
                    reveal(container_process_allocator_quota_2m_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
                    lemma_thread_effective_quota_2m_fold_change_by_forall(thread_ptr, -1);
                    lemma_thread_effective_quota_2m_fold_sum_eq_forall();
                    lemma_thread_pending_2m_folds_eq_forall(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp);
                    lemma_process_effective_quota_2m_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp)) by {
                    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(
                        krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_4k_mp,
                    );
                };
                assert(container_process_allocator_quota_1g_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp)) by {
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(
                        krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_1g_mp,
                    );
                };
                assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
                assert(allocator_free_page_ptrs_wf(krnl.allc_2m_mp)) by { reveal(allocator_free_page_ptrs_wf); };
                assert(hugepage_2m_wf(krnl.pg_arr)) by { reveal(hugepage_2m_wf); };
                assert(hugepage_1g_wf(krnl.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
                assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
                assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
                assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by { reveal(scheduler_pages_wf); };
                assert(thread_staged_pages_2m_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_2m_wf); };
                assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                    thread_staged_pages_4k_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                    thread_staged_pages_1g_wf_preserved_for_temp_cache_and_owned_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                };
                assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
                assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
                assert(krnl.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_global_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by {
                    reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_cpu_cache_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by {
                    reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf);
                    page_ptr_valid_imply_page_index_valid();
                    page_ptr2page_index_injective();
                    reveal(allocator_perms_wf);
                };
                assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); };
                assert(container_allocator_global_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_cpu_cache_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); };
                assert(container_allocator_global_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_cpu_cache_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); };
            };
            assert(krnl.process_management_inv()) by {
                assert(thread_caller_callee_wf(krnl.thr_mp)) by {
                    assert(thread_process_management_fields_unchanged(old(krnl).thr_mp, krnl.thr_mp)) by { reveal(thread_perms_wf); };
                    thread_caller_callee_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp);
                };
                assert(per_container_process_tree_wf(krnl.ctn_mp, krnl.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(krnl.ctn_mp, old(krnl).prc_mp, krnl.prc_mp); };
                thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                container_thread_endpoint_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                container_thread_scheduler_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.sched_mp);
                container_thread_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp);
                process_thread_wf_preserved_for_thread_process_management_fields(krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp);
                thread_cpu_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.cpu_arr);
            };
        }
        proof {
            held_pages_unchanged_except_for_entries_unchanged_except(
                old(krnl).pg_arr, krnl.pg_arr, old(lctx), page_index,
            );
            held_threads_unchanged_except_for_unchanged_except(
                old(krnl).thr_mp, krnl.thr_mp, old(lctx), thread_ptr,
            );
        }
        (page_ptr, Tracked(page_lock_perm))
    }
} // verus!
