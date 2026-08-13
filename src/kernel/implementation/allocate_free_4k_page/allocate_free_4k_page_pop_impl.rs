use super::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {

impl KernelK {

    // ================================================================
    // pop_stage_4k_page: cache[cpu_id] + thread are already write-locked and
    // the cache is non-empty. Peek the head, lock the page slot, pop the head,
    // retype it Free4k{PreCpuCache}→Owned4k, stage it in the thread's
    // temp_alloc_cache_4k, decrement the allocator's total_free_pages. Leaves
    // page + cache still write-locked; re-establishes inv().
    // ================================================================
    #[verifier::spinoff_prover]
    pub(super) fn pop_stage_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_lock_perm): Tracked<&LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            cpu_id_valid(cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).container_map.dom().contains(container_ptr),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == old(lctx).thread_id(),
            cache_lock_perm.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(self).thread_map.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(self).inv(),
            page_ptr_valid(ret.0),
            old(lctx).lock_entry_fresh(
                old(self).page_array.lock_id_by_index(
                    page_ptr2page_index(ret.0)),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
                MUTABLE_LOCK_ID),
            old(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state is Free4k,
            !old(self).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_4k.view().contains(ret.0),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            forall|p: RwLockPageAllocatorPtr|
                #![trigger final(self).allocator_4k_map.spec_index(p)]
                old(self).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                ==> final(self).allocator_4k_map.spec_index(p)
                    == old(self).allocator_4k_map.spec_index(p),
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).page_array.unchanged_except(
                &old(self).page_array, page_ptr2page_index(ret.0)),
            held_pages_unchanged(
                old(self).page_array, final(self).page_array, old(lctx)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- cache + thread lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            cache_lock_perm.lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).lock_id(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.unchanged_except(
                &old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches, cpu_id),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(self).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(self).thread_map.spec_index(thread_ptr).view().owning_container
                == old(self).thread_map.spec_index(thread_ptr).view().owning_container,
            final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            thread_lock_perm.lock_id() == final(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            // ---- page slot left write-locked, perm handed back ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            // ---- held-lock set: gained exactly the page slot ----
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                (
                    final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
                    KernelObjId::Page(page_ptr2page_index(ret.0)),
                ),
            ),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                =~= old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container
                == container_ptr,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(self).thread_map.spec_index(thread_ptr).view(),
                ),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                == old(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(self).container_map == old(self).container_map,
            final(self).process_map == old(self).process_map,
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).cpu_array == old(self).cpu_array,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
    {
        assert(
            self.allocator_4k_map.perms_wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches.inv()
            && self.thread_map.perms_wf()
            && self.page_array.inv()
        ) by {
            reveal(allocator_perms_wf);
            reveal(thread_perms_wf);
            reveal(page_array_wf);
        };
        let cache_ref = self.allocator_4k_map.borrow_cache(
            alloc_ptr_4k, cpu_id, Tracked(cache_lock_perm),
        );
        let (node_addr, page_ptr) = cache_ref.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) by {
            reveal(allocator_perms_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        let page_index = page_ptr2page_index(page_ptr);
        assert(
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)
        ) by {
            reveal(LinkedList::wf_value_list);
        };
        assert({
            &&& lctx.lock_id_acyclic(
                self.page_array.lock_id_by_index(page_index),
            )
            &&& old(lctx).lock_entry_fresh(
                old(self).page_array.lock_id_by_index(page_index),
                KernelObjId::Page(page_index),
                MUTABLE_LOCK_ID)
        }) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_cpu_cache_free_4k_page_wf);
            reveal(lock_id_aligned);
        };
        // Lock the page slot after deriving its ordering id from the cache head.
        let Tracked(page_lock_perm) = self.wlock_page(page_index, Tracked(&mut *lctx));

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let alloc_mut = self.allocator_4k_map.borrow_mut(alloc_ptr_4k);
        let (node_addr2, Tracked(node_perm)) = alloc_mut.pop_cache_page(cpu_id, Tracked(&*lctx), Tracked(cache_lock_perm));
        assert(node_addr2 == node_addr) by {
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().linked_list
                .lemma_value_addr_unique(node_addr, node_addr2);
        };
        assert(
            self.page_array.inv()
            && self.thread_map.perms_wf()
            && self.thread_map.spec_index(thread_ptr).is_init()
        ) by {
            reveal(page_array_wf);
            reveal(thread_perms_wf);
        };
        let ghost old_page_lock_id = self.page_array.lock_id_by_index(page_index);
        {
            let mut page = self.page_array.borrow_mut(
                page_index, Tracked(&*lctx), Tracked(&page_lock_perm),
            );
            assert(
                page.state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr_4k),
                    state: FreePageAllocatorState::PreCpuCache { cpu_id },
                }
                && page.owning_container == container_ptr
            ) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_cpu_cache_free_4k_page_wf);
                reveal(container_allocator_wf);
            };
            page.state = PageState::Owned4k { thread_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_cpu_cache_free_4k_page_wf);
                reveal(LinkedList::wf_map);
            };
            page.free_list_node_storage.put(Tracked(node_perm));

            let thread_mut = self.thread_map.borrow_mut(
                thread_ptr, Tracked(&*lctx), Tracked(thread_lock_perm),
            );
            thread_mut.temp_alloc_cache_4k = Ghost(thread_mut.temp_alloc_cache_4k.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                old_page_lock_id,
                self.page_array.lock_id_by_index(page_index),
            );
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
            };
        }
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            page_ptr_lemma1();
            reveal(thread_staged_pages_4k_wf);
            if old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { thread_ptr }) by {
                    reveal(thread_staged_pages_4k_wf);
                };
            }
        };
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(lock_id_aligned);
            };
        }
        proof {
            assert(
                thread_quota_2m_fields_unchanged(old(self).thread_map, self.thread_map)
                && thread_quota_1g_fields_unchanged(old(self).thread_map, self.thread_map)
            ) by {
                reveal(thread_quota_2m_fields_unchanged);
                reveal(thread_quota_1g_fields_unchanged);
            };
            // ---- subsystems_inv ----
            assert(self.subsystems_inv()) by {
                reveal(KernelK::default_pagetable_wf);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(container_tree_fields_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(thread_temp_alloc_empty_unless_wlocked);
                reveal(page_array_wf);
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
            };
            // ---- memory_management_inv ----
            assert(self.memory_management_inv()) by {
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array); };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(container_pages_wf(self.page_array, self.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map); };
                assert(process_pages_wf(self.page_array, self.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map); };
                assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_wf);
                    reveal(container_thread_wf);
                    reveal(container_allocator_wf);
                    lemma_thread_effective_quota_4k_fold_change_by_forall(thread_ptr, -1);
                    lemma_thread_effective_quota_4k_fold_sum_eq_forall();
                    lemma_thread_pending_4k_folds_eq_forall(
                        self.container_map,
                        old(self).thread_map,
                        self.thread_map,
                    );
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by {
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                };
                assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by {
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(hugepage_2m_wf(self.page_array)) by {
                    hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array);
                };
                assert(hugepage_1g_wf(self.page_array)) by {
                    hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array);
                };
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                    page_pagetable_wf_preserved_for_nonmapped_page_change(old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array, page_index);
                };
                assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(self.iommu_table_map, self.page_array)) by {
                    reveal(iommu_table_pages_wf);
                };
                assert(pcid_allocator_pages_wf(
                    self.page_array,
                    self.pcid_allocator_map,
                )) by {
                    pcid_allocator_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).pcid_allocator_map, self.pcid_allocator_map);
                };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                assert(thread_staged_pages_wf(self.thread_map, self.page_array)) by {
                    reveal(thread_staged_pages_4k_wf);
                    thread_staged_pages_2m_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                };
                assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array); };
                assert(container_allocator_global_free_4k_page_wf(
                    self.allocator_4k_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_global_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_lemma1();
                };
                assert(container_allocator_cpu_cache_free_4k_page_wf(
                    self.allocator_4k_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_cpu_cache_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_free_4k_page_wf(
                    self.allocator_4k_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                };
                assert(container_allocator_global_free_2m_page_wf(
                    self.allocator_2m_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_global_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_2m_page_wf(
                    self.allocator_2m_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_cpu_cache_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_2m_page_wf(
                    self.allocator_2m_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                };
                assert(container_allocator_global_free_1g_page_wf(
                    self.allocator_1g_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_global_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_1g_page_wf(
                    self.allocator_1g_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_cpu_cache_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_1g_page_wf(
                    self.allocator_1g_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                };
            };
            // ---- process_management_inv: container_map, thread_map, etc. all byte-equal ----
            assert(self.process_management_inv()) by {
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    per_container_process_tree_wf_preserved_for_tree_fields_eq(self.container_map, old(self).process_map, self.process_map);
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map);
                thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map);
                container_thread_endpoint_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.endpoint_map);
                container_thread_scheduler_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.scheduler_map);
                container_thread_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map);
                process_thread_wf_preserved_for_thread_process_management_fields(self.process_map, old(self).thread_map, self.thread_map);
                thread_cpu_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.cpu_array);
            };
            assert(self.inv()) by {
                reveal(cpu_dirty_map_contains_container_processes);
                reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                reveal(cpu_dirty_map_proc_pcid_match);
                reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                reveal(container_cpu_wf);
                reveal(tlb_wf_spec);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    // ================================================================
    // pop_stage_global_4k_page: global-pool twin of pop_stage_4k_page. The
    // allocator's global_pool + the thread are already write-locked and the
    // pool is non-empty. Peek the head, lock the page slot, pop the head,
    // retype it Free4k{GlobalList}→Owned4k, stage it in the thread's
    // temp_alloc_cache_4k, decrement the allocator's total_free_pages. Leaves
    // page + global_pool still write-locked; re-establishes inv().
    // ================================================================
    #[verifier::spinoff_prover]
    pub(super) fn pop_stage_global_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).container_map.dom().contains(container_ptr),
            old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.view().len() > 0,
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(self).thread_map.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(self).inv(),
            page_ptr_valid(ret.0),
            old(lctx).lock_entry_fresh(
                old(self).page_array.lock_id_by_index(
                    page_ptr2page_index(ret.0)),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
                MUTABLE_LOCK_ID),
            old(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state is Free4k,
            !old(self).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_4k.view().contains(ret.0),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota,
            forall|p: RwLockPageAllocatorPtr|
                #![trigger final(self).allocator_4k_map.spec_index(p)]
                old(self).allocator_4k_map.dom().contains(p) && p != alloc_ptr_4k
                ==> final(self).allocator_4k_map.spec_index(p)
                    == old(self).allocator_4k_map.spec_index(p),
            final(self).allocator_2m_map == old(self).allocator_2m_map,
            final(self).allocator_1g_map == old(self).allocator_1g_map,
            final(self).page_array.unchanged_except(
                &old(self).page_array, page_ptr2page_index(ret.0)),
            held_pages_unchanged(
                old(self).page_array, final(self).page_array, old(lctx)),
            // ---- user view unchanged: staging is kernel-internal ----
            kernel_k_to_kernel_u(*final(self)) == kernel_k_to_kernel_u(*old(self)),
            // ---- global_pool + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            global_pool_lock_perm.lock_id() == final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.lock_id(),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(self).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(self).thread_map.spec_index(thread_ptr).view().owning_container
                == old(self).thread_map.spec_index(thread_ptr).view().owning_container,
            final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.unchanged_except(&old(self).thread_map, thread_ptr),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            thread_lock_perm.lock_id() == final(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(self).thread_map.lock_id_by_key(thread_ptr)
                == old(self).thread_map.lock_id_by_key(thread_ptr),
            // ---- page slot left write-locked, perm handed back ----
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            // ---- held-lock set: gained exactly the page slot ----
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                (
                    final(self).page_array.lock_id_by_index(page_ptr2page_index(ret.0)),
                    KernelObjId::Page(page_ptr2page_index(ret.0)),
                ),
            ),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()
                =~= old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container
                == container_ptr,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(self).thread_map.spec_index(thread_ptr).view(),
                ),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors
                == old(self).thread_map.spec_index(thread_ptr).view().endpoint_descriptors,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(self).container_map == old(self).container_map,
            final(self).process_map == old(self).process_map,
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
            final(self).endpoint_map == old(self).endpoint_map,
            final(self).iommu_root_table == old(self).iommu_root_table,
            final(self).iommu_table_map == old(self).iommu_table_map,
            final(self).iommu_tlb == old(self).iommu_tlb,
            final(self).cpu_array == old(self).cpu_array,
    {
        assert(
            self.allocator_4k_map.perms_wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
            && self.allocator_4k_map.spec_index(alloc_ptr_4k).global_pool.inv()
            && self.thread_map.perms_wf()
            && self.page_array.inv()
        ) by {
            reveal(allocator_perms_wf);
            reveal(thread_perms_wf);
            reveal(page_array_wf);
        };
        let poll_ref = self.allocator_4k_map.borrow_global_pool(
            alloc_ptr_4k, Tracked(global_pool_lock_perm),
        );
        let (node_addr, page_ptr) = poll_ref.peek_head();
        assert(page_ptr_valid(page_ptr)) by {
            reveal(allocator_perms_wf);
            reveal(allocator_free_page_ptrs_wf);
        };
        let page_index = page_ptr2page_index(page_ptr);
        assert(
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().view().contains(page_ptr)
        ) by {
            reveal(LinkedList::wf_value_list);
        };
        assert({
            &&& self.page_array.spec_index(page_index).view().view().state
                == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr_4k),
                    state: FreePageAllocatorState::GlobalList,
                }
            &&& old(lctx).lock_entry_fresh(
                old(self).page_array.lock_id_by_index(page_index),
                KernelObjId::Page(page_index),
                MUTABLE_LOCK_ID)
        }) by {
            reveal(container_allocator_free_4k_page_wf);
            reveal(container_allocator_global_free_4k_page_wf);
            reveal(lock_id_aligned);
        };
        // Lock the page slot after deriving its ordering id from the pool head.
        let Tracked(page_lock_perm) = self.wlock_page(page_index, Tracked(&mut *lctx));

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let alloc_mut = self.allocator_4k_map.borrow_mut(alloc_ptr_4k);
        let (node_addr2, Tracked(node_perm)) = alloc_mut.pop_global_pool_page(Tracked(&*lctx), Tracked(global_pool_lock_perm));
        assert(node_addr2 == node_addr) by {
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().linked_list
                .lemma_value_addr_unique(node_addr, node_addr2);
        };
        assert(
            self.page_array.inv()
            && self.thread_map.perms_wf()
            && self.thread_map.spec_index(thread_ptr).is_init()
        ) by {
            reveal(page_array_wf);
            reveal(thread_perms_wf);
        };
        let ghost old_page_lock_id = self.page_array.lock_id_by_index(page_index);

        {
            let mut page = self.page_array.borrow_mut(page_index, Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(
                page.state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr_4k),
                    state: FreePageAllocatorState::GlobalList,
                }
                && page.owning_container == container_ptr
            ) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_global_free_4k_page_wf);
                reveal(container_allocator_wf);
            };
            page.state = PageState::Owned4k { thread_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by {
                reveal(container_allocator_free_4k_page_wf);
                reveal(container_allocator_global_free_4k_page_wf);
                reveal(LinkedList::wf_map);
            };
            page.free_list_node_storage.put(Tracked(node_perm));

            let thread_mut = self.thread_map.borrow_mut(
                thread_ptr, Tracked(&*lctx), Tracked(thread_lock_perm),
            );
            thread_mut.temp_alloc_cache_4k = Ghost(thread_mut.temp_alloc_cache_4k.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(
                KernelObjId::Page(page_index),
                old_page_lock_id,
                self.page_array.lock_id_by_index(page_index),
            );
            assert(lock_id_aligned(self, &*lctx)) by {
                reveal(lock_id_aligned);
            };
        }
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            page_ptr_lemma1();
            reveal(thread_staged_pages_4k_wf);
            if old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(self).page_array.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { thread_ptr }) by {
                    reveal(thread_staged_pages_4k_wf);
                };
            }
        };
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            assert(kernel_k_to_kernel_u(*self) == kernel_k_to_kernel_u(*old(self))) by {
                kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self);
            };
            assert(self.locked_objects_match_lctx(&*lctx)) by {
                reveal(lock_id_aligned);
            };
        }
        proof {
            assert(
                thread_quota_2m_fields_unchanged(old(self).thread_map, self.thread_map)
                && thread_quota_1g_fields_unchanged(old(self).thread_map, self.thread_map)
            ) by {
                reveal(thread_quota_2m_fields_unchanged);
                reveal(thread_quota_1g_fields_unchanged);
            };
            // ---- subsystems_inv ----
            assert(self.subsystems_inv()) by {
                reveal(KernelK::default_pagetable_wf);
                reveal(cpu_array_wf);
                reveal(container_perms_wf);
                reveal(container_tree_fields_wf);
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
                reveal(thread_temp_alloc_empty_unless_wlocked);
                reveal(page_array_wf);
                reveal(thread_perms_wf);
                reveal(thread_free_quota_pending_empty_unless_wlocked);
            };
            // ---- memory_management_inv ----
            assert(self.memory_management_inv()) by {
                assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_4k_map, self.allocator_4k_map);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_2m_map, self.allocator_2m_map);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).allocator_1g_map, self.allocator_1g_map);
                };
                assert(container_page_owner_wf(self.container_map, self.page_array)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(self).container_map, self.container_map, old(self).page_array, self.page_array); };
                assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by {
                    reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf);
                    reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf);
                };
                assert(container_pages_wf(self.page_array, self.container_map)) by { container_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).container_map, self.container_map); };
                assert(process_pages_wf(self.page_array, self.process_map)) by { process_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).process_map, self.process_map); };
                assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_wf);
                    reveal(container_thread_wf);
                    reveal(container_allocator_wf);
                    lemma_thread_effective_quota_4k_fold_change_by_forall(thread_ptr, -1);
                    lemma_thread_effective_quota_4k_fold_sum_eq_forall();
                    lemma_thread_pending_4k_folds_eq_forall(
                        self.container_map,
                        old(self).thread_map,
                        self.thread_map,
                    );
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by {
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields_forall();
                };
                assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by {
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields_forall();
                };
                assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by {
                    reveal(container_allocator_wf);
                };
                assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by {
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(hugepage_2m_wf(self.page_array)) by {
                    hugepage_2m_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array);
                };
                assert(hugepage_1g_wf(self.page_array)) by {
                    hugepage_1g_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array);
                };
                assert(page_pagetable_wf(self.pagetable_map, self.page_array)) by {
                    page_pagetable_wf_preserved_for_nonmapped_page_change(old(self).pagetable_map, self.pagetable_map, old(self).page_array, self.page_array, page_index);
                };
                assert(pagetable_pages_wf(self.pagetable_map, self.page_array)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(self.iommu_table_map, self.page_array)) by {
                    reveal(iommu_table_pages_wf);
                };
                assert(pcid_allocator_pages_wf(
                    self.page_array,
                    self.pcid_allocator_map,
                )) by {
                    pcid_allocator_pages_wf_preserved_for_page_state_eq(old(self).page_array, self.page_array, old(self).pcid_allocator_map, self.pcid_allocator_map);
                };
                assert(thread_pages_wf(self.thread_map, self.page_array)) by { thread_pages_wf_preserved_for_page_state_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array); };
                assert(thread_staged_pages_4k_wf(self.thread_map, self.page_array)) by {
                    reveal(thread_staged_pages_4k_wf);
                    page_ptr_lemma1();
                };
                assert(thread_staged_pages_wf(self.thread_map, self.page_array)) by {
                    thread_staged_pages_2m_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(self).thread_map, self.thread_map, old(self).page_array, self.page_array);
                };
                assert(endpoint_pages_wf(self.endpoint_map, self.page_array)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(self).endpoint_map, self.endpoint_map, old(self).page_array, self.page_array); };
                assert(container_allocator_global_free_4k_page_wf(
                    self.allocator_4k_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_global_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_cpu_cache_free_4k_page_wf(
                    self.allocator_4k_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                    reveal(container_allocator_cpu_cache_free_4k_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                    page_ptr_lemma1();
                };
                assert(container_allocator_free_4k_page_wf(
                    self.allocator_4k_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_4k_page_wf);
                };
                assert(container_allocator_global_free_2m_page_wf(
                    self.allocator_2m_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_global_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_2m_page_wf(
                    self.allocator_2m_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                    reveal(container_allocator_cpu_cache_free_2m_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_2m_page_wf(
                    self.allocator_2m_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_2m_page_wf);
                };
                assert(container_allocator_global_free_1g_page_wf(
                    self.allocator_1g_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_global_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_cpu_cache_free_1g_page_wf(
                    self.allocator_1g_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                    reveal(container_allocator_cpu_cache_free_1g_page_wf);
                    reveal(allocator_free_page_ptrs_wf);
                };
                assert(container_allocator_free_1g_page_wf(
                    self.allocator_1g_map, self.page_array,
                )) by {
                    reveal(container_allocator_free_1g_page_wf);
                };
            };
            // ---- process_management_inv: container_map, thread_map, etc. all byte-equal ----
            assert(self.process_management_inv()) by {
                assert(per_container_process_tree_wf(self.container_map, self.process_map)) by {
                    per_container_process_tree_wf_preserved_for_tree_fields_eq(self.container_map, old(self).process_map, self.process_map);
                };
                assert(process_cpu_wf(self.process_map, self.cpu_array)) by {
                    reveal(process_cpu_wf);
                };
                thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map);
                thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.endpoint_map);
                container_thread_endpoint_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.endpoint_map);
                container_thread_scheduler_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map, self.scheduler_map);
                container_thread_wf_preserved_for_thread_process_management_fields(self.container_map, old(self).thread_map, self.thread_map);
                process_thread_wf_preserved_for_thread_process_management_fields(self.process_map, old(self).thread_map, self.thread_map);
                thread_cpu_wf_preserved_for_thread_process_management_fields(old(self).thread_map, self.thread_map, self.cpu_array);
            };
            assert(self.inv()) by {
                reveal(cpu_dirty_map_contains_container_processes);
                reveal(cpu_not_in_dirty_map_imply_not_in_tlb);
                reveal(cpu_dirty_map_proc_pcid_match);
                reveal(cpu_dirty_map_contains_pagetable_pcid_match);
                reveal(container_cpu_wf);
                reveal(tlb_wf_spec);
            };
            assert(lock_id_aligned(&*self, &*lctx)) by {
                reveal(lock_id_aligned);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

}

} // verus!
