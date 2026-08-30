use super::*;
use super::allocate_free_4k_impl_basd::allocator_objects_unlocked_except_cache_pool;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {

    // ================================================================
    // pop_stage_4k_page: cache[cpu_id] + thread are already write-locked and
    // the cache is non-empty. Peek the head, lock the page slot, pop the head,
    // retype it Free4k{PreCpuCache}→Owned4k, stage it in the thread's
    // temp_alloc_cache_4k, decrement the allocator's total_free_pages. Leaves
    // page + cache still write-locked; re-establishes inv().
    // ================================================================
    pub(super) fn pop_stage_4k_page(
        krnl: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_lock_perm): Tracked<&LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(krnl).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            allocator_objects_unlocked_except_cache_pool(old(krnl).allc_4k_mp, alloc_ptr_4k, old(lctx).thread_id()),
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == old(lctx).thread_id(),
            cache_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
            lock_id_aligned(old(krnl), old(lctx)),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(krnl).inv(),
            allocator_objects_unlocked_except_cache_pool(final(krnl).allc_4k_mp, alloc_ptr_4k, final(lctx).thread_id()),
            forall|other_cpu: CpuId|
                #![trigger final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k)
                    .cpu_caches.spec_index(other_cpu).view()
                    .locked_by_thread(final(lctx).thread_id())]
                index_valid(NUM_CPUS, other_cpu)
                ==> final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(final(lctx).thread_id())
                    == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k)
                        .cpu_caches.spec_index(other_cpu).view()
                        .locked_by_thread(old(lctx).thread_id()),
            page_ptr_valid(ret.0),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state is Free4k,
            !old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(ret.0),
            final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, alloc_ptr_4k),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
            final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(ret.0)),
            // ---- user view unchanged: staging is krnl-internal ----
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            // ---- cache + thread lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            cache_lock_perm.lock_id() == final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).lock_id(),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.entries_unchanged_except(&old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches, cpu_id),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().locked_by_thread(final(lctx).thread_id()),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
                (old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(final(lctx).thread_id())),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)]
                #![trigger final(krnl).thr_mp.spec_index(t)]
                t != thread_ptr
                    && old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        == old(krnl).thr_mp.spec_index(t)
                    && final(krnl).thr_mp.lock_id_by_key(t)
                        == old(krnl).thr_mp.lock_id_by_key(t),
            final(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).locked_by_thread(final(lctx).thread_id()),
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            // ---- page slot left write-locked, perm handed back ----
            index_valid(NUM_PAGES, page_ptr2page_index(ret.0)),
            page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(ret.0)]),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locked_by_thread(final(lctx).thread_id()),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            // ---- held-lock set: gained exactly the page slot ----
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), KernelObjId::Page(page_ptr2page_index(ret.0)))),
            lock_id_aligned(final(krnl), final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(krnl).ctn_mp == old(krnl).ctn_mp,
            final(krnl).prc_mp == old(krnl).prc_mp,
            final(krnl).pt_mp == old(krnl).pt_mp,
            final(krnl).sched_mp == old(krnl).sched_mp,
            final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
            final(krnl).ep_mp == old(krnl).ep_mp,
            final(krnl).irt == old(krnl).irt,
            final(krnl).it_mp == old(krnl).it_mp,
            final(krnl).iommu_tlb == old(krnl).iommu_tlb,
            final(krnl).cpu_arr == old(krnl).cpu_arr,
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool,
    {
        assert(
            krnl.allc_4k_mp.perms_wf()
            && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf()
            && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.inv()
            && krnl.thr_mp.perms_wf()
            && krnl.pg_arr.inv()
        ) by { reveal(allocator_perms_wf); reveal(thread_perms_wf); reveal(page_array_wf); };
        let cache_ref = krnl.allc_4k_mp.borrow_cache(alloc_ptr_4k, cpu_id, Tracked(cache_lock_perm));
        let (node_addr, page_ptr) = cache_ref.linked_list.peek_head();
        assert(page_ptr_valid(page_ptr)) by { reveal(allocator_perms_wf); reveal(allocator_free_page_ptrs_wf); };
        let page_index = page_ptr2page_index(page_ptr);
        assert({
            &&& index_valid(NUM_PAGES, page_index)
            &&& old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k)
                .cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)
            &&& lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(page_index))
        }) by {
            page_ptr_valid_imply_page_index_valid();
            reveal(LinkedList::wf_value_list); reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf);
        };
        // Lock the page slot after deriving its ordering id from the cache head.
        let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let (node_addr2, Tracked(node_perm)) = {
            let alloc_mut = krnl.allc_4k_mp.borrow_mut(alloc_ptr_4k);
            alloc_mut.pop_cache_page(cpu_id, Tracked(&*lctx), Tracked(cache_lock_perm))
        };
        assert(node_addr2 == node_addr) by { old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches.spec_index(cpu_id).view().view().linked_list.lemma_value_addr_unique(node_addr, node_addr2); };
        assert(
            krnl.pg_arr.inv()
            && krnl.thr_mp.perms_wf()
            && krnl.thr_mp.spec_index(thread_ptr).is_init()
        ) by { reveal(page_array_wf); reveal(thread_perms_wf); };
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        {
            let mut page = krnl.pg_arr.borrow_mut(page_index, Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(
                page.state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr_4k),
                    state: FreePageAllocatorState::PreCpuCache { cpu_id },
                }
                && page.owning_container == container_ptr
            ) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(container_allocator_wf); };
            page.state = PageState::Owned4k { thread_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(LinkedList::wf_map); };
            page.free_list_node_storage.put(Tracked(node_perm));
        } {
            let thread_mut = krnl.thr_mp.borrow_mut(thread_ptr, Tracked(&*lctx), Tracked(thread_lock_perm));
            thread_mut.temp_alloc_cache_4k = Ghost(thread_mut.temp_alloc_cache_4k.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            assert(lock_id_aligned(krnl, &*lctx)) by {
                assert(
                    PAGE_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR
                        && IOMMU_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR
                ) by (compute);
                reveal(lock_id_aligned);
                lock_id_fields_eq_imply_eq();
            };
        }
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            reveal(thread_staged_pages_4k_wf);
            if old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { thread_ptr }) by { reveal(thread_staged_pages_4k_wf); };
            }
        };
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
        }
        proof {
            // ---- subsystems_inv ----
            assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_array_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf); reveal(allocator_perms_wf); reveal(process_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
            // ---- memory_management_inv ----
            assert(krnl.memory_management_inv()) by {
                assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
                };
                assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
                assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
                assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
                assert(container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp)) by {
                    reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
                    lemma_thread_effective_quota_4k_fold_change_by_forall(thread_ptr, -1);
                    lemma_thread_effective_quota_4k_fold_sum_eq_forall();
                    lemma_thread_pending_4k_folds_eq_forall(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp);
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_2m_mp)) by { container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_2m_mp); };
                assert(container_process_allocator_quota_1g_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp)) by { container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_1g_mp); };
                assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
                assert(allocator_free_page_ptrs_wf(krnl.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
                assert(hugepage_2m_wf(krnl.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(hugepage_1g_wf(krnl.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
                assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
                assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
                assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(thread_staged_pages_4k_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
                assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                    thread_staged_pages_2m_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                };
                assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(container_allocator_global_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by {
                    reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf);
                    page_ptr_valid_imply_page_index_valid();
                };
                assert(container_allocator_cpu_cache_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by {
                    reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); };
                assert(container_allocator_global_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_cpu_cache_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); };
                assert(container_allocator_global_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_cpu_cache_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); };
            };
            // ---- process_management_inv: container_map, thread_map, etc. all byte-equal ----
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
        assert(krnl.thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view())) by { reveal(Thread::stable_allocation_root_equal); reveal(thread_perms_wf); };
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
        krnl: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        container_ptr: RwLockContainerPtr,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
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
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.wlocked_by(old(lctx)),
            old(lctx).lock_id_set().contains((old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(), KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, alloc_ptr_4k))),
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().view().len() > 0,
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().len() > 0,
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            page_objects_unlocked(old(krnl).pg_arr, old(lctx).thread_id()),
            lock_id_aligned(old(krnl), old(lctx)),
            old(lctx).held_lock_majors_lt(FREE_PAGE_LOCK_MAJOR),
        ensures
            final(krnl).inv(),
            page_ptr_valid(ret.0),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state is Free4k,
            !old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(ret.0),
            final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
            final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, alloc_ptr_4k),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota,
            final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
            final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(ret.0)),
            // ---- user view unchanged: staging is krnl-internal ----
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            // ---- global_pool + process lock state preserved, phase still Acquire ----
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            global_pool_lock_perm.lock_id() == final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.lock_id(),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).cpu_caches,
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.wlocked_by(final(lctx)),
            final(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.locked_by_thread(final(lctx).thread_id()),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(krnl).thr_mp.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
                (old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(final(lctx).thread_id())),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)]
                #![trigger final(krnl).thr_mp.spec_index(t)]
                t != thread_ptr
                    && old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        == old(krnl).thr_mp.spec_index(t)
                    && final(krnl).thr_mp.lock_id_by_key(t)
                        == old(krnl).thr_mp.lock_id_by_key(t),
            final(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).locked_by_thread(final(lctx).thread_id()),
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            // ---- page slot left write-locked, perm handed back ----
            index_valid(NUM_PAGES, page_ptr2page_index(ret.0)),
            page_objects_unlocked_except(final(krnl).pg_arr, final(lctx).thread_id(), set![page_ptr2page_index(ret.0)]),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().wlocked_by(final(lctx)),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locked_by_thread(final(lctx).thread_id()),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().being_killed() == false,
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().locking_thread()->Write_lock_id,
            // ---- held-lock set: gained exactly the page slot ----
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(ret.0)), KernelObjId::Page(page_ptr2page_index(ret.0)))),
            lock_id_aligned(final(krnl), final(lctx)),
            // ---- staging: ret staged Owned4k; 4k cache gained exactly ret, 2m/1g caches + nominal quota untouched ----
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().insert(ret.0),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().state == (PageState::Owned4k{ thread_ptr }),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(ret.0)).view().view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view()),
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors == old(krnl).thr_mp.spec_index(thread_ptr).view().endpoint_descriptors,
            // ---- container_map + scheduler_map untouched (staging never writes them) ----
            final(krnl).ctn_mp == old(krnl).ctn_mp,
            final(krnl).prc_mp == old(krnl).prc_mp,
            final(krnl).pt_mp == old(krnl).pt_mp,
            final(krnl).sched_mp == old(krnl).sched_mp,
            final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
            final(krnl).ep_mp == old(krnl).ep_mp,
            final(krnl).irt == old(krnl).irt,
            final(krnl).it_mp == old(krnl).it_mp,
            final(krnl).iommu_tlb == old(krnl).iommu_tlb,
            final(krnl).cpu_arr == old(krnl).cpu_arr,
    {
        assert(
            krnl.allc_4k_mp.perms_wf()
            && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf()
            && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.inv()
            && krnl.thr_mp.perms_wf()
            && krnl.pg_arr.inv()
        ) by { reveal(allocator_perms_wf); reveal(thread_perms_wf); reveal(page_array_wf); };
        let poll_ref = krnl.allc_4k_mp.borrow_global_pool(alloc_ptr_4k, Tracked(global_pool_lock_perm));
        let (node_addr, page_ptr) = poll_ref.peek_head();
        assert(page_ptr_valid(page_ptr)) by { reveal(allocator_perms_wf); reveal(allocator_free_page_ptrs_wf); };
        let page_index = page_ptr2page_index(page_ptr);
        assert({
            &&& index_valid(NUM_PAGES, page_index)
            &&& old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k)
                .global_pool.view().view().contains(page_ptr)
            &&& krnl.pg_arr.spec_index(page_index).view().view().state
                == PageState::Free4k {
                allocator_ptr: Ghost(alloc_ptr_4k),
                state: FreePageAllocatorState::GlobalList,
            }
            &&& lctx.lock_id_acyclic(krnl.pg_arr.lock_id_by_index(page_index))
        }) by {
            page_ptr_valid_imply_page_index_valid();
            reveal(LinkedList::wf_value_list); reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf);
        };
        // Lock the page slot after deriving its ordering id from the pool head.
        let Tracked(page_lock_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));

        // Mutation block: pop + decrement (PageAllocator::inv() re-established by
        // the wrapper), retype Free4k→Owned4k, stage.
        let (node_addr2, Tracked(node_perm)) = {
            let alloc_mut = krnl.allc_4k_mp.borrow_mut(alloc_ptr_4k);
            alloc_mut.pop_global_pool_page(Tracked(&*lctx), Tracked(global_pool_lock_perm))
        };
        assert(node_addr2 == node_addr) by { old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).global_pool.view().linked_list.lemma_value_addr_unique(node_addr, node_addr2); };
        assert(
            krnl.pg_arr.inv()
            && krnl.thr_mp.perms_wf()
            && krnl.thr_mp.spec_index(thread_ptr).is_init()
        ) by { reveal(page_array_wf); reveal(thread_perms_wf); };
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);

        {
            let mut page = krnl.pg_arr.borrow_mut(page_index, Tracked(&*lctx), Tracked(&page_lock_perm));
            assert(
                page.state == PageState::Free4k {
                    allocator_ptr: Ghost(alloc_ptr_4k),
                    state: FreePageAllocatorState::GlobalList,
                }
                && page.owning_container == container_ptr
            ) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_wf); };
            page.state = PageState::Owned4k { thread_ptr };
            assert(node_addr == page.free_list_node_storage.addr()) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(LinkedList::wf_map); };
            page.free_list_node_storage.put(Tracked(node_perm));
        } {
            let thread_mut = krnl.thr_mp.borrow_mut(thread_ptr, Tracked(&*lctx), Tracked(thread_lock_perm));
            thread_mut.temp_alloc_cache_4k = Ghost(thread_mut.temp_alloc_cache_4k.view().insert(page_ptr));
        }
        proof {
            lctx.enter_kernel_view_release();
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
        }
        // ---- staging delta: page_ptr fresh in temp_alloc_cache_4k ⟹ effective_quota_4k −1 ----
        assert(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) == false) by {
            reveal(thread_staged_pages_4k_wf);
            if old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr) {
                assert(old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state
                    == PageState::Owned4k { thread_ptr }) by { reveal(thread_staged_pages_4k_wf); };
            }
        };
        proof {
            // ---- user view unchanged: only page_array / temp_alloc / total moved ----
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
        }
        proof {
            // ---- subsystems_inv ----
            assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(cpu_array_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf); reveal(allocator_perms_wf); reveal(process_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(page_array_wf); reveal(thread_perms_wf); reveal(thread_free_quota_pending_empty_unless_wlocked); };
            // ---- memory_management_inv ----
            assert(krnl.memory_management_inv()) by {
                assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
                };
                assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { reveal(container_process_page_pagetable_wf); reveal(container_process_wf); reveal(process_pagetable_match); reveal(container_page_owner_wf); reveal(mapped_4k_page_pagetable_wf); reveal(mapped_2m_page_pagetable_wf); reveal(mapped_1g_page_pagetable_wf); };
                assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
                assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
                assert(container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp)) by {
                    reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
                    lemma_thread_effective_quota_4k_fold_change_by_forall(thread_ptr, -1);
                    lemma_thread_effective_quota_4k_fold_sum_eq_forall();
                    lemma_thread_pending_4k_folds_eq_forall(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp);
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_2m_mp)) by { container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_2m_mp); };
                assert(container_process_allocator_quota_1g_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp)) by { container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_1g_mp); };
                assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
                assert(allocator_free_page_ptrs_wf(krnl.allc_4k_mp)) by { reveal(allocator_free_page_ptrs_wf); };
                assert(hugepage_2m_wf(krnl.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(hugepage_1g_wf(krnl.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by { page_pagetable_wf_preserved_for_nonmapped_page_change(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
                assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
                assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
                assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(thread_staged_pages_4k_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
                assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                    thread_staged_pages_2m_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                };
                assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(container_allocator_global_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by {
                    reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf); reveal(LinkedList::value_list_unique);
                    seq_skip_lemma::<PagePtr>();
                };
                assert(container_allocator_cpu_cache_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by {
                    reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); reveal(allocator_free_page_ptrs_wf);
                    page_ptr_valid_imply_page_index_valid();
                    page_ptr2page_index_injective();
                };
                assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); };
                assert(container_allocator_global_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_global_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_cpu_cache_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); reveal(container_allocator_cpu_cache_free_2m_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { reveal(container_allocator_free_2m_page_wf); };
                assert(container_allocator_global_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_global_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_cpu_cache_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); reveal(container_allocator_cpu_cache_free_1g_page_wf); reveal(allocator_free_page_ptrs_wf); };
                assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { reveal(container_allocator_free_1g_page_wf); };
            };
            // ---- process_management_inv: container_map, thread_map, etc. all byte-equal ----
            assert(krnl.process_management_inv()) by {
                assert(thread_caller_callee_wf(krnl.thr_mp)) by {
                    assert(thread_process_management_fields_unchanged(old(krnl).thr_mp, krnl.thr_mp)) by { reveal(thread_perms_wf); };
                    thread_caller_callee_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp);
                };
                assert(per_container_process_tree_wf(krnl.ctn_mp, krnl.prc_mp)) by { per_container_process_tree_wf_preserved_for_tree_fields_eq(krnl.ctn_mp, old(krnl).prc_mp, krnl.prc_mp); };
                assert(process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)) by { reveal(process_cpu_wf); };
                thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                container_thread_endpoint_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
                container_thread_scheduler_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.sched_mp);
                container_thread_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp);
                process_thread_wf_preserved_for_thread_process_management_fields(krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp);
                thread_cpu_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.cpu_arr);
            };
        }
        assert(krnl.thr_mp.spec_index(thread_ptr).view().stable_allocation_root_equal(&old(krnl).thr_mp.spec_index(thread_ptr).view())) by { reveal(Thread::stable_allocation_root_equal); reveal(thread_perms_wf); };
        assert(lock_id_aligned(krnl, &*lctx)) by { reveal(lock_id_aligned); };
        (page_ptr, Tracked(page_lock_perm))
    }

} // verus!
