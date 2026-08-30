use vstd::prelude::*;
use vstd::set::lemma_set_remove_len;

verus! {

use crate::*;

    /// Publish one staged 4K page at a fresh virtual address whose L1 table
    /// already exists.
    ///
    /// The caller holds the page, owner-thread, and target-page-table write
    /// locks. The thread lock is needed because mapping consumes the page from
    /// its temporary allocation cache and charges its quota. Hidden page/thread
    /// metadata is updated while the krnl phase is Acquire; the published PTE
    /// store is the operation that closes the section into Release. The caller
    /// later ends the krnl step, which observes the changed `PageTableU` and
    /// records exactly one non-stuttering transition.
    pub(super) fn map_owned_4k_page(
        krnl: &mut KernelK,
        page_ptr: PagePtr,
        thread_ptr: RwLockThreadPtr,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
        write: bool,
        execute_disable: bool,
        Tracked(lctx): Tracked<&mut LocalContext>,
        page_lock_perm: Tracked<&LockPerm>,
        thread_lock_perm: Tracked<&LockPerm>,
        pagetable_lock_perm: Tracked<&LockPerm>,
    )
        requires
            staged_4k_page_op_requires(old(krnl), old(lctx), page_ptr, thread_ptr, pagetable_ptr, va, page_lock_perm.view(), thread_lock_perm.view(), pagetable_lock_perm.view()),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va) == false,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) is Some,
        ensures
            staged_4k_page_op_ensures(final(krnl), final(lctx), old(krnl), old(lctx), page_ptr, thread_ptr, pagetable_ptr, page_lock_perm.view(), thread_lock_perm.view(), pagetable_lock_perm.view()),
            kernel_k_to_kernel_u(*final(krnl)) != kernel_k_to_kernel_u(*old(krnl)),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == PageState::Mapped4k,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k.view() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().perm_4k.view(),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().mappings() == Set::empty().insert((pagetable_ptr, va)),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count == 1,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().insert(va, MapEntry { addr: page_ptr, present: true, write, execute_disable, owning_container: Ghost(final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container), }),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3) == Some(PageEntry { addr: page_ptr, perm: PageEntryPerm { present: true, ps: false, write, execute_disable, user: true, kernel_present: true, }, }),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(spec_va2index(va).0) == old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(spec_va2index(va).0),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1) == old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(spec_va2index(va).0, spec_va2index(va).1),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) == old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(krnl).pt_mp.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                ==> final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().page_closure() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().page_closure(),
    {
        let page_index = page_ptr2page_index(page_ptr);
        let indices = va2index(va);
        assert(
            krnl.pt_mp.perms_wf()
            && krnl.pt_mp.spec_index(pagetable_ptr).inv()
            && krnl.pg_arr.inv()
            && krnl.pg_arr.spec_index(page_index).view().inv()
            && krnl.thr_mp.perms_wf()
            && krnl.thr_mp.spec_index(thread_ptr).inv()
        ) by { reveal(pagetable_perms_wf); reveal(page_array_wf); reveal(thread_perms_wf); };
        let target_l1_ptr;
        {
            let pagetable = krnl.pt_mp.borrow(pagetable_ptr, pagetable_lock_perm);
            let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
            let l3_entry = pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap();
            let l2_entry = pagetable.get_entry_l2(indices.0, indices.1, indices.2, &l3_entry).unwrap();
            target_l1_ptr = l2_entry.addr;
        }

        let page_owner;
        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        {
            let page = krnl.pg_arr.borrow_mut(page_index, Tracked(&*lctx), page_lock_perm);
            page_owner = page.owning_container;
            page.state = PageState::Mapped4k;
            page.mappings = Ghost(Set::empty().insert((pagetable_ptr, va)));
            page.ref_count = 1;
        } {
            let thread = krnl.thr_mp.borrow_mut(thread_ptr, Tracked(&*lctx), thread_lock_perm);
            thread.temp_alloc_cache_4k = Ghost(thread.temp_alloc_cache_4k.view().remove(page_ptr));
            thread.quota_4k = thread.quota_4k - 1;
        }
        let target_entry = MapEntry {
            addr: page_ptr,
            present: true,
            write,
            execute_disable,
            owning_container: Ghost(page_owner),
        };
        proof {
            assert(spec_index2va(indices) == va) by { spec_va_4k_index_roundtrip(); };
        }
        {
            let pagetable = krnl.pt_mp.borrow_mut(pagetable_ptr, Tracked(&mut *lctx), pagetable_lock_perm);
            pagetable.map_4k_page(indices.0, indices.1, indices.2, indices.3, target_l1_ptr, &target_entry, Tracked(&mut *lctx));
        }

        proof {
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            assert(krnl.subsystems_inv()) by {
                assert(krnl.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
                assert(pagetable_perms_wf(krnl.pt_mp)) by { reveal(pagetable_perms_wf); };
                assert(page_array_wf(krnl.pg_arr)) by { reveal(page_array_wf); };
                assert(thread_perms_wf(krnl.thr_mp)) by {
                    reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked);
                    lemma_set_remove_len(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), page_ptr);
                };
            };
            assert(krnl.memory_management_inv()) by {
                assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
                };
                assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(hugepage_2m_wf(krnl.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(hugepage_1g_wf(krnl.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by { page_pagetable_wf_preserved_for_4k_mapping_insert(old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, pagetable_ptr, page_ptr, va); };
                assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by {
                    reveal(process_thread_wf); reveal(process_pagetable_match);
                    container_process_page_pagetable_wf_preserved_for_4k_mapping_insert(krnl.ctn_mp, krnl.prc_mp, old(krnl).pt_mp, krnl.pt_mp, old(krnl).pg_arr, krnl.pg_arr, pagetable_ptr, page_ptr, va);
                };
                assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
                assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
                assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
                assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
                assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                    reveal(thread_staged_pages_4k_wf);
                    thread_staged_pages_2m_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                    thread_staged_pages_1g_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr);
                };
                assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
                assert(container_process_allocator_quota_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_4k_mp);
                    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_2m_mp);
                    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_1g_mp);
                };
                assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { container_allocator_free_4k_page_wf_preserved_for_nonfree_page_change(krnl.allc_4k_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
                assert(container_allocator_free_2m_page_wf(krnl.allc_2m_mp, krnl.pg_arr)) by { container_allocator_free_2m_page_wf_preserved_for_nonfree_page_change(krnl.allc_2m_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
                assert(container_allocator_free_1g_page_wf(krnl.allc_1g_mp, krnl.pg_arr)) by { container_allocator_free_1g_page_wf_preserved_for_nonfree_page_change(krnl.allc_1g_mp, old(krnl).pg_arr, krnl.pg_arr, page_index); };
            };
            assert(krnl.process_management_inv()) by {
                assert(thread_caller_callee_wf(krnl.thr_mp)) by {
                    assert(thread_process_management_fields_unchanged(old(krnl).thr_mp, krnl.thr_mp)) by { reveal(thread_perms_wf); };
                    thread_caller_callee_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp);
                };
                assert(thread_endpoint_ref_counter_wf(krnl.thr_mp, krnl.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp); };
                assert(thread_endpoint_queue_wf(krnl.thr_mp, krnl.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp); };
                assert(container_thread_endpoint_wf(krnl.ctn_mp, krnl.thr_mp, krnl.ep_mp)) by { container_thread_endpoint_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp); };
                assert(container_thread_scheduler_wf(krnl.ctn_mp, krnl.thr_mp, krnl.sched_mp)) by { container_thread_scheduler_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.sched_mp); };
                assert(container_thread_wf(krnl.ctn_mp, krnl.thr_mp)) by { container_thread_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp); };
                assert(process_thread_wf(krnl.prc_mp, krnl.thr_mp)) by { process_thread_wf_preserved_for_thread_process_management_fields(krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp); };
                assert(thread_cpu_wf(krnl.thr_mp, krnl.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.cpu_arr); };
            };
            assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
            assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr)) by { tlb_wf_spec_preserved_for_4k_mapping_insert(krnl.cpu_tlb, krnl.cpu_arr, old(krnl).pt_mp, krnl.pt_mp, pagetable_ptr, va); };
            assert(lock_id_aligned(krnl, &*lctx)) by { reveal(lock_id_aligned); };
            assert({
                let process_ptr = krnl.thr_mp.spec_index(thread_ptr)
                    .view().owning_proc;
                &&& kernel_k_to_kernel_u(*old(krnl)).process_map.dom()
                    .contains(process_ptr)
                &&& kernel_k_to_kernel_u(*krnl).process_map.dom()
                    .contains(process_ptr)
                &&& !kernel_k_to_kernel_u(*old(krnl)).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(va)
                &&& kernel_k_to_kernel_u(*krnl).process_map
                    .spec_index(process_ptr).pagetable.mapping_4k.dom()
                    .contains(va)
            }) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
        }
    }

}
