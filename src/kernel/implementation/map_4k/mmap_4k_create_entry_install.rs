use vstd::prelude::*;
use vstd::set::lemma_set_remove_len;

verus! {
use crate::*;

/// The first absent directory entry on a 4K walk.  Each variant installs
/// exactly one already-initialized child table: L4 installs an L3 table, L3
/// installs an L2 table, and L2 installs the L1 table that will hold the leaf.
#[derive(Clone, Copy)]
pub(super) enum MissingPageTableLevel {
    L4,
    L3,
    L2,
}

    /// Consume one staged 4K page and publish it as exactly one page-table
    /// structure page.  The parent pointer is intentionally recovered from the
    /// locked PageTable here rather than accepted from the caller: the semantic
    /// missing level determines both the parent and the PageTable operation.
    ///
    /// Hidden Page/Thread state is made consistent while the krnl phase is
    /// Acquire. The single parent-entry store closes it into Release. Directory
    /// topology is absent from `PageTableU`, so the following boundary stutters.
    pub(super) fn install_staged_4k_page_table_page(krnl: &mut KernelK, level: MissingPageTableLevel, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), Tracked(lctx): Tracked<&mut LocalContext>, page_lock_perm: Tracked<&LockPerm>, quota_thread_lock_perm: Tracked<&LockPerm>, pagetable_lock_perm: Tracked<&LockPerm>)
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            page_ptr_valid(page_ptr),
            old(krnl).thr_mp.dom().contains(quota_thread_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == container_ptr,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0,
            pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thread_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= 1,
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(old(lctx)),
            page_lock_perm.view().state() is WriteLock,
            page_lock_perm.view().thread_id() == old(lctx).thread_id(),
            page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).wlocked_by(old(lctx)),
            quota_thread_lock_perm.view().state() is WriteLock,
            quota_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).pt_mp.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
            pagetable_lock_perm.view().state() is WriteLock,
            pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            match level {
                MissingPageTableLevel::L4 =>
                    old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is Some
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
        ensures
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write, }),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().remove((old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr)))).insert((final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr)))),
            forall|held: HeldLock| #![trigger final(lctx).lock_id_set().contains((held.0, held.1))] held.1 != KernelObjId::Page(page_ptr2page_index(page_ptr)) ==> final(lctx).lock_id_set().contains((held.0, held.1)) == old(lctx).lock_id_set().contains((held.0, held.1)),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().wlocked_by(final(lctx)),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).wlocked_by(final(lctx)),
            final(krnl).pt_mp.spec_index(pagetable_ptr).wlocked_by(final(lctx)),
            final(krnl).thr_mp.lock_id_by_key(quota_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(quota_thread_ptr),
            final(krnl).pt_mp.lock_id_by_key(pagetable_ptr) == old(krnl).pt_mp.lock_id_by_key(pagetable_ptr),
            page_lock_perm.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            quota_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_fields_equal(&old(krnl).thr_mp.spec_index(quota_thread_ptr).view()),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().state == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_entries =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_entries,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().pcid == old(krnl).pt_mp.spec_index(pagetable_ptr).view().pcid,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().cr3 == old(krnl).pt_mp.spec_index(pagetable_ptr).view().cr3,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, quota_thread_ptr),
            final(krnl).it_mp == old(krnl).it_mp,
            final(krnl).irt == old(krnl).irt,
            final(krnl).cpu_arr == old(krnl).cpu_arr,
            final(krnl).ctn_mp == old(krnl).ctn_mp,
            final(krnl).sched_mp == old(krnl).sched_mp,
            final(krnl).pcid_allc_mp == old(krnl).pcid_allc_mp,
            final(krnl).cpu_set_mp == old(krnl).cpu_set_mp,
            final(krnl).prc_mp == old(krnl).prc_mp,
            final(krnl).ep_mp == old(krnl).ep_mp,
            final(krnl).allc_4k_mp == old(krnl).allc_4k_mp,
            final(krnl).allc_2m_mp == old(krnl).allc_2m_mp,
            final(krnl).allc_1g_mp == old(krnl).allc_1g_mp,
            final(krnl).cpu_tlb == old(krnl).cpu_tlb,
            final(krnl).iommu_tlb == old(krnl).iommu_tlb,
            final(krnl).rt_ctn == old(krnl).rt_ctn,
            final(krnl).dflt_pt == old(krnl).dflt_pt,
            held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![quota_thread_ptr]),
            held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![pagetable_ptr]),
            kernel_k_to_kernel_u(*final(krnl)) == kernel_k_to_kernel_u(*old(krnl)),
            pagetable_map_user_view(final(krnl).pt_mp) == pagetable_map_user_view(old(krnl).pt_mp),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0)->0.addr == page_ptr
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) == old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0)
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1)->0.addr == page_ptr
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) == old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0)
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) == old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1)
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == page_ptr
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
    {
        let page_index = page_ptr2page_index(page_ptr);
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(quota_thread_ptr).inv()) by { reveal(pagetable_perms_wf); reveal(thread_perms_wf); };
        assert(index_valid(NUM_PAGES, page_index) && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().is_init() && krnl.pg_arr.spec_index(page_index).view().inv() && krnl.pg_arr.spec_index(page_index).view().view().inv() && krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr) by {
            reveal(page_array_wf);
            page_ptr_valid_imply_page_index_valid();
        };
        assert(!krnl.pt_mp.spec_index(pagetable_ptr).view().page_closure().contains(page_ptr)) by { reveal(pagetable_pages_wf); };

        let parent_page_map_ptr;
        {
            let pagetable = krnl.pt_mp.borrow(pagetable_ptr, pagetable_lock_perm);
            parent_page_map_ptr = match level {
                MissingPageTableLevel::L4 => pagetable.cr3,
                MissingPageTableLevel::L3 =>
                    pagetable.get_entry_l4(indices.0).unwrap().addr,
                MissingPageTableLevel::L2 => {
                    let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
                    pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap().addr
                },
            };
        }

        let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        let (page_map_ptr, Tracked(page_map_perm)) = {
            let page = krnl.pg_arr.borrow_mut_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), page_lock_perm);
            let Tracked(page_perm) = take_perm_4k(page);
            page.state = PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_ptr } };
            page_perm_to_page_map(page_ptr, Tracked(page_perm))
        };

        {
            let thread = krnl.thr_mp.borrow_mut_typed(quota_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), quota_thread_lock_perm);
            thread.temp_alloc_cache_4k = Ghost(thread.temp_alloc_cache_4k.view().remove(page_ptr));
            thread.quota_4k = thread.quota_4k - 1;
        } {
            let pagetable = krnl.pt_mp.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_lock_perm);
            match level {
                MissingPageTableLevel::L4 => { pagetable.create_entry_l4(indices.0,indices.1,page_map_ptr,Tracked(page_map_perm),Tracked(&mut *lctx)); },
                MissingPageTableLevel::L3 => { pagetable.create_entry_l3(indices.0,indices.1,indices.2,parent_page_map_ptr,page_map_ptr,Tracked(page_map_perm),Tracked(&mut *lctx)); },
                MissingPageTableLevel::L2 => { pagetable.create_entry_l2(indices.0,indices.1,indices.2,parent_page_map_ptr,page_map_ptr,Tracked(page_map_perm),Tracked(&mut *lctx)); },
            }
        }

        proof {
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            assert(krnl.subsystems_inv()) by {
                assert(krnl.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
                assert(pagetable_perms_wf(krnl.pt_mp)) by { reveal(pagetable_perms_wf); };
                assert(page_array_wf(krnl.pg_arr)) by { reveal(page_array_wf); };
                assert(thread_perms_wf(krnl.thr_mp)) by {
                    reveal(thread_perms_wf); reveal(thread_temp_alloc_empty_unless_wlocked); reveal(thread_free_quota_pending_empty_unless_wlocked);
                    lemma_set_remove_len(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view(), page_ptr);
                };
            };
            assert(krnl.memory_management_inv()) by {
                assert(cpu_set_pages_wf(krnl.cpu_set_mp, krnl.pg_arr)) by { reveal(cpu_set_pages_wf); };
                assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by {
                    allocator_4k_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_4k_mp, krnl.allc_4k_mp);
                    allocator_2m_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_2m_mp, krnl.allc_2m_mp);
                    allocator_1g_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).allc_1g_mp, krnl.allc_1g_mp);
                };
                assert(container_page_owner_wf(krnl.ctn_mp, krnl.pg_arr)) by { container_page_owner_wf_preserved_for_owning_container_eq(old(krnl).ctn_mp, krnl.ctn_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(hugepage_2m_wf(krnl.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(hugepage_1g_wf(krnl.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr); };
                assert(page_pagetable_wf(krnl.pt_mp, krnl.pg_arr)) by {
                    reveal(pagetable_perms_wf);
                    reveal(mapped_4k_page_pagetable_wf);
                    reveal(mapped_2m_page_pagetable_wf);
                    reveal(mapped_1g_page_pagetable_wf);
                };
                assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { reveal(process_pagetable_match); };
                assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by {
                    reveal(container_process_page_pagetable_wf);
                    reveal(mapped_4k_page_pagetable_wf);
                    reveal(mapped_2m_page_pagetable_wf);
                    reveal(mapped_1g_page_pagetable_wf);
                    reveal(process_pagetable_match);
                    reveal(container_page_owner_wf);
                };
                assert(container_pages_wf(krnl.pg_arr, krnl.ctn_mp)) by { container_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).ctn_mp, krnl.ctn_mp); };
                assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { process_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).prc_mp, krnl.prc_mp); };
                assert(pagetable_pages_wf(krnl.pt_mp, krnl.pg_arr)) by { reveal(pagetable_pages_wf); };
                assert(iommu_table_pages_wf(krnl.it_mp, krnl.pg_arr)) by { reveal(iommu_table_pages_wf); };
                assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(scheduler_pages_wf(krnl.sched_mp, krnl.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(old(krnl).sched_mp, krnl.sched_mp, old(krnl).pg_arr, krnl.pg_arr); };
                assert(pcid_allocator_pages_wf(krnl.pg_arr, krnl.pcid_allc_mp)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(old(krnl).pg_arr, krnl.pg_arr, old(krnl).pcid_allc_mp, krnl.pcid_allc_mp); };
                assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by {
                    assert(thread_staged_pages_4k_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_4k_wf); };
                    assert(thread_staged_pages_2m_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_staged_pages_2m_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
                    assert(thread_staged_pages_1g_wf(krnl.thr_mp, krnl.pg_arr)) by { thread_staged_pages_1g_wf_preserved_for_eq(old(krnl).thr_mp, krnl.thr_mp, old(krnl).pg_arr, krnl.pg_arr); };
                };
                assert(endpoint_pages_wf(krnl.ep_mp, krnl.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(old(krnl).ep_mp, krnl.ep_mp, old(krnl).pg_arr, krnl.pg_arr); };
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
            assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp)) by { reveal(cpu_dirty_map_contains_pagetable_pcid_match); };
            assert(tlb_wf_spec(krnl.cpu_tlb, krnl.pt_mp, krnl.cpu_arr)) by { reveal(tlb_wf_spec); };
            assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl), krnl); };
            held_threads_unchanged_except_for_unchanged_except(old(krnl).thr_mp, krnl.thr_mp, old(lctx), quota_thread_ptr);
            held_pagetables_unchanged_except_for_unchanged_except(old(krnl).pt_mp, krnl.pt_mp, old(lctx), pagetable_ptr);
        }
    }

}
