use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::set::lemma_set_remove_len;

verus! {
use crate::*;
use super::mmap_4k_build_structure_spec::*;
#[cfg(verus_keep_ghost)]
use super::mmap_4k_create_entry_install_eof::*;

/// The first absent directory entry on a 4K walk.  Each variant installs
/// exactly one already-initialized child table: L4 installs an L3 table, L3
/// installs an L2 table, and L2 installs the L1 table that will hold the leaf.
#[derive(Clone, Copy)]
pub(super) enum MissingPageTableLevel { L4, L3, L2 }

    /// Consume one staged 4K page and publish it as exactly one page-table
    /// structure page.  The parent pointer is intentionally recovered from the
    /// locked PageTable here rather than accepted from the caller: the semantic
    /// missing level determines both the parent and the PageTable operation.
    ///
    /// Hidden Page/Thread state is made consistent while the krnl phase is
    /// Acquire. The single parent-entry store closes it into Release. Directory
    /// topology is absent from `PageTableU`, while the consumed quota is visible
    /// through `ThreadU` at the following boundary.
    #[verifier::spinoff_prover]
    pub(super) fn install_staged_4k_page_table_page(
        krnl: &mut KernelK, level: MissingPageTableLevel, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
        pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), Tracked(lctx): Tracked<&mut LocalContext>, page_lock_perm: Tracked<&LockPerm>,
        quota_thread_lock_perm: Tracked<&LockPerm>, pagetable_lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            page_ptr_valid(page_ptr),
            old(krnl).thr_mp.dom().contains(quota_thread_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), quota_thread_ptr, container_ptr),
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0,
            pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thread_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= 1,
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
            page_lock_perm.view().state() is WriteLock,
            page_lock_perm.view().thread_id() == old(lctx).thread_id(),
            page_lock_perm.view().lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            quota_thread_lock_perm.view().state() is WriteLock,
            quota_thread_lock_perm.view().thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.view().lock_id() == old(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.view().state() is WriteLock,
            pagetable_lock_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            match level {
                MissingPageTableLevel::L4 => old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is None,
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
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                    ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write, }),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            page_lock_perm.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            quota_thread_lock_perm.view().lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view() == (Thread {
                quota_4k: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k,
                syscall_progress: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(quota_thread_ptr).view()
            }),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view(), level),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_fields_unchanged(&old(krnl).thr_mp.spec_index(quota_thread_ptr).view()),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().state == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, quota_thread_ptr),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, ..*old(krnl) }),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 => final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
    {
        let page_index = page_ptr2page_index(page_ptr);
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(quota_thread_ptr).inv()) by {
            pagetable_perms_wf_map(krnl.pt_mp);
            pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, quota_thread_ptr);
        };
        assert(index_valid(NUM_PAGES, page_index) && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(page_index).view().is_init() && krnl.pg_arr.spec_index(page_index).view().inv()
            && krnl.pg_arr.spec_index(page_index).view().view().inv() && krnl.pg_arr.spec_index(page_index).view().view().addr == page_ptr) by {
            page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index);
        };
        assert(!krnl.pt_mp.spec_index(pagetable_ptr).view().page_closure().contains(page_ptr)) by {
            if krnl.pt_mp.spec_index(pagetable_ptr).view().page_closure().contains(page_ptr) { pagetable_pages_wf_closure_entry_at(krnl.pt_mp, krnl.pg_arr, pagetable_ptr, page_ptr); }
        };

        let parent_page_map_ptr;
        {
            let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_lock_perm);
            parent_page_map_ptr = match level {
                MissingPageTableLevel::L4 => pagetable.cr3,
                MissingPageTableLevel::L3 => pagetable.get_entry_l4(indices.0).unwrap().addr,
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
            page.state = PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_ptr, table_type: PT_TYPE } };
            page_perm_to_page_map(page_ptr, Tracked(page_perm))
        };

        {
            let thread = krnl.thr_mp.borrow_mut_typed(quota_thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), quota_thread_lock_perm);
            thread.temp_alloc_cache_4k = Ghost(thread.temp_alloc_cache_4k.view().remove(page_ptr));
            thread.quota_4k = thread.quota_4k - 1;
            thread.syscall_progress = Ghost(mmap_4k_progress_after_directory(thread.syscall_progress.view(), level));
        } {
            let pagetable = krnl.pt_mp.borrow_mut_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_lock_perm);
            match level {
                MissingPageTableLevel::L4 => { pagetable.create_entry_l4(indices.0, indices.1, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx)); },
                MissingPageTableLevel::L3 => { pagetable.create_entry_l3(indices.0, indices.1, indices.2, parent_page_map_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx)); },
                MissingPageTableLevel::L2 => { pagetable.create_entry_l2(indices.0, indices.1, indices.2, parent_page_map_ptr, page_map_ptr, Tracked(page_map_perm), Tracked(&mut *lctx)); },
            }
        }

        proof {
            lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index));
            assert(install_staged_4k_page_table_page_eof_transition_framing(*old(krnl), *krnl, level, page_ptr, quota_thread_ptr, pagetable_ptr)) by { reveal(install_staged_4k_page_table_page_eof_transition_framing); };
            install_staged_4k_page_table_page_eof(*old(krnl), *krnl, level, page_ptr, quota_thread_ptr, process_ptr, container_ptr, pagetable_ptr);
            held_pagetables_unchanged_except_for_unchanged_except(old(krnl).pt_mp, krnl.pt_mp, old(lctx), pagetable_ptr);
        }
    }
}
