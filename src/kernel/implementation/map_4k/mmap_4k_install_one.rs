use vstd::prelude::*;
use crate::*;
use super::mmap_4k_create_entry_install::{
    install_staged_4k_page_table_page,
    MissingPageTableLevel,
};

verus! {
    /// Allocate and install one missing directory page, then end the krnl
    /// section.  Directory topology is absent from `PageTableU`, so this
    /// boundary is a stuttering user step.
    pub(super) fn install_one_mmap_4k_directory_page(krnl: &mut KernelK, level: MissingPageTableLevel, alloc_ptr_4k: RwLockPageAllocatorPtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>)
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).thr_mp.dom().contains(quota_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == container_ptr,
            ((old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)),
            quota_thread_lock_perm.state() is WriteLock,
            quota_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(quota_thread_ptr)) >= 1,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
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
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
        ensures
            forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            final(krnl).prc_mp.dom().contains(process_ptr),
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            final(krnl).thr_mp.dom().contains(quota_thread_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == container_ptr,
            ((final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)),
            quota_thread_lock_perm.thread_id() == final(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            final(lctx).page_lock_map().dom().is_empty(),
            final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR) ==> final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![quota_thread_ptr]),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![pagetable_ptr]),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().state == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            final(krnl).pt_mp.spec_index(pagetable_ptr).inv(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().user_view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().user_view(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
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
                MissingPageTableLevel::L2 =>
                    final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
    {
        proof {
            broadcast use group_held_objects_unchanged_transitive;
        }
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, quota_thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm));
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr));
        proof {
            assert(krnl.prc_mp.dom().contains(process_ptr) && krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr && krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr) by {  reveal(process_thread_wf); reveal(process_pagetable_match); };
        }
        install_staged_4k_page_table_page(krnl, level, page_ptr, quota_thread_ptr, process_ptr, container_ptr, pagetable_ptr, indices, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm));
        let ghost installed_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr));
        krnl.wunlock_page(page_ptr2page_index(page_ptr), Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedHeldLock {
                    lock_id: staged_page_lock_id, mode: TypedLockMode::Write,
                }, TypedHeldLock {
                    lock_id: installed_page_lock_id, mode: TypedLockMode::Write,
                });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedHeldLock {
                    lock_id: installed_page_lock_id, mode: TypedLockMode::Write,
                });
            };

            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
            assert(krnl.prc_mp.dom().contains(process_ptr) && ((krnl.thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && krnl.thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write))) by {  reveal(process_thread_wf); };
            assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { reveal(container_allocator_wf); };
            assert(krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.pt_mp.spec_index(pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
            if old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR) {
                assert(lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by { broadcast use held_lock_major_lt_preserved_for_typed_maps_unchanged; };
            }
        }
    }

} // verus!
