use vstd::prelude::*;
use crate::*;
verus! {

    pub open spec fn kernel_u_only_process_quota_4k_changed(
        old_u: KernelU,
        new_u: KernelU,
        process_ptr: RwLockProcessPtr,
        delta: int,
    ) -> bool {
        &&& new_u.cpu_array == old_u.cpu_array
        &&& new_u.process_map.dom() == old_u.process_map.dom()
        &&& old_u.process_map.dom().contains(process_ptr)
        &&& new_u.process_map.spec_index(process_ptr).quota_4k as int
                == old_u.process_map.spec_index(process_ptr).quota_4k as int + delta
        &&& new_u.process_map.spec_index(process_ptr).zombie == old_u.process_map.spec_index(process_ptr).zombie
        &&& new_u.process_map.spec_index(process_ptr).pagetable      == old_u.process_map.spec_index(process_ptr).pagetable
        &&& new_u.process_map.spec_index(process_ptr).iommu_table    == old_u.process_map.spec_index(process_ptr).iommu_table
        &&& new_u.process_map.spec_index(process_ptr).quota_2m       == old_u.process_map.spec_index(process_ptr).quota_2m
        &&& new_u.process_map.spec_index(process_ptr).quota_1g       == old_u.process_map.spec_index(process_ptr).quota_1g
        &&& new_u.process_map.spec_index(process_ptr).parent         == old_u.process_map.spec_index(process_ptr).parent
        &&& new_u.process_map.spec_index(process_ptr).children       == old_u.process_map.spec_index(process_ptr).children
        &&& new_u.process_map.spec_index(process_ptr).depth          == old_u.process_map.spec_index(process_ptr).depth
        &&& new_u.process_map.spec_index(process_ptr).uppertree_seq  == old_u.process_map.spec_index(process_ptr).uppertree_seq
        &&& new_u.process_map.spec_index(process_ptr).subtree_set    == old_u.process_map.spec_index(process_ptr).subtree_set
        &&& new_u.process_map.spec_index(process_ptr).owned_threads  == old_u.process_map.spec_index(process_ptr).owned_threads
        &&& new_u.process_map.spec_index(process_ptr).killed         == old_u.process_map.spec_index(process_ptr).killed
        &&& forall|p: RwLockProcessPtr|
            #![trigger new_u.process_map.spec_index(p)]
            old_u.process_map.dom().contains(p) && p != process_ptr ==>
                new_u.process_map.spec_index(p) == old_u.process_map.spec_index(p)
    }

    pub(super) fn commit_alloc_quota_4k(
        krnl: &mut KernelK,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        cpu_id: CpuId,
        container_ptr: RwLockContainerPtr,
        process_ptr: RwLockProcessPtr,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        alloc_amount: usize,
        cpu_lock_perm: Tracked<LockPerm>,
        container_lock_perm: Tracked<LockPerm>,
        quota_lock_perm: Tracked<LockPerm>,
        process_lock_perm: Tracked<LockPerm>,
    )
        requires
            old(krnl).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_published[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            container_lock_perm.view().state() is WriteLock,
            container_lock_perm.view().thread_id() == old(lctx).thread_id(),
            container_lock_perm.view().lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            old(krnl).ctn_mp.spec_index(container_ptr).being_killed() == false,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota.is_init(),
            quota_lock_perm.view().state() is WriteLock,
            quota_lock_perm.view().thread_id() == old(lctx).thread_id(),
            quota_lock_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), alloc_ptr_4k, TypedLockMode::Write),
            old(krnl).prc_mp.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            old(krnl).prc_mp.spec_index(process_ptr).being_killed() == false,
            old(krnl).prc_mp.spec_index(process_ptr).view().owned_threads.view().len() != 0,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
            old(lctx).container_lock_map().dom() =~= set![container_ptr],
            old(lctx).process_lock_map().dom() =~= set![process_ptr],
            old(lctx).thread_lock_map().dom().is_empty(),
            old(lctx).endpoint_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).pcid_allocator_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom().is_empty(),
            old(lctx).iommu_table_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_4k_lock_map().dom() =~= set![alloc_ptr_4k],
            old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
            old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
            old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(krnl).ctn_mp.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            alloc_amount <= usize::MAX - old(krnl).prc_mp.spec_index(process_ptr).view().quota_4k,
            old(krnl).allc_4k_mp.spec_index(alloc_ptr_4k).quota.view().value >= alloc_amount,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(lctx).no_locks_held(),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            final(steps).steps == record_user_view_change(old(steps).steps,kernel_k_to_kernel_u(*old(krnl)),kernel_k_to_kernel_u(*final(krnl))),
            alloc_amount == 0 ==> final(steps).steps == old(steps).steps,
            alloc_amount > 0 ==> kernel_u_only_process_quota_4k_changed(kernel_k_to_kernel_u(*old(krnl)),kernel_k_to_kernel_u(*final(krnl)),
                process_ptr,alloc_amount as int),
    {

        proof {
            assert(
                krnl.prc_mp.perms_wf()
                && krnl.allc_4k_mp.perms_wf()
                && krnl.prc_mp.spec_index(process_ptr).is_init()
            ) by { reveal(process_perms_wf); reveal(allocator_perms_wf); };
        }
        {
            let process_mut = krnl.prc_mp.borrow_mut_typed(process_ptr, Ghost(lctx.process_lock_map()), Tracked(&*lctx), Tracked(process_lock_perm.borrow()));
            process_mut.quota_4k = process_mut.quota_4k + alloc_amount;
        } {
            let quota_mut = krnl.allc_4k_mp.borrow_mut_quota_typed(alloc_ptr_4k, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_lock_perm.borrow()));
            quota_mut.value = quota_mut.value - alloc_amount;
        }

        proof {
            assert(allocator_perms_wf(krnl.allc_4k_mp) && krnl.allc_4k_mp.spec_index(alloc_ptr_4k).wf()) by { reveal(allocator_perms_wf); };
            assert(krnl.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); reveal(process_perms_wf); };
            assert(krnl.memory_management_inv()) by {
                assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { lemma_allocator_pages_wf_preserved_for_allocator_quota_value_framed_fields_forall(); };
                assert(container_process_page_pagetable_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr)) by { lemma_container_process_page_pagetable_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(process_pages_wf(krnl.pg_arr, krnl.prc_mp)) by { lemma_process_pages_wf_preserved_for_process_domain_eq_forall(); };
                assert(container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp)) by {
                    reveal(container_process_allocator_quota_4k_wf); reveal(container_process_wf); reveal(container_allocator_wf);
                    lemma_process_effective_quota_4k_fold_change_by_forall(process_ptr, alloc_amount as int);
                    lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(krnl.ctn_mp, krnl.prc_mp,krnl.thr_mp, krnl.allc_2m_mp)) by {
                    container_process_allocator_quota_2m_wf_preserved_for_process_2m_fields(
                        krnl.ctn_mp, krnl.thr_mp,krnl.allc_2m_mp, old(krnl).prc_mp, krnl.prc_mp,);
                };
                assert(container_process_allocator_quota_1g_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp,)) by {
                    container_process_allocator_quota_1g_wf_preserved_for_process_1g_fields(
                        krnl.ctn_mp, krnl.thr_mp, krnl.allc_1g_mp,old(krnl).prc_mp, krnl.prc_mp,);
                };
                assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { lemma_container_allocator_wf_preserved_for_allocator_quota_value_framed_fields_forall(); };
                assert(allocator_free_page_ptrs_wf(krnl.allc_4k_mp)) by { lemma_allocator_free_page_ptrs_wf_preserved_for_pool_and_cache_contents_forall(); };
                assert(process_pagetable_match(krnl.prc_mp, krnl.pt_mp)) by { lemma_process_pagetable_match_preserved_for_process_pagetable_fields_forall(); };
                assert(process_iommu_table_match(krnl.prc_mp, krnl.it_mp)) by { lemma_process_iommu_table_match_preserved_for_process_iommu_table_fields_forall(); };
                assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { lemma_container_allocator_free_4k_page_wf_preserved_for_lock_op(*old(krnl),*krnl,); };
            };
            assert(krnl.process_management_inv()) by {
                assert(process_pcid_allocator_wf(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp)) by { lemma_process_pcid_allocator_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(container_process_wf(krnl.ctn_mp, krnl.prc_mp)) by { lemma_container_process_wf_preserved_for_process_rodata_forall(); };
                assert(per_container_process_tree_wf(krnl.ctn_mp, krnl.prc_mp)) by { lemma_per_container_process_tree_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
                assert(process_cpu_wf(krnl.prc_mp, krnl.cpu_arr)) by { lemma_process_cpu_wf_preserved_for_process_pagetable_fields_forall(); };
                assert(process_thread_wf(krnl.prc_mp, krnl.thr_mp)) by { reveal(process_empty_lists_wlocked); reveal(process_thread_wf); lemma_process_thread_wf_preserved_for_process_thread_membership_fields_forall(); };
            };
            assert(cpu_dirty_map_wf(krnl.ctn_mp, krnl.cpu_set_mp, krnl.prc_mp, krnl.cpu_arr, krnl.cpu_tlb, krnl.pt_mp, krnl.pcid_needflush)) by { lemma_cpu_dirty_map_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
            assert(iommu_root_table_process_wf(&krnl.irt, krnl.prc_mp, krnl.it_mp)) by { lemma_iommu_root_table_process_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
            assert(process_pci_function_ownership_wf(&krnl.irt, krnl.prc_mp)) by { lemma_process_pci_function_ownership_wf_preserved_for_process_quota_4k_framed_fields_forall(); };
            assert(iommu_tlb_wf_spec(krnl.iommu_tlb, &krnl.irt, krnl.prc_mp, krnl.it_mp)) by { lemma_iommu_tlb_wf_spec_preserved_for_process_quota_4k_framed_fields_forall(); };
        }
        krnl.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
        krnl.wunlock_container(container_ptr, Tracked(&mut *lctx), container_lock_perm);
        krnl.wunlock_allocator_quota_4k(alloc_ptr_4k, Tracked(&mut *lctx), quota_lock_perm);
        krnl.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
        proof {
            if alloc_amount > 0 {
                assert(kernel_u_only_process_quota_4k_changed(kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(*krnl), process_ptr, alloc_amount as int)) by {
                    reveal(kernel_k_to_kernel_u);
                };
            }
            if alloc_amount == 0 {
                assert(kernel_k_to_kernel_u(*krnl) == kernel_k_to_kernel_u(*old(krnl))) by { kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(krnl),krnl); };
            }
            steps.end_kernel_step(&*krnl, &*lctx);
        }
    }


}
