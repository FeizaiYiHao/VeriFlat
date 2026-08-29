use vstd::prelude::*;
use vstd::assert_seqs_equal;
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
        kernel: &mut KernelK,
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
            old(kernel).inv(),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            cpu_lock_perm.view().state() is WriteLock,
            cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.view().lock_id() == old(kernel).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(kernel).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(kernel).cpu_array.spec_index(cpu_id).view().being_killed() == false,
            old(kernel).container_map.dom().contains(container_ptr),
            container_lock_perm.view().state() is WriteLock,
            container_lock_perm.view().thread_id() == old(lctx).thread_id(),
            container_lock_perm.view().lock_id() == old(kernel).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
            old(kernel).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
            old(kernel).container_map.spec_index(container_ptr).being_killed() == false,
            old(kernel).allocator_4k_map.dom().contains(alloc_ptr_4k),
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota.is_init(),
            quota_lock_perm.view().state() is WriteLock,
            quota_lock_perm.view().thread_id() == old(lctx).thread_id(),
            quota_lock_perm.view().lock_id() == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                .wlocked_by(old(lctx)),
            old(kernel).process_map.dom().contains(process_ptr),
            process_lock_perm.view().state() is WriteLock,
            process_lock_perm.view().thread_id() == old(lctx).thread_id(),
            process_lock_perm.view().lock_id() == old(kernel).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
            old(kernel).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(kernel).process_map.spec_index(process_ptr).being_killed() == false,
            old(lctx).lock_id_set() =~= set![
                (
                    old(kernel).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                ),
                (
                    old(kernel).container_map.lock_id_by_key(container_ptr),
                    KernelObjId::Container(container_ptr),
                ),
                (
                    old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .quota.lock_id(),
                    KernelObjId::AllocatorQuota(
                        PageSize::SZ4k, alloc_ptr_4k),
                ),
                (
                    old(kernel).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr),
                ),
            ],
            old(lctx).page_lock_set().is_empty(),
            old(lctx).cpu_lock_set() =~= set![cpu_id],
            old(lctx).container_lock_set() =~= set![container_ptr],
            old(lctx).process_lock_set() =~= set![process_ptr],
            old(lctx).thread_lock_set().is_empty(),
            old(lctx).endpoint_lock_set().is_empty(),
            old(lctx).scheduler_lock_set().is_empty(),
            old(lctx).pcid_allocator_lock_set().is_empty(),
            old(lctx).pagetable_lock_set().is_empty(),
            old(lctx).iommu_table_lock_set().is_empty(),
            old(lctx).allocator_quota_lock_set() =~=
                set![(PageSize::SZ4k, alloc_ptr_4k)],
            old(lctx).allocator_cache_lock_set().is_empty(),
            old(lctx).allocator_global_pool_lock_set().is_empty(),
            old(kernel).container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
            old(kernel).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            alloc_amount <= usize::MAX - old(kernel).process_map.spec_index(process_ptr).view().quota_4k,
            old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().value >= alloc_amount,
            lock_id_aligned(old(kernel), old(lctx)),
            typed_lock_sets_aligned(old(kernel), old(lctx)),
        ensures
            final(kernel).inv(),
            lock_id_aligned(final(kernel), final(lctx)),
            typed_lock_sets_aligned(final(kernel), final(lctx)),
            final(kernel).pagetable_map     == old(kernel).pagetable_map,
            final(kernel).iommu_table_map     == old(kernel).iommu_table_map,
            final(kernel).iommu_root_table     == old(kernel).iommu_root_table,
            final(kernel).page_array        == old(kernel).page_array,
            final(kernel).cpu_tlb           == old(kernel).cpu_tlb,
            final(kernel).iommu_tlb           == old(kernel).iommu_tlb,
            final(kernel).root_container    == old(kernel).root_container,
            final(kernel).scheduler_map     == old(kernel).scheduler_map,
            final(kernel).pcid_allocator_map == old(kernel).pcid_allocator_map,
            final(kernel).thread_map        == old(kernel).thread_map,
            final(kernel).endpoint_map      == old(kernel).endpoint_map,
            final(kernel).allocator_2m_map  == old(kernel).allocator_2m_map,
            final(kernel).allocator_1g_map  == old(kernel).allocator_1g_map,
            final(kernel).default_pagetable == old(kernel).default_pagetable,
            final(kernel).cpu_array.entries_unchanged_except(&old(kernel).cpu_array, cpu_id),
            final(kernel).cpu_array.spec_index(cpu_id).view().locking_thread() is None,
            final(kernel).container_map.unchanged_except(&old(kernel).container_map, container_ptr),
            final(kernel).container_map.spec_index(container_ptr).locking_thread() is None,
            final(kernel).process_map.unchanged_except(&old(kernel).process_map, process_ptr),
            final(kernel).process_map.spec_index(process_ptr).locking_thread() is None,
            final(kernel).allocator_4k_map.dom() == old(kernel).allocator_4k_map.dom(),
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread() is None,
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
            final(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
            forall|k: usize| #![auto] old(kernel).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                final(kernel).allocator_4k_map.spec_index(k) == old(kernel).allocator_4k_map.spec_index(k),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(lctx).page_lock_set().is_empty(),
            final(lctx).cpu_lock_set().is_empty(),
            final(lctx).container_lock_set().is_empty(),
            final(lctx).process_lock_set().is_empty(),
            final(lctx).thread_lock_set().is_empty(),
            final(lctx).endpoint_lock_set().is_empty(),
            final(lctx).scheduler_lock_set().is_empty(),
            final(lctx).pcid_allocator_lock_set().is_empty(),
            final(lctx).pagetable_lock_set().is_empty(),
            final(lctx).iommu_table_lock_set().is_empty(),
            final(lctx).allocator_quota_lock_set().is_empty(),
            final(lctx).allocator_cache_lock_set().is_empty(),
            final(lctx).allocator_global_pool_lock_set().is_empty(),
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            alloc_amount == 0 ==> final(steps).steps == old(steps).steps,
            alloc_amount > 0 ==> {
                &&& final(steps).steps.len() == old(steps).steps.len() + 1
                &&& final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(kernel))
                &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(kernel))
                &&& kernel_u_only_process_quota_4k_changed(
                    final(steps).steps.last().old_u,
                    final(steps).steps.last().new_u,
                    process_ptr,
                    alloc_amount as int,
                )
            },
    {

        proof {
            assert(
                kernel.process_map.perms_wf()
                && kernel.process_map.spec_index(process_ptr).is_init()
            ) by {
                reveal(process_perms_wf);
            };
            assert(kernel.allocator_4k_map.perms_wf()) by {
                reveal(allocator_perms_wf);
            };
        }
        {
            let process_mut = kernel.process_map.borrow_mut(
                process_ptr,
                Tracked(&*lctx),
                Tracked(process_lock_perm.borrow()),
            );
            process_mut.quota_4k = process_mut.quota_4k + alloc_amount;
        }
        {
            let quota_mut = kernel.allocator_4k_map.borrow_mut_quota(
                alloc_ptr_4k,
                Tracked(&*lctx),
                Tracked(quota_lock_perm.borrow()),
            );
            quota_mut.value = quota_mut.value - alloc_amount;
        }

        proof {
            assert(
                allocator_perms_wf(kernel.allocator_4k_map)
                && kernel.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                && process_perms_wf(kernel.process_map)
            ) by {
                reveal(allocator_perms_wf);
                reveal(process_perms_wf);
            };
            assert(kernel.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
            assert(kernel.memory_management_inv()) by {
                assert(allocator_pages_wf(kernel.page_array, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by { lemma_no_change_imply_allocator_pages_wf_forall(); };
                assert(container_process_page_pagetable_wf(kernel.container_map, kernel.process_map, kernel.pagetable_map, kernel.page_array)) by { lemma_no_change_imply_container_process_page_pagetable_wf_forall(); };
                assert(process_pages_wf(kernel.page_array, kernel.process_map)) by { lemma_no_change_imply_process_pages_wf_forall(); };
                assert(container_process_allocator_quota_4k_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_4k_map)) by {
                    reveal(container_process_allocator_quota_4k_wf);
                    reveal(container_process_wf);
                    reveal(container_allocator_wf);
                    crate::kernel::lemma::allocator_quota_fold::lemma_process_effective_quota_4k_fold_change_by_forall(process_ptr, alloc_amount as int);
                    crate::kernel::lemma::allocator_quota_fold::lemma_process_effective_quota_4k_fold_sum_eq_forall();
                };
                assert(container_process_allocator_quota_2m_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_2m_map)) by { crate::kernel::lemma::allocator_quota_fold::container_process_allocator_quota_2m_wf_forall(); };
                assert(container_process_allocator_quota_1g_wf(kernel.container_map, kernel.process_map, kernel.thread_map, kernel.allocator_1g_map)) by { crate::kernel::lemma::allocator_quota_fold::container_process_allocator_quota_1g_wf_forall(); };
                assert(container_allocator_wf(kernel.container_map, kernel.allocator_4k_map, kernel.allocator_2m_map, kernel.allocator_1g_map)) by { lemma_no_change_imply_container_allocator_wf_forall(); };
                assert(allocator_free_page_ptrs_wf(kernel.allocator_4k_map)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                assert(process_pagetable_match(kernel.process_map, kernel.pagetable_map)) by { lemma_no_change_imply_process_pagetable_match_forall(); };
                assert(process_iommu_table_match(kernel.process_map, kernel.iommu_table_map)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
                assert(container_allocator_free_4k_page_wf(kernel.allocator_4k_map, kernel.page_array)) by { lemma_no_change_imply_container_allocator_free_4k_page_wf_forall(); };
            };
            assert(kernel.process_management_inv()) by {
                assert(process_pcid_allocator_wf(kernel.container_map, kernel.process_map, kernel.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_forall(); };
                assert(container_process_wf(kernel.container_map, kernel.process_map)) by { lemma_no_change_imply_container_process_wf_forall(); };
                assert(per_container_process_tree_wf(kernel.container_map, kernel.process_map)) by { lemma_no_change_imply_per_container_process_tree_wf_forall(); };
                assert(process_cpu_wf(kernel.process_map, kernel.cpu_array)) by { lemma_no_change_imply_process_cpu_wf_forall(); };
                assert(process_thread_wf(kernel.process_map, kernel.thread_map)) by { lemma_no_change_imply_process_thread_wf_forall(); };
            };
            assert(cpu_dirty_map_wf(kernel.container_map, kernel.process_map, kernel.cpu_array, kernel.cpu_tlb, kernel.pagetable_map)) by { lemma_no_change_imply_cpu_dirty_map_wf_forall(); };
            assert(iommu_root_table_process_wf(&kernel.iommu_root_table, kernel.process_map, kernel.iommu_table_map)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
            assert(process_pci_function_ownership_wf(&kernel.iommu_root_table, kernel.process_map)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
            assert(iommu_tlb_wf_spec(kernel.iommu_tlb, &kernel.iommu_root_table, kernel.process_map, kernel.iommu_table_map)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
            assert({
                &&& kernel.process_map.unchanged_except(
                    &old(kernel).process_map, process_ptr)
                &&& kernel.allocator_4k_map.unchanged_except(
                    &old(kernel).allocator_4k_map, alloc_ptr_4k)
                &&& kernel.cpu_array.lock_id_by_index(cpu_id)
                    == old(kernel).cpu_array.lock_id_by_index(cpu_id)
                &&& kernel.container_map.lock_id_by_key(container_ptr)
                    == old(kernel).container_map.lock_id_by_key(container_ptr)
                &&& kernel.process_map.lock_id_by_key(process_ptr)
                    == old(kernel).process_map.lock_id_by_key(process_ptr)
                &&& kernel.allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id()
                    == old(kernel).allocator_4k_map.spec_index(alloc_ptr_4k)
                        .quota.lock_id()
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(lock_id_aligned(&*kernel, &*lctx)) by {
                reveal(lock_id_aligned);
                lock_id_fields_eq_imply_eq();
            };
            assert(typed_lock_sets_aligned(&*kernel, &*lctx)) by {
                reveal(typed_lock_sets_aligned);
            };
        }
        kernel.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
        kernel.wunlock_container(container_ptr, Tracked(&mut *lctx), container_lock_perm);
        kernel.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut *lctx), quota_lock_perm);
        kernel.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
        proof {
            if alloc_amount == 0 {
                assert(kernel_k_to_kernel_u(*kernel)
                    == kernel_k_to_kernel_u(*old(kernel))) by {
                    kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                        old(kernel),
                        kernel,
                    );
                };
            } else {
                assert(kernel_u_only_process_quota_4k_changed(
                    kernel_k_to_kernel_u(*old(kernel)),
                    kernel_k_to_kernel_u(*kernel),
                    process_ptr,
                    alloc_amount as int,
                )) by {
                    assert_seqs_equal!(
                        kernel_k_to_kernel_u(*kernel).cpu_array
                            == kernel_k_to_kernel_u(*old(kernel)).cpu_array
                    );
                };
            }
            steps.end_kernel_step(&*kernel, &*lctx);
        }
    }


}
