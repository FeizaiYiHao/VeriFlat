use vstd::prelude::*;
use vstd::assert_seqs_equal;
use crate::*;
verus! {
    impl KernelK{
        pub fn commit_alloc_quota_4k(
            &mut self,
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
                old(self).inv(),
                index_valid(NUM_CPUS, cpu_id),
                old(lctx).kernel_view_locking_state() is Acquire,
                old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
                cpu_lock_perm.view().state() is WriteLock,
                cpu_lock_perm.view().thread_id() == old(lctx).thread_id(),
                cpu_lock_perm.view().lock_id() == old(self).cpu_array.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
                old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
                old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
                old(self).container_map.dom().contains(container_ptr),
                container_lock_perm.view().state() is WriteLock,
                container_lock_perm.view().thread_id() == old(lctx).thread_id(),
                container_lock_perm.view().lock_id() == old(self).container_map.spec_index(container_ptr).locking_thread()->Write_lock_id,
                old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
                old(self).container_map.spec_index(container_ptr).being_killed() == false,
                old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.is_init(),
                quota_lock_perm.view().state() is WriteLock,
                quota_lock_perm.view().thread_id() == old(lctx).thread_id(),
                quota_lock_perm.view().lock_id() == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread()->Write_lock_id,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota
                    .wlocked_by(old(lctx)),
                old(self).process_map.dom().contains(process_ptr),
                process_lock_perm.view().state() is WriteLock,
                process_lock_perm.view().thread_id() == old(lctx).thread_id(),
                process_lock_perm.view().lock_id() == old(self).process_map.spec_index(process_ptr).locking_thread()->Write_lock_id,
                old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
                old(self).process_map.spec_index(process_ptr).being_killed() == false,
                old(lctx).lock_id_set().contains((
                    old(self).cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id),
                )),
                old(lctx).lock_id_set().contains((
                    old(self).container_map.lock_id_by_key(container_ptr),
                    KernelObjId::Container(container_ptr),
                )),
                old(lctx).lock_id_set().contains((
                    old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                    KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                )),
                old(lctx).lock_id_set().contains((
                    old(self).process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr),
                )),
                old(self).container_map.spec_index(container_ptr).view().owned_processes.view().contains(process_ptr),
                old(self).container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
                alloc_amount <= usize::MAX - old(self).process_map.spec_index(process_ptr).view().quota_4k,
                old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.view().value >= alloc_amount,
                lock_id_aligned(old(self), old(lctx)),
            ensures
                final(self).inv(),
                lock_id_aligned(final(self), final(lctx)),
                final(self).pagetable_map     == old(self).pagetable_map,
                final(self).iommu_table_map     == old(self).iommu_table_map,
                final(self).iommu_root_table     == old(self).iommu_root_table,
                final(self).page_array        == old(self).page_array,
                final(self).cpu_tlb           == old(self).cpu_tlb,
                final(self).iommu_tlb           == old(self).iommu_tlb,
                final(self).root_container    == old(self).root_container,
                final(self).scheduler_map     == old(self).scheduler_map,
                final(self).pcid_allocator_map == old(self).pcid_allocator_map,
                final(self).thread_map        == old(self).thread_map,
                final(self).endpoint_map      == old(self).endpoint_map,
                final(self).allocator_2m_map  == old(self).allocator_2m_map,
                final(self).allocator_1g_map  == old(self).allocator_1g_map,
                final(self).default_pagetable == old(self).default_pagetable,
                final(self).cpu_array.entries_unchanged_except(&old(self).cpu_array, cpu_id),
                final(self).cpu_array.spec_index(cpu_id).view().locking_thread() is None,
                final(self).container_map.unchanged_except(&old(self).container_map, container_ptr),
                final(self).container_map.spec_index(container_ptr).locking_thread() is None,
                final(self).process_map.unchanged_except(&old(self).process_map, process_ptr),
                final(self).process_map.spec_index(process_ptr).locking_thread() is None,
                final(self).allocator_4k_map.dom() == old(self).allocator_4k_map.dom(),
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.locking_thread() is None,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).cpu_caches,
                final(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool == old(self).allocator_4k_map.spec_index(alloc_ptr_4k).global_pool,
                forall|k: usize| #![auto] old(self).allocator_4k_map.dom().contains(k) && k != alloc_ptr_4k ==>
                    final(self).allocator_4k_map.spec_index(k) == old(self).allocator_4k_map.spec_index(k),
                final(lctx).thread_id() == old(lctx).thread_id(),
                final(lctx).lock_id_set() == old(lctx).lock_id_set()
                    .remove((
                        old(self).cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id),
                    ))
                    .remove((
                        old(self).container_map.lock_id_by_key(container_ptr),
                        KernelObjId::Container(container_ptr),
                    ))
                    .remove((
                        old(self).allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                        KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k),
                    ))
                    .remove((
                        old(self).process_map.lock_id_by_key(process_ptr),
                        KernelObjId::Process(process_ptr),
                    )),
                final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
                alloc_amount == 0 ==> final(steps).steps == old(steps).steps,
                alloc_amount > 0 ==> {
                    &&& final(steps).steps.len() == old(steps).steps.len() + 1
                    &&& final(steps).steps.last().old_u == kernel_k_to_kernel_u(*old(self))
                    &&& final(steps).steps.last().new_u == kernel_k_to_kernel_u(*final(self))
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
                    self.process_map.perms_wf()
                    && self.process_map.spec_index(process_ptr).is_init()
                ) by {
                    reveal(process_perms_wf);
                };
                assert(self.allocator_4k_map.perms_wf()) by {
                    reveal(allocator_perms_wf);
                };
            }
            {
                let process_mut = self.process_map.borrow_mut(
                    process_ptr,
                    Tracked(&*lctx),
                    Tracked(process_lock_perm.borrow()),
                );
                process_mut.quota_4k = process_mut.quota_4k + alloc_amount;
            }
            {
                let quota_mut = self.allocator_4k_map.borrow_mut_quota(
                    alloc_ptr_4k,
                    Tracked(&*lctx),
                    Tracked(quota_lock_perm.borrow()),
                );
                quota_mut.value = quota_mut.value - alloc_amount;
            }

            proof {
                assert(
                    allocator_perms_wf(self.allocator_4k_map)
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k).wf()
                    && process_perms_wf(self.process_map)
                ) by {
                    reveal(allocator_perms_wf);
                    reveal(process_perms_wf);
                };
                assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
                assert(self.memory_management_inv()) by {
                    assert(allocator_pages_wf(self.page_array, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { lemma_no_change_imply_allocator_pages_wf_forall(); };
                    assert(container_process_page_pagetable_wf(self.container_map, self.process_map, self.pagetable_map, self.page_array)) by { lemma_no_change_imply_container_process_page_pagetable_wf_forall(); };
                    assert(process_pages_wf(self.page_array, self.process_map)) by { lemma_no_change_imply_process_pages_wf_forall(); };
                    assert(container_process_allocator_quota_4k_wf(self.container_map, self.process_map, self.thread_map, self.allocator_4k_map)) by {
                        reveal(container_process_allocator_quota_4k_wf);
                        reveal(container_process_wf);
                        reveal(container_allocator_wf);
                        crate::kernel::lemma::allocator_quota_fold::lemma_process_effective_quota_4k_fold_change_by_forall(process_ptr, alloc_amount as int);
                        crate::kernel::lemma::allocator_quota_fold::lemma_process_effective_quota_4k_fold_sum_eq_forall();
                    };
                    assert(container_process_allocator_quota_2m_wf(self.container_map, self.process_map, self.thread_map, self.allocator_2m_map)) by { crate::kernel::lemma::allocator_quota_fold::container_process_allocator_quota_2m_wf_forall(); };
                    assert(container_process_allocator_quota_1g_wf(self.container_map, self.process_map, self.thread_map, self.allocator_1g_map)) by { crate::kernel::lemma::allocator_quota_fold::container_process_allocator_quota_1g_wf_forall(); };
                    assert(container_allocator_wf(self.container_map, self.allocator_4k_map, self.allocator_2m_map, self.allocator_1g_map)) by { lemma_no_change_imply_container_allocator_wf_forall(); };
                    assert(allocator_free_page_ptrs_wf(self.allocator_4k_map)) by { lemma_no_change_imply_allocator_free_page_ptrs_wf_forall(); };
                    assert(process_pagetable_match(self.process_map, self.pagetable_map)) by { lemma_no_change_imply_process_pagetable_match_forall(); };
                    assert(process_iommu_table_match(self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_process_iommu_table_match_forall(); };
                    assert(container_allocator_free_4k_page_wf(self.allocator_4k_map, self.page_array)) by { lemma_no_change_imply_container_allocator_free_4k_page_wf_forall(); };
                };
                assert(self.process_management_inv()) by {
                    assert(process_pcid_allocator_wf(self.container_map, self.process_map, self.pcid_allocator_map)) by { lemma_no_change_imply_process_pcid_allocator_wf_forall(); };
                    assert(container_process_wf(self.container_map, self.process_map)) by { lemma_no_change_imply_container_process_wf_forall(); };
                    assert(per_container_process_tree_wf(self.container_map, self.process_map)) by { lemma_no_change_imply_per_container_process_tree_wf_forall(); };
                    assert(process_cpu_wf(self.process_map, self.cpu_array)) by { lemma_no_change_imply_process_cpu_wf_forall(); };
                    assert(process_thread_wf(self.process_map, self.thread_map)) by { lemma_no_change_imply_process_thread_wf_forall(); };
                };
                assert(cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)) by { lemma_no_change_imply_cpu_dirty_map_wf_forall(); };
                assert(iommu_root_table_process_wf(&self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_root_table_process_wf_forall(); };
                assert(process_pci_function_ownership_wf(&self.iommu_root_table, self.process_map)) by { lemma_no_change_imply_process_pci_function_ownership_wf_forall(); };
                assert(iommu_tlb_wf_spec(self.iommu_tlb, &self.iommu_root_table, self.process_map, self.iommu_table_map)) by { lemma_no_change_imply_iommu_tlb_wf_spec_forall(); };
                assert({
                    &&& self.process_map.lock_id_by_key(process_ptr)
                        == old(self).process_map.lock_id_by_key(process_ptr)
                    &&& self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id()
                        == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                            .quota.lock_id()
                    &&& lctx.lock_entry_contains(
                        self.cpu_array.lock_id_by_index(cpu_id),
                        KernelObjId::Cpu(cpu_id))
                    &&& lctx.lock_entry_contains(
                        self.container_map.lock_id_by_key(container_ptr),
                        KernelObjId::Container(container_ptr))
                    &&& lctx.lock_entry_contains(
                        self.allocator_4k_map.spec_index(alloc_ptr_4k).quota.lock_id(),
                        KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr_4k))
                    &&& lctx.lock_entry_contains(
                        self.process_map.lock_id_by_key(process_ptr),
                        KernelObjId::Process(process_ptr))
                }) by {
                    lock_id_fields_eq_imply_eq();
                };
                assert(lock_id_aligned(&*self, &*lctx)) by {
                    reveal(lock_id_aligned);
                    lock_id_fields_eq_imply_eq();
                };
            }
            self.wunlock_cpu(cpu_id, Tracked(&mut *lctx), cpu_lock_perm);
            self.wunlock_container(container_ptr, Tracked(&mut *lctx), container_lock_perm);
            self.wunlock_quota_4k(alloc_ptr_4k, Tracked(&mut *lctx), quota_lock_perm);
            self.wunlock_process(process_ptr, Tracked(&mut *lctx), process_lock_perm);
            proof {
                if alloc_amount == 0 {
                    assert(kernel_k_to_kernel_u(*self)
                        == kernel_k_to_kernel_u(*old(self))) by {
                        kernel_no_change_to_user_view_fields_imply_kernel_u_eq(
                            old(self),
                            self,
                        );
                    };
                } else {
                    assert(kernel_u_only_process_quota_4k_changed(
                        kernel_k_to_kernel_u(*old(self)),
                        kernel_k_to_kernel_u(*self),
                        process_ptr,
                        alloc_amount as int,
                    )) by {
                        assert_seqs_equal!(
                            kernel_k_to_kernel_u(*self).cpu_array
                                == kernel_k_to_kernel_u(*old(self)).cpu_array
                        );
                    };
                }
                steps.end_kernel_step(&*self, &*lctx);
            }
        }

    }

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

}
