use vstd::prelude::*;
use crate::*;
use super::mmap_4k_context::{
    mmap_4k_held_context,
    mmap_4k_allocation_ready,
};
use super::mmap_4k_create_entry_install::{
    install_staged_4k_page_table_page,
    MissingPageTableLevel,
};
use super::mmap_4k_stage_page::stage_mmap_4k_page;

verus! {


    /// Allocate and install one missing directory page, then end the kernel
    /// section.  Directory topology is absent from `PageTableU`, so this
    /// boundary is a stuttering user step.
    pub(super) fn install_one_mmap_4k_directory_page(
        kernel: &mut KernelK,
        level: MissingPageTableLevel,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        indices: (L4Index, L3Index, L2Index),
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
        requires
            mmap_4k_held_context(
                old(kernel), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            thread_effective_quota_4k(
                old(kernel).thread_map.spec_index(thread_ptr),
            ) >= 1,
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            match level {
                MissingPageTableLevel::L4 =>
                    old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is Some
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0, indices.1,
                        ) is None
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            indices.0, indices.1,
                        ) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0, indices.1,
                        ) is Some
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                    &&& old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                },
            },
            mmap_4k_allocation_ready(old(kernel), old(lctx)),
        ensures
            mmap_4k_held_context(
                final(kernel), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            mmap_4k_allocation_ready(final(kernel), final(lctx)),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                (old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t)
                        .locked_by_thread(final(lctx).thread_id())),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)]
                #![trigger final(kernel).thread_map.spec_index(t)]
                t != thread_ptr
                    && old(kernel).thread_map.dom().contains(t)
                    && old(kernel).thread_map.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(kernel).thread_map.dom().contains(t)
                    && final(kernel).thread_map.spec_index(t)
                        == old(kernel).thread_map.spec_index(t)
                    && final(kernel).thread_map.lock_id_by_key(t)
                        == old(kernel).thread_map.lock_id_by_key(t),
            forall|p: RwLockPageTableRoot|
                #![trigger old(kernel).pagetable_map.spec_index(p)]
                #![trigger final(kernel).pagetable_map.spec_index(p)]
                (old(kernel).pagetable_map.dom().contains(p)
                    && old(kernel).pagetable_map.spec_index(p)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(kernel).pagetable_map.dom().contains(p)
                    && final(kernel).pagetable_map.spec_index(p)
                        .locked_by_thread(final(lctx).thread_id())),
            forall|p: RwLockPageTableRoot|
                #![trigger old(kernel).pagetable_map.spec_index(p)]
                #![trigger final(kernel).pagetable_map.spec_index(p)]
                p != pagetable_ptr
                    && old(kernel).pagetable_map.dom().contains(p)
                    && old(kernel).pagetable_map.spec_index(p)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(kernel).pagetable_map.dom().contains(p)
                    && final(kernel).pagetable_map.spec_index(p)
                        == old(kernel).pagetable_map.spec_index(p)
                    && final(kernel).pagetable_map.lock_id_by_key(p)
                        == old(kernel).pagetable_map.lock_id_by_key(p),
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k - 1,
            final(kernel).thread_map.spec_index(thread_ptr).view().state
                == old(kernel).thread_map.spec_index(thread_ptr).view().state,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .blocking_endpoint_ptr
                == old(kernel).thread_map.spec_index(thread_ptr).view()
                    .blocking_endpoint_ptr,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .upper_container_seq
                == old(kernel).thread_map.spec_index(thread_ptr).view()
                    .upper_container_seq,
            held_containers_unchanged(
                old(kernel).container_map, final(kernel).container_map, old(lctx),
            ),
            held_processes_unchanged(
                old(kernel).process_map, final(kernel).process_map, old(lctx),
            ),
            held_endpoints_unchanged(
                old(kernel).endpoint_map, final(kernel).endpoint_map, old(lctx),
            ),
            held_schedulers_unchanged(
                old(kernel).scheduler_map, final(kernel).scheduler_map, old(lctx),
            ),
            held_pcid_allocators_unchanged(
                old(kernel).pcid_allocator_map, final(kernel).pcid_allocator_map,
                old(lctx),
            ),
            held_iommu_tables_unchanged(
                old(kernel).iommu_table_map, final(kernel).iommu_table_map,
                old(lctx),
            ),
            held_cpus_unchanged(
                old(kernel).cpu_array, final(kernel).cpu_array, old(lctx),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_2m_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(kernel).allocator_2m_map, final(lctx).thread_id(),
            ),
            allocator_objects_unlocked(
                old(kernel).allocator_1g_map, old(lctx).thread_id(),
            ) ==> allocator_objects_unlocked(
                final(kernel).allocator_1g_map, final(lctx).thread_id(),
            ),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().user_view()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is Some
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0, indices.1,
                        ) is None
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(
                            indices.0, indices.1,
                        ) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(
                            indices.0, indices.1,
                        ) is Some
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                    &&& final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is None
                },
                MissingPageTableLevel::L2 =>
                    final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(
                            indices.0,
                            indices.1,
                            indices.2,
                        ) is Some,
            },
    {
        let (page_ptr, Tracked(page_lock_perm)) = stage_mmap_4k_page(kernel,
            alloc_ptr_4k,
            thread_ptr,
            process_ptr,
            container_ptr,
            cpu_id,
            pagetable_ptr,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(thread_lock_perm),
            Tracked(pagetable_lock_perm),
        );
        install_staged_4k_page_table_page(kernel,
            level,
            page_ptr,
            thread_ptr,
            pagetable_ptr,
            indices,
            Tracked(&mut *lctx),
            Tracked(&page_lock_perm),
            Tracked(thread_lock_perm),
            Tracked(pagetable_lock_perm),
        );
        proof {
            assert(page_objects_unlocked_except(
                kernel.page_array, lctx.thread_id(),
                set![page_ptr2page_index(page_ptr)],
            )) by {
                reveal(page_objects_unlocked_except);
            };
        }
        kernel.wunlock_page(
            page_ptr2page_index(page_ptr),
            Tracked(&mut *lctx),
            Tracked(page_lock_perm),
        );
        proof {
            assert({
                &&& lctx.lock_entry_contains(
                    kernel.cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id))
                &&& lctx.lock_entry_contains(
                    kernel.thread_map.lock_id_by_key(thread_ptr),
                    KernelObjId::Thread(thread_ptr))
                &&& lctx.lock_entry_contains(
                    kernel.pagetable_map.lock_id_by_key(pagetable_ptr),
                    KernelObjId::PageTable(pagetable_ptr))
            }) by {
                lock_id_fields_eq_imply_eq();
            };
            assert(mmap_4k_allocation_ready(kernel, &*lctx)) by {
                assert(
                    PAGE_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR
                        && IOMMU_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR
                        && ALLOCATED_PAGE_MAJOR < ALLOCATOR_CACHE_MAJOR
                ) by (compute);
            };
            kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(mmap_4k_allocation_ready(kernel, &*lctx)) by {
                assert(
                    PAGE_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR
                        && IOMMU_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR
                        && ALLOCATED_PAGE_MAJOR < ALLOCATOR_CACHE_MAJOR
                ) by (compute);
            };
            assert({
                &&& kernel.container_map.dom().contains(container_ptr)
                &&& kernel.container_map.spec_index(container_ptr)
                    .view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                &&& kernel.allocator_4k_map.dom().contains(alloc_ptr_4k)
            }) by {
                reveal(container_thread_wf);
                reveal(container_allocator_wf);
            };
            assert({
                &&& kernel.pagetable_map.dom().contains(pagetable_ptr)
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).view().wf()
            }) by {
                reveal(pagetable_perms_wf);
            };
            assert({
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& kernel.cpu_array.spec_index(cpu_id).view().wlocked_by(&*lctx)
                &&& kernel.cpu_array.spec_index(cpu_id).view().locked_by(&*lctx)
                &&& kernel.cpu_array.spec_index(cpu_id).view().being_killed() == false
                &&& kernel.container_map.dom().contains(container_ptr)
                &&& kernel.process_map.dom().contains(process_ptr)
                &&& kernel.process_map.spec_index(process_ptr).view_rodata().view()
                    .owning_container == container_ptr
                &&& kernel.thread_map.dom().contains(thread_ptr)
                &&& kernel.thread_map.spec_index(thread_ptr).wlocked_by(&*lctx)
                &&& kernel.thread_map.spec_index(thread_ptr).locked_by(&*lctx)
                &&& kernel.thread_map.spec_index(thread_ptr).being_killed() == false
                &&& kernel.thread_map.spec_index(thread_ptr).view().owning_proc
                    == process_ptr
                &&& kernel.thread_map.spec_index(thread_ptr).view().owning_container
                    == container_ptr
                &&& kernel.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                    == pagetable_ptr
                &&& thread_lock_perm.state() is WriteLock
                &&& thread_lock_perm.thread_id() == lctx.thread_id()
                &&& thread_lock_perm.lock_id()
                    == kernel.thread_map.spec_index(thread_ptr)
                        .locking_thread()->Write_lock_id
                &&& kernel.pagetable_map.dom().contains(pagetable_ptr)
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).wlocked_by(&*lctx)
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).locked_by(&*lctx)
                &&& pagetable_lock_perm.state() is WriteLock
                &&& pagetable_lock_perm.thread_id() == lctx.thread_id()
                &&& pagetable_lock_perm.lock_id()
                    == kernel.pagetable_map.spec_index(pagetable_ptr)
                        .locking_thread()->Write_lock_id
            }) by {
                reveal(cpu_array_wf);
                reveal(container_thread_wf);
                reveal(container_process_wf);
                reveal(process_thread_wf);
                reveal(thread_perms_wf);
                reveal(pagetable_perms_wf);
                lock_id_fields_eq_imply_eq();
            };

            assert({
                &&& lctx.lock_entry_contains(
                    kernel.cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id))
                &&& lctx.lock_entry_contains(
                    kernel.thread_map.lock_id_by_key(thread_ptr),
                    KernelObjId::Thread(thread_ptr))
                &&& lctx.lock_entry_contains(
                    kernel.pagetable_map.lock_id_by_key(pagetable_ptr),
                    KernelObjId::PageTable(pagetable_ptr))
            }) by {
                lock_id_fields_eq_imply_eq();
            };

            assert(mmap_4k_held_context(
                kernel,
                &*lctx,
                alloc_ptr_4k,
                thread_ptr,
                process_ptr,
                container_ptr,
                cpu_id,
                pagetable_ptr,
                thread_lock_perm,
                pagetable_lock_perm,
            )) by {
                lock_id_fields_eq_imply_eq();
            };
        }
    }


} // verus!
