use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_owned::map_owned_4k_page;

verus! {


    /// Allocate and publish one 4K leaf after its directory walk is prepared.
    /// The physical leaf is published with both present bits set, then the
    /// completed user-visible mapping is recorded as exactly one kernel step.
    pub(super) fn map_one_mmap_4k_page(
        kernel: &mut KernelK,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        va: VAddr,
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
            mmap_4k_allocation_ready(old(kernel), old(lctx)),
            old(kernel).container_map.spec_index(container_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(kernel).process_map.spec_index(process_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            old(lctx).lock_entry_contains(
                old(kernel).container_map.lock_id_by_key(container_ptr),
                KernelObjId::Container(container_ptr),
            ),
            old(lctx).lock_entry_contains(
                old(kernel).process_map.lock_id_by_key(process_ptr),
                KernelObjId::Process(process_ptr),
            ),
            va_4k_valid(va),
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_va2index(va).0,
            pei_valid(spec_va2index(va).0),
            pei_valid(spec_va2index(va).1),
            pei_valid(spec_va2index(va).2),
            pei_valid(spec_va2index(va).3),
            old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            thread_effective_quota_4k(
                old(kernel).thread_map.spec_index(thread_ptr),
            ) >= 1,
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().dom().contains(va) == false,
            old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l2(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                ) is Some,
        ensures
            mmap_4k_held_context(
                final(kernel), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            mmap_4k_allocation_ready(final(kernel), final(lctx)),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(lctx).lock_entry_contains(
                final(kernel).container_map.lock_id_by_key(container_ptr),
                KernelObjId::Container(container_ptr),
            ),
            final(lctx).lock_entry_contains(
                final(kernel).process_map.lock_id_by_key(process_ptr),
                KernelObjId::Process(process_ptr),
            ),
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k - 1,
            final(kernel).process_map.spec_index(process_ptr)
                == old(kernel).process_map.spec_index(process_ptr),
            final(kernel).container_map.spec_index(container_ptr)
                == old(kernel).container_map.spec_index(container_ptr),
            final(kernel).cpu_array.spec_index(cpu_id).view()
                == old(kernel).cpu_array.spec_index(cpu_id).view(),
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
            thread_objects_unlocked_except(
                old(kernel).thread_map, old(lctx).thread_id(), set![thread_ptr],
            ) ==> thread_objects_unlocked_except(
                final(kernel).thread_map, final(lctx).thread_id(), set![thread_ptr],
            ),
            pagetable_objects_unlocked_except(
                old(kernel).pagetable_map, old(lctx).thread_id(), set![pagetable_ptr],
            ) ==> pagetable_objects_unlocked_except(
                final(kernel).pagetable_map, final(lctx).thread_id(), set![pagetable_ptr],
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
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .mapping_4k().insert(
                        va,
                        final(kernel).pagetable_map.spec_index(pagetable_ptr)
                            .view().mapping_4k().spec_index(va),
                    ),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(kernel).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(kernel).pagetable_map.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                ==> final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().dom().contains(va),
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).present,
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).write,
            !final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).execute_disable,
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_4k_l1(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                ) is Some,
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_4k_l1(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                )->0.perm.present,
            final(kernel).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_4k_l1(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                )->0.perm.kernel_present,
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
        map_owned_4k_page(kernel,
            page_ptr,
            thread_ptr,
            pagetable_ptr,
            va,
            true,
            false,
            Tracked(&mut *lctx),
            Tracked(&page_lock_perm),
            Tracked(thread_lock_perm),
            Tracked(pagetable_lock_perm),
        );
        proof {
            assert(thread_objects_unlocked_except(
                old(kernel).thread_map, old(lctx).thread_id(), set![thread_ptr],
            ) ==> thread_objects_unlocked_except(
                kernel.thread_map, lctx.thread_id(), set![thread_ptr],
            )) by {
                reveal(thread_objects_unlocked_except);
            };
            assert(pagetable_objects_unlocked_except(
                old(kernel).pagetable_map, old(lctx).thread_id(), set![pagetable_ptr],
            ) ==> pagetable_objects_unlocked_except(
                kernel.pagetable_map, lctx.thread_id(), set![pagetable_ptr],
            )) by {
                reveal(pagetable_objects_unlocked_except);
            };
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
            assert(lctx.lock_entry_contains(
                kernel.cpu_array.lock_id_by_index(cpu_id),
                KernelObjId::Cpu(cpu_id),
            )) by { lock_id_fields_eq_imply_eq(); };
            assert(lctx.lock_entry_contains(
                kernel.container_map.lock_id_by_key(container_ptr),
                KernelObjId::Container(container_ptr),
            )) by { lock_id_fields_eq_imply_eq(); };
            assert(lctx.lock_entry_contains(
                kernel.process_map.lock_id_by_key(process_ptr),
                KernelObjId::Process(process_ptr),
            )) by { lock_id_fields_eq_imply_eq(); };
            assert(lctx.lock_entry_contains(
                kernel.thread_map.lock_id_by_key(thread_ptr),
                KernelObjId::Thread(thread_ptr),
            )) by { lock_id_fields_eq_imply_eq(); };
            assert(lctx.lock_entry_contains(
                kernel.pagetable_map.lock_id_by_key(pagetable_ptr),
                KernelObjId::PageTable(pagetable_ptr),
            )) by { lock_id_fields_eq_imply_eq(); };
            kernel.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert({
                &&& kernel.container_map.dom().contains(container_ptr)
                &&& kernel.container_map.spec_index(container_ptr)
                    .view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                &&& kernel.allocator_4k_map.dom().contains(alloc_ptr_4k)
            }) by {
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
