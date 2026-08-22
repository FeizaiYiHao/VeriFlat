use vstd::prelude::*;
use crate::*;
use super::mmap_4k_context::{
    mmap_4k_held_context,
    mmap_4k_allocation_ready,
    mmap_4k_other_objects_unlocked,
};

verus! {

impl KernelK {
    /// Allocate and publish one 4K leaf after its directory walk is prepared.
    /// The physical leaf is published with both present bits set, then the
    /// completed user-visible mapping is recorded as exactly one kernel step.
    pub(super) fn map_one_mmap_4k_page(
        &mut self,
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
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            mmap_4k_allocation_ready(old(self), old(lctx)),
            va_4k_valid(va),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_va2index(va).0,
            pei_valid(spec_va2index(va).0),
            pei_valid(spec_va2index(va).1),
            pei_valid(spec_va2index(va).2),
            pei_valid(spec_va2index(va).3),
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= 1,
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().dom().contains(va) == false,
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_l2(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                ) is Some,
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_allocation_ready(final(self), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k - 1,
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).container_map.spec_index(container_ptr)
                == old(self).container_map.spec_index(container_ptr),
            final(self).cpu_array.spec_index(cpu_id).view()
                == old(self).cpu_array.spec_index(cpu_id).view(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .mapping_4k().insert(
                        va,
                        final(self).pagetable_map.spec_index(pagetable_ptr)
                            .view().mapping_4k().spec_index(va),
                    ),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(self).pagetable_map.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(self).pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                ==> final(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().dom().contains(va),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).present,
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).write,
            !final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .mapping_4k().spec_index(va).execute_disable,
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_4k_l1(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                ) is Some,
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_4k_l1(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                )->0.perm.present,
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_resolve_mapping_4k_l1(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                )->0.perm.kernel_present,
    {
        let (page_ptr, Tracked(page_lock_perm)) = self.stage_mmap_4k_page(
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
        self.map_owned_4k_page(
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
            assert(page_objects_unlocked_except(
                self.page_array, lctx.thread_id(),
                set![page_ptr2page_index(page_ptr)],
            )) by {
                reveal(page_objects_unlocked_except);
            };
        }
        self.wunlock_page(
            page_ptr2page_index(page_ptr),
            Tracked(&mut *lctx),
            Tracked(page_lock_perm),
        );
        proof {
            assert(lctx.lock_entry_contains(
                self.cpu_array.lock_id_by_index(cpu_id),
                KernelObjId::Cpu(cpu_id),
            )) by { lock_id_fields_eq_imply_eq(); };
            assert(lctx.lock_entry_contains(
                self.container_map.lock_id_by_key(container_ptr),
                KernelObjId::Container(container_ptr),
            )) by { lock_id_fields_eq_imply_eq(); };
            assert(lctx.lock_entry_contains(
                self.process_map.lock_id_by_key(process_ptr),
                KernelObjId::Process(process_ptr),
            )) by { lock_id_fields_eq_imply_eq(); };
            assert(lctx.lock_entry_contains(
                self.thread_map.lock_id_by_key(thread_ptr),
                KernelObjId::Thread(thread_ptr),
            )) by { lock_id_fields_eq_imply_eq(); };
            assert(lctx.lock_entry_contains(
                self.pagetable_map.lock_id_by_key(pagetable_ptr),
                KernelObjId::PageTable(pagetable_ptr),
            )) by { lock_id_fields_eq_imply_eq(); };
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert({
                &&& self.container_map.dom().contains(container_ptr)
                &&& self.container_map.spec_index(container_ptr)
                    .view_rodata().view().allocator_ptr_4k == alloc_ptr_4k
                &&& self.allocator_4k_map.dom().contains(alloc_ptr_4k)
            }) by {
                reveal(container_allocator_wf);
            };
            assert({
                &&& self.pagetable_map.dom().contains(pagetable_ptr)
                &&& self.pagetable_map.spec_index(pagetable_ptr).view().wf()
            }) by {
                reveal(pagetable_perms_wf);
            };
            assert(mmap_4k_other_objects_unlocked(
                self,
                lctx.thread_id(),
                cpu_id,
                container_ptr,
                process_ptr,
                thread_ptr,
                pagetable_ptr,
            )) by {
                reveal(cpu_objects_unlocked_except);
                reveal(container_objects_unlocked_except);
                reveal(process_objects_unlocked_except);
                reveal(thread_objects_unlocked_except);
                reveal(pagetable_objects_unlocked_except);
            };
            assert({
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.cpu_array.spec_index(cpu_id).view().wlocked_by(&*lctx)
                &&& self.cpu_array.spec_index(cpu_id).view().locked_by(&*lctx)
                &&& self.cpu_array.spec_index(cpu_id).view().being_killed() == false
                &&& self.container_map.dom().contains(container_ptr)
                &&& self.container_map.spec_index(container_ptr).wlocked_by(&*lctx)
                &&& self.container_map.spec_index(container_ptr).locked_by(&*lctx)
                &&& self.container_map.spec_index(container_ptr).being_killed() == false
                &&& self.process_map.dom().contains(process_ptr)
                &&& self.process_map.spec_index(process_ptr).wlocked_by(&*lctx)
                &&& self.process_map.spec_index(process_ptr).locked_by(&*lctx)
                &&& self.process_map.spec_index(process_ptr).being_killed() == false
                &&& self.process_map.spec_index(process_ptr).view_rodata().view()
                    .owning_container == container_ptr
                &&& self.thread_map.dom().contains(thread_ptr)
                &&& self.thread_map.spec_index(thread_ptr).wlocked_by(&*lctx)
                &&& self.thread_map.spec_index(thread_ptr).locked_by(&*lctx)
                &&& self.thread_map.spec_index(thread_ptr).being_killed() == false
                &&& self.thread_map.spec_index(thread_ptr).view().owning_proc
                    == process_ptr
                &&& self.thread_map.spec_index(thread_ptr).view().owning_container
                    == container_ptr
                &&& self.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                    == pagetable_ptr
                &&& thread_lock_perm.state() is WriteLock
                &&& thread_lock_perm.thread_id() == lctx.thread_id()
                &&& thread_lock_perm.lock_id()
                    == self.thread_map.spec_index(thread_ptr)
                        .locking_thread()->Write_lock_id
                &&& self.pagetable_map.dom().contains(pagetable_ptr)
                &&& self.pagetable_map.spec_index(pagetable_ptr).wlocked_by(&*lctx)
                &&& self.pagetable_map.spec_index(pagetable_ptr).locked_by(&*lctx)
                &&& pagetable_lock_perm.state() is WriteLock
                &&& pagetable_lock_perm.thread_id() == lctx.thread_id()
                &&& pagetable_lock_perm.lock_id()
                    == self.pagetable_map.spec_index(pagetable_ptr)
                        .locking_thread()->Write_lock_id
            }) by {
                lock_id_fields_eq_imply_eq();
            };

            assert({
                &&& lctx.lock_entry_contains(
                    self.cpu_array.lock_id_by_index(cpu_id),
                    KernelObjId::Cpu(cpu_id))
                &&& lctx.lock_entry_contains(
                    self.container_map.lock_id_by_key(container_ptr),
                    KernelObjId::Container(container_ptr))
                &&& lctx.lock_entry_contains(
                    self.process_map.lock_id_by_key(process_ptr),
                    KernelObjId::Process(process_ptr))
                &&& lctx.lock_entry_contains(
                    self.thread_map.lock_id_by_key(thread_ptr),
                    KernelObjId::Thread(thread_ptr))
                &&& lctx.lock_entry_contains(
                    self.pagetable_map.lock_id_by_key(pagetable_ptr),
                    KernelObjId::PageTable(pagetable_ptr))
            }) by {
                lock_id_fields_eq_imply_eq();
            };

            assert(mmap_4k_held_context(
                self,
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
}

} // verus!
