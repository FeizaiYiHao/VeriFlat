use vstd::prelude::*;

use crate::*;
use super::mmap_4k_context::{mmap_4k_held_context, mmap_4k_no_page_locks};
use super::mmap_4k_range_induction::{
    pagetable_4k_insert_advances_range_prefix_forall,
    pagetable_4k_insert_preserves_range_suffix_forall,
    pagetable_prepare_advances_range_prefix_forall,
};
use super::mmap_4k_raw_range::mmap_4k_range_mapped_implies_raw;
use super::mmap_4k_syscall_def::*;

verus! {

impl KernelK {
    /// Prepare every directory walk first, then map the checked range one leaf
    /// at a time. The running thread supplies the conservative
    /// four-pages-per-VA quota bound. Directory pages consume quota but append
    /// no user steps; after all walks exist, each leaf mapping appends one.
    pub(super) fn map_checked_4k_range(
        &mut self,
        range: &VaRange4K,
        credit: usize,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<LockPerm>,
        Tracked(process_lock_perm): Tracked<LockPerm>,
        Tracked(container_lock_perm): Tracked<LockPerm>,
        Tracked(cpu_lock_perm): Tracked<LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<LockPerm>,
    )
        requires
            mmap_4k_held_context(
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, &thread_lock_perm,
                &pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            range.wf(),
            range.len > 0,
            credit == 4 * range.len,
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id()
                == old(self).cpu_array.spec_index(cpu_id).view()
                    .locking_thread()->Write_lock_id,
            old(self).container_map.spec_index(container_ptr).being_killed() == false,
            container_lock_perm.state() is WriteLock,
            container_lock_perm.thread_id() == old(lctx).thread_id(),
            container_lock_perm.lock_id()
                == old(self).container_map.spec_index(container_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).view().pagetable
                == pagetable_ptr,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id()
                == old(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k >= credit,
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= credit,
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            mmap_4k_range_empty(
                old(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            ),
            mmap_4k_no_page_locks(old(lctx)),
            page_objects_unlocked(old(self).page_array, old(lctx).thread_id()),
            old(lctx).lock_id_set() =~= set![
                (old(self).cpu_array.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)),
            ],
            old(lctx).stable_lock_id_set() =~= set![
                (container_lock_perm.ordering_lock_id(), KernelObjId::Container(container_ptr)),
                (process_lock_perm.ordering_lock_id(), KernelObjId::Process(process_ptr)),
                (thread_lock_perm.ordering_lock_id(), KernelObjId::Thread(thread_ptr)),
                (pagetable_lock_perm.ordering_lock_id(), KernelObjId::PageTable(pagetable_ptr)),
            ],
        ensures
            final(self).inv(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() =~= Set::<HeldLock>::empty(),
            final(lctx).stable_lock_id_set() =~= Set::<HeldLock>::empty(),
            final(self).all_objects_unlocked(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(steps).steps.len() == old(steps).steps.len() + range.len,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            final(self).pagetable_map.dom().contains(pagetable_ptr),
            mmap_4k_range_mapped(
                final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
                true,
                true,
            ),
            mmap_4k_raw_range_mapped(
                final(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range.start,
                range.len,
                true,
                true,
            ),
    {
        assert(self.pagetable_map.spec_index(pagetable_ptr).view().wf()) by {
            reveal(pagetable_perms_wf);
        };
        let mut prepared_i: usize = 0;
        while prepared_i < range.len
            invariant
                mmap_4k_held_context(
                    self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                    container_ptr, cpu_id, pagetable_ptr, &thread_lock_perm,
                    &pagetable_lock_perm,
                ),
                steps.steps == old(steps).steps,
                steps.snap_shot == kernel_k_to_kernel_u(*self),
                range.wf(),
                range.len > 0,
                0 <= prepared_i <= range.len,
                credit == 4 * range.len,
                cpu_lock_perm.state() is WriteLock,
                cpu_lock_perm.thread_id() == lctx.thread_id(),
                cpu_lock_perm.lock_id()
                    == self.cpu_array.spec_index(cpu_id).view()
                        .locking_thread()->Write_lock_id,
                self.container_map.spec_index(container_ptr).being_killed() == false,
                container_lock_perm.state() is WriteLock,
                container_lock_perm.thread_id() == lctx.thread_id(),
                container_lock_perm.lock_id()
                    == self.container_map.spec_index(container_ptr)
                        .locking_thread()->Write_lock_id,
                self.process_map.spec_index(process_ptr).being_killed() == false,
                self.process_map.spec_index(process_ptr).view().pagetable
                    == pagetable_ptr,
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == lctx.thread_id(),
                process_lock_perm.lock_id()
                    == self.process_map.spec_index(process_ptr)
                        .locking_thread()->Write_lock_id,
                self.thread_map.spec_index(thread_ptr).view().quota_4k
                    >= 4 * range.len - 3 * prepared_i,
                thread_effective_quota_4k(
                    self.thread_map.spec_index(thread_ptr),
                ) >= 4 * range.len - 3 * prepared_i,
                self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                self.thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_clean(),
                self.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                mmap_4k_range_empty(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                ),
                mmap_4k_range_prepared_prefix(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    prepared_i as int,
                ),
                mmap_4k_no_page_locks(&*lctx),
                page_objects_unlocked(self.page_array, lctx.thread_id()),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                lctx.stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            decreases range.len - prepared_i,
        {
            let current_va = range.index(prepared_i);
            self.prepare_one_mmap_4k_path(
                alloc_ptr_4k,
                thread_ptr,
                process_ptr,
                container_ptr,
                cpu_id,
                pagetable_ptr,
                current_va,
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                Tracked(&thread_lock_perm),
                Tracked(&pagetable_lock_perm),
            );
            assert(mmap_4k_range_empty(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            )) by {
                reveal(PageTable::wf_mapping_4k);
                reveal(PageTable::wf_mapping_2m);
                reveal(PageTable::wf_mapping_1g);
            };
            assert(mmap_4k_range_prepared_prefix(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range,
                (prepared_i + 1) as int,
            )) by {
                pagetable_prepare_advances_range_prefix_forall();
            };
            prepared_i = prepared_i + 1;
        }
        let mut i: usize = 0;
        while i < range.len
            invariant
                mmap_4k_held_context(
                    self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                    container_ptr, cpu_id, pagetable_ptr, &thread_lock_perm,
                    &pagetable_lock_perm,
                ),
                steps.snap_shot == kernel_k_to_kernel_u(*self),
                range.wf(),
                range.len > 0,
                0 <= i <= range.len,
                steps.steps.len() == old(steps).steps.len() + i,
                credit == 4 * range.len,
                cpu_lock_perm.state() is WriteLock,
                cpu_lock_perm.thread_id() == lctx.thread_id(),
                cpu_lock_perm.lock_id()
                    == self.cpu_array.spec_index(cpu_id).view()
                        .locking_thread()->Write_lock_id,
                self.container_map.spec_index(container_ptr).being_killed() == false,
                container_lock_perm.state() is WriteLock,
                container_lock_perm.thread_id() == lctx.thread_id(),
                container_lock_perm.lock_id()
                    == self.container_map.spec_index(container_ptr)
                        .locking_thread()->Write_lock_id,
                self.process_map.spec_index(process_ptr).being_killed() == false,
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == lctx.thread_id(),
                self.process_map.spec_index(process_ptr).view().pagetable
                    == pagetable_ptr,
                process_lock_perm.lock_id()
                    == self.process_map.spec_index(process_ptr)
                        .locking_thread()->Write_lock_id,
                self.thread_map.spec_index(thread_ptr).view().quota_4k
                    >= range.len - i,
                thread_effective_quota_4k(
                    self.thread_map.spec_index(thread_ptr),
                ) >= range.len - i,
                self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                self.thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_clean(),
                self.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                mmap_4k_range_mapped_prefix(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    i as int,
                    true,
                    true,
                ),
                mmap_4k_range_empty_from(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    i as int,
                ),
                mmap_4k_range_prepared(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                ),
                mmap_4k_no_page_locks(&*lctx),
                page_objects_unlocked(self.page_array, lctx.thread_id()),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                lctx.stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            decreases range.len - i,
        {
            let current_va = range.index(i);
            self.map_one_mmap_4k_page(
                alloc_ptr_4k,
                thread_ptr,
                process_ptr,
                container_ptr,
                cpu_id,
                pagetable_ptr,
                current_va,
                range,
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                Tracked(&thread_lock_perm),
                Tracked(&pagetable_lock_perm),
            );
            assert(mmap_4k_range_mapped_prefix(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range,
                (i + 1) as int,
                true,
                true,
            )) by {
                reveal(pagetable_perms_wf);
                pagetable_4k_insert_advances_range_prefix_forall();
            };
            assert(mmap_4k_range_empty_from(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range,
                (i + 1) as int,
            )) by {
                reveal(pagetable_perms_wf);
                pagetable_4k_insert_preserves_range_suffix_forall();
            };
            i = i + 1;
        }

        proof {
            assert({
                &&& lctx.lock_id_set() =~= set![
                    (self.cpu_array.lock_id_by_index(cpu_id), KernelObjId::Cpu(cpu_id)),
                ]
                &&& lctx.stable_lock_id_set() =~= set![
                    (container_lock_perm.ordering_lock_id(), KernelObjId::Container(container_ptr)),
                    (process_lock_perm.ordering_lock_id(), KernelObjId::Process(process_ptr)),
                    (thread_lock_perm.ordering_lock_id(), KernelObjId::Thread(thread_ptr)),
                    (pagetable_lock_perm.ordering_lock_id(), KernelObjId::PageTable(pagetable_ptr)),
                ]
                &&& self.cpu_array.lock_id_by_index(cpu_id)
                    == old(self).cpu_array.lock_id_by_index(cpu_id)
            }) by {
                broadcast use vstd::set::group_set_lemmas;
                reveal(lock_id_aligned);
            };
        }
        self.wunlock_pagetable(
            pagetable_ptr,
            Tracked(&mut *lctx),
            Tracked(pagetable_lock_perm),
        );
        self.wunlock_thread(
            thread_ptr,
            Tracked(&mut *lctx),
            Tracked(thread_lock_perm),
        );
        self.wunlock_process(
            process_ptr,
            Tracked(&mut *lctx),
            Tracked(process_lock_perm),
        );
        self.wunlock_container(
            container_ptr,
            Tracked(&mut *lctx),
            Tracked(container_lock_perm),
        );
        self.wunlock_cpu(
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(cpu_lock_perm),
        );
        proof {
            steps.end_kernel_step(&*self, &*lctx);
            assert(mmap_4k_raw_range_mapped(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range.start,
                range.len,
                true,
                true,
            )) by {
                mmap_4k_range_mapped_implies_raw(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    true,
                    true,
                );
            };
        }
    }
}

} // verus!
