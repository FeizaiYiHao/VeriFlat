use vstd::prelude::*;
use crate::*;

use super::mmap_4k_context::{mmap_4k_held_context, mmap_4k_no_page_locks};
use super::mmap_4k_syscall_def::*;

verus! {

impl KernelK {
    /// Stage one allocator page through the ordinary allocator while the
    /// lower-major process PageTable remains locked. Allocator locks are taken
    /// only for this allocation and released before returning.
    pub(super) fn stage_mmap_4k_page(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            mmap_4k_held_context(
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= 1,
            old(self).pagetable_map.spec_index(pagetable_ptr)
                .locked_by_thread(old(lctx).thread_id()),
            mmap_4k_no_page_locks(old(lctx)),
            page_objects_unlocked(old(self).page_array, old(lctx).thread_id()),
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((
                final(self).page_array.lock_id_by_index(
                    page_ptr2page_index(ret.0),
                ),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
            )),
            final(lctx).stable_lock_id_set() == old(lctx).stable_lock_id_set(),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            page_ptr_valid(ret.0),
            index_valid(NUM_PAGES, page_ptr2page_index(ret.0)),
            final(self).container_map.spec_index(container_ptr)
                == old(self).container_map.spec_index(container_ptr),
            final(self).container_map.spec_index(container_ptr).view_rodata()
                == old(self).container_map.spec_index(container_ptr).view_rodata(),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state == (PageState::Owned4k { thread_ptr }),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().owning_container == container_ptr,
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().wlocked_by(final(lctx)),
            forall|i: PageIndex|
                #![trigger final(self).page_array.spec_index(i)]
                index_valid(NUM_PAGES, i) && i != page_ptr2page_index(ret.0)
                ==> !final(self).page_array.spec_index(i).view()
                    .locked_by_thread(final(lctx).thread_id()),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id()
                == final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                    .view().locking_thread()->Write_lock_id,
            final(self).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_4k.view()
                =~= old(self).thread_map.spec_index(thread_ptr).view()
                    .temp_alloc_cache_4k.view().insert(ret.0),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(self).thread_map.spec_index(thread_ptr).view(),
                ),
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr)
                == old(self).pagetable_map.spec_index(pagetable_ptr),
            final(self).cpu_array.spec_index(cpu_id).view()
                == old(self).cpu_array.spec_index(cpu_id).view(),
    {
        let (page_ptr, Tracked(page_lock_perm)) = self.allocate_free_4k_page(
            alloc_ptr_4k,
            thread_ptr,
            process_ptr,
            container_ptr,
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(thread_lock_perm),
        );
        proof {
            assert({
                &&& self.page_array.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().state == (PageState::Owned4k { thread_ptr })
                &&& self.page_array.spec_index(page_ptr2page_index(page_ptr))
                    .view().view().owning_container == container_ptr
                &&& self.page_array.spec_index(page_ptr2page_index(page_ptr))
                    .view().wlocked_by(&*lctx)
                &&& page_lock_perm.lock_id() == self.page_array.spec_index(
                    page_ptr2page_index(page_ptr),
                ).view().locking_thread()->Write_lock_id
            }) by { reveal(lock_id_aligned); };
            assert({
                &&& self.container_map.dom().contains(container_ptr)
                &&& old(self).container_map.spec_index(container_ptr)
                    .locked_by_thread(old(lctx).thread_id())
                &&& self.container_map.spec_index(container_ptr)
                    .locked_by_thread(lctx.thread_id())
                &&& self.container_map.spec_index(container_ptr)
                    == old(self).container_map.spec_index(container_ptr)
                &&& self.container_map.spec_index(container_ptr).view_rodata()
                    == old(self).container_map.spec_index(container_ptr).view_rodata()
                &&& self.process_map.spec_index(process_ptr).view_rodata().view()
                    .owning_container == container_ptr
            }) by {
                reveal(container_process_wf);
            };
            assert({
                &&& self.process_map.dom().contains(process_ptr)
                &&& old(self).process_map.spec_index(process_ptr)
                    .locked_by_thread(old(lctx).thread_id())
                &&& self.process_map.spec_index(process_ptr)
                    == old(self).process_map.spec_index(process_ptr)
                &&& self.process_map.spec_index(process_ptr)
                    .locked_by_thread(lctx.thread_id())
                &&& self.thread_map.dom().contains(thread_ptr)
                &&& old(self).thread_map.spec_index(thread_ptr)
                    .locked_by_thread(old(lctx).thread_id())
                &&& self.thread_map.spec_index(thread_ptr).view()
                    .temp_alloc_cache_4k.view()
                    =~= old(self).thread_map.spec_index(thread_ptr).view()
                        .temp_alloc_cache_4k.view().insert(page_ptr)
                &&& self.thread_map.spec_index(thread_ptr).view().quota_4k
                    == old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                &&& self.thread_map.spec_index(thread_ptr).view().owning_container
                    == old(self).thread_map.spec_index(thread_ptr).view().owning_container
                &&& self.thread_map.spec_index(thread_ptr).view().owning_proc
                    == old(self).thread_map.spec_index(thread_ptr).view().owning_proc
                &&& self.thread_map.spec_index(thread_ptr).view().owning_proc
                    == process_ptr
                &&& self.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                    == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                &&& self.thread_map.spec_index(thread_ptr).being_killed() == false
                &&& self.thread_map.spec_index(thread_ptr)
                    .locked_by_thread(lctx.thread_id())
            }) by {
                reveal(process_thread_wf);
            };
            assert({
                &&& self.pagetable_map.dom().contains(pagetable_ptr)
                &&& old(self).pagetable_map.spec_index(pagetable_ptr)
                    .locked_by_thread(old(lctx).thread_id())
                &&& self.pagetable_map.spec_index(pagetable_ptr)
                    == old(self).pagetable_map.spec_index(pagetable_ptr)
                &&& self.pagetable_map.spec_index(pagetable_ptr)
                    .locked_by_thread(lctx.thread_id())
                &&& self.pagetable_map.spec_index(pagetable_ptr).view().wf()
            }) by {
                reveal(pagetable_perms_wf);
            };
            assert({
                &&& self.cpu_array.spec_index(cpu_id).view()
                    .locked_by_thread(lctx.thread_id())
                &&& self.cpu_array.spec_index(cpu_id).view()
                    == old(self).cpu_array.spec_index(cpu_id).view()
            }) by {
                reveal(lock_id_aligned);
            };
            assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
                reveal(container_allocator_wf);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

    /// Inspect the complete range while the target process PageTable remains
    /// write-locked. No kernel state or LocalContext state changes.
    pub(super) fn check_mmap_4k_range(
        &self,
        range: &VaRange4K,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&LocalContext>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Mmap4kRangeCheck)
        requires
            self.inv(),
            range.wf(),
            self.pagetable_map.dom().contains(pagetable_ptr),
            self.pagetable_map.spec_index(pagetable_ptr).wlocked_by(lctx),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == lctx.thread_id(),
            pagetable_lock_perm.lock_id()
                == self.pagetable_map.spec_index(pagetable_ptr)
                    .locking_thread()->Write_lock_id,
        ensures
            ret is Empty ==> mmap_4k_range_empty(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            ),
    {
        proof {
            assert(
                self.pagetable_map.perms_wf()
                && self.pagetable_map.spec_index(pagetable_ptr).inv()
            ) by { reveal(pagetable_perms_wf); };
        }
        let mut i: usize = 0;
        while i < range.len
            invariant
                self.inv(),
                self.pagetable_map.perms_wf(),
                self.pagetable_map.spec_index(pagetable_ptr).inv(),
                range.wf(),
                0 <= i <= range.len,
                self.pagetable_map.dom().contains(pagetable_ptr),
                self.pagetable_map.spec_index(pagetable_ptr).wlocked_by(lctx),
                pagetable_lock_perm.state() is WriteLock,
                pagetable_lock_perm.thread_id() == lctx.thread_id(),
                pagetable_lock_perm.lock_id()
                    == self.pagetable_map.spec_index(pagetable_ptr)
                        .locking_thread()->Write_lock_id,
                forall|j: int|
                    #![trigger range.view().spec_index(j)]
                    0 <= j < i
                    ==> {
                        let indices = spec_va2index(range.view().spec_index(j));
                        &&& self.pagetable_map.spec_index(pagetable_ptr).view()
                            .kernel_l4_end <= indices.0 && pei_valid(indices.0)
                        &&& pei_valid(indices.1)
                        &&& pei_valid(indices.2)
                        &&& pei_valid(indices.3)
                        &&& self.pagetable_map.spec_index(pagetable_ptr).view()
                            .spec_4k_entry_useable(
                                indices.0,
                                indices.1,
                                indices.2,
                                indices.3,
                            )
                    },
            decreases range.len - i,
        {
            let current_va = range.index(i);
            let indices = va2index(current_va);
            let pagetable = self.pagetable_map.borrow(
                pagetable_ptr,
                Tracked(pagetable_lock_perm),
            );
            if indices.0 < pagetable.kernel_l4_end {
                return Mmap4kRangeCheck::Invalid;
            }
            let (_, error_code, _) = pagetable.resolve_mapping_4k_l1(
                indices.0,
                indices.1,
                indices.2,
                indices.3,
            );
            match error_code {
                PageTableErrorCode::L4EntryNotExist
                | PageTableErrorCode::L3EntryNotExist
                | PageTableErrorCode::L2EntryNotExist
                | PageTableErrorCode::L1EntryNotExist => {},
                PageTableErrorCode::NoError
                | PageTableErrorCode::EntryTakenBy4k
                | PageTableErrorCode::EntryTakenBy2m
                | PageTableErrorCode::EntryTakenBy1g => {
                    return Mmap4kRangeCheck::InUse;
                },
            }
            i = i + 1;
        }
        Mmap4kRangeCheck::Empty
    }
}

}
