use vstd::prelude::*;
use crate::*;

use super::mmap_4k_context::{
    mmap_4k_held_context,
    mmap_4k_allocation_ready,
    mmap_4k_other_objects_unlocked,
};

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
            mmap_4k_allocation_ready(old(self), old(lctx)),
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
            assert(self.allocator_4k_map.dom().contains(alloc_ptr_4k)) by {
                reveal(container_allocator_wf);
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
                reveal(thread_objects_unlocked_except);
                lock_id_fields_eq_imply_eq();
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }

}

}
