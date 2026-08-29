use vstd::prelude::*;
use crate::*;

use super::mmap_4k_context::{
    mmap_4k_held_context,
    mmap_4k_allocation_ready,
};


verus! {


    /// Stage one allocator page through the ordinary allocator while the
    /// lower-major process PageTable remains locked. Allocator locks are taken
    /// only for this allocation and released before returning.
    pub fn stage_mmap_4k_page(
        kernel: &mut KernelK,
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
                old(kernel), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(kernel)),
            thread_effective_quota_4k(
                old(kernel).thread_map.spec_index(thread_ptr),
            ) >= 1,
            mmap_4k_allocation_ready(old(kernel), old(lctx)),
        ensures
            mmap_4k_held_context(
                final(kernel), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert((
                final(kernel).page_array.lock_id_by_index(
                    page_ptr2page_index(ret.0),
                ),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
            )),
            final(kernel).thread_map.lock_id_by_key(thread_ptr)
                == old(kernel).thread_map.lock_id_by_key(thread_ptr),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(kernel)),
            allocator_objects_unlocked(
                final(kernel).allocator_4k_map, final(lctx).thread_id()),
            final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            final(lctx).held_lock_majors_lt(ALLOCATOR_CACHE_MAJOR),
            page_ptr_valid(ret.0),
            final(kernel).container_map.spec_index(container_ptr).view_rodata()
                == old(kernel).container_map.spec_index(container_ptr).view_rodata(),
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
            held_pagetables_unchanged(
                old(kernel).pagetable_map, final(kernel).pagetable_map, old(lctx),
            ),
            held_iommu_tables_unchanged(
                old(kernel).iommu_table_map, final(kernel).iommu_table_map,
                old(lctx),
            ),
            held_cpus_unchanged(
                old(kernel).cpu_array, final(kernel).cpu_array, old(lctx),
            ),
            forall|t: RwLockThreadPtr|
                #![trigger old(kernel).thread_map.spec_index(t)
                    .locked_by_thread(old(lctx).thread_id())]
                #![trigger final(kernel).thread_map.spec_index(t)
                    .locked_by_thread(final(lctx).thread_id())]
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
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state == (PageState::Owned4k { thread_ptr }),
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().owning_container == container_ptr,
            final(kernel).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().wlocked_by(final(lctx)),
            page_objects_unlocked_except(
                final(kernel).page_array, final(lctx).thread_id(),
                set![page_ptr2page_index(ret.0)],
            ),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id()
                == final(kernel).page_array.spec_index(page_ptr2page_index(ret.0))
                    .view().locking_thread()->Write_lock_id,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_4k.view()
                =~= old(kernel).thread_map.spec_index(thread_ptr).view()
                    .temp_alloc_cache_4k.view().insert(ret.0),
            final(kernel).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(kernel).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .upper_container_seq
                == old(kernel).thread_map.spec_index(thread_ptr).view()
                    .upper_container_seq,
            final(kernel).thread_map.spec_index(thread_ptr).view().state
                == old(kernel).thread_map.spec_index(thread_ptr).view().state,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .blocking_endpoint_ptr
                == old(kernel).thread_map.spec_index(thread_ptr).view()
                    .blocking_endpoint_ptr,
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m
                == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_2m,
            final(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g
                == old(kernel).thread_map.spec_index(thread_ptr).view().temp_alloc_cache_1g,
            final(kernel).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(kernel).thread_map.spec_index(thread_ptr).view(),
                ),
    {
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(kernel,
            thread_ptr,
            container_ptr,
            cpu_id,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(thread_lock_perm),
        );
        proof {
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
                reveal(container_process_wf);
                reveal(process_thread_wf);
                reveal(pagetable_perms_wf);
                reveal(container_allocator_wf);
            };
            assert({
                &&& kernel.thread_map.spec_index(thread_ptr).view()
                    .upper_container_seq
                    == old(kernel).thread_map.spec_index(thread_ptr).view()
                        .upper_container_seq
                &&& kernel.thread_map.spec_index(thread_ptr).view().state
                    == old(kernel).thread_map.spec_index(thread_ptr).view().state
                &&& kernel.thread_map.spec_index(thread_ptr).view()
                    .blocking_endpoint_ptr
                    == old(kernel).thread_map.spec_index(thread_ptr).view()
                        .blocking_endpoint_ptr
            }) by {
                reveal(Thread::stable_allocation_root_equal);
            };
        }
        (page_ptr, Tracked(page_lock_perm))
    }



}
