use super::*;
use vstd::prelude::*;
use crate::*;

verus! {

impl KernelK {
    /// Pop and stage one 4K page while every cache and the global pool of the
    /// allocator are already write-locked.  This is the allocation primitive
    /// for mmap: the allocator locks are acquired before the PageTable lock and
    /// remain held across every page-table update in the range.
    ///
    /// A cache is preferred.  If every cache is empty, allocator conservation
    /// and the thread's remaining effective quota force the global pool to be
    /// non-empty.  The selected Free4k page has major
    /// `FREE_PAGE_LOCK_MAJOR`; hence a PageTable lock (and every other held
    /// object below that major) may remain held while the page slot is acquired.
    pub(crate) fn pop_stage_4k_page_with_allocator_locked(
        &mut self,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            cpu_id_valid(cpu_id),
            old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).container_map.dom().contains(container_ptr),
            old(self).process_map.dom().contains(process_ptr),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == process_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr,
            old(self).container_map.spec_index(container_ptr).view_rodata().view()
                .allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id()
                == old(self).thread_map.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= 1,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            Self::cache_perms_match_lctx(
                old(self).allocator_4k_map,
                alloc_ptr_4k,
                old(lctx),
                cache_perms,
            ),
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(self).pagetable_map.spec_index(pagetable_ptr)
                .wlocked_by(old(lctx)),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id()
                == old(self).pagetable_map.spec_index(pagetable_ptr)
                    .locking_thread()->Write_lock_id,
            forall|held_lock_id: LockId|
                #![trigger old(lctx).lock_id_set().contains(held_lock_id)]
                old(lctx).lock_id_set().contains(held_lock_id)
                    ==> held_lock_id.major < FREE_PAGE_LOCK_MAJOR,
        ensures
            final(self).inv(),
            kernel_k_to_kernel_u(*final(self))
                == kernel_k_to_kernel_u(*old(self)),
            final(lctx).wf(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state()
                == old(lctx).user_view_locking_state(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set().insert(
                final(self).page_array.lock_id_by_index(
                    page_ptr2page_index(ret.0),
                ),
            ),
            final(lctx).lock_maps_inserted(
                old(lctx),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
                final(self).page_array.lock_id_by_index(
                    page_ptr2page_index(ret.0),
                ),
            ),
            forall|held_lock_id: LockId|
                #![trigger final(lctx).lock_id_set().contains(held_lock_id)]
                final(lctx).lock_id_set().contains(held_lock_id)
                    ==> held_lock_id.major < FREE_PAGE_LOCK_MAJOR,
            page_ptr_valid(ret.0),
            old(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state is Free4k,
            !old(self).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_4k.view().contains(ret.0),
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).page_array.unchanged_except(
                &old(self).page_array,
                page_ptr2page_index(ret.0),
            ),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().being_killed() == false,
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state == (PageState::Owned4k { thread_ptr }),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().owning_container == container_ptr,
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().wlocked_by(final(lctx)),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().locked_by(final(lctx)),
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            ret.1.view().lock_id()
                == final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                    .view().locking_thread()->Write_lock_id,
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.spec_index(thread_ptr)
                .wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr)
                .locked_by(final(lctx)),
            thread_lock_perm.lock_id()
                == final(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
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
            final(self).thread_map.spec_index(thread_ptr).view().owning_container
                == old(self).thread_map.spec_index(thread_ptr).view().owning_container,
            final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(self).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            Self::cache_perms_match_lctx(
                final(self).allocator_4k_map,
                alloc_ptr_4k,
                final(lctx),
                cache_perms,
            ),
            final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(final(lctx)),
            global_pool_lock_perm.lock_id()
                == final(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.locking_thread()->Write_lock_id,
            final(self).pagetable_map == old(self).pagetable_map,
            final(self).pagetable_map.spec_index(pagetable_ptr)
                .wlocked_by(final(lctx)),
            pagetable_lock_perm.lock_id()
                == final(self).pagetable_map.spec_index(pagetable_ptr)
                    .locking_thread()->Write_lock_id,
            final(self).process_map == old(self).process_map,
            final(self).process_map.spec_index(process_ptr)
                .wlocked_by(final(lctx)),
            final(self).container_map == old(self).container_map,
            final(self).cpu_array == old(self).cpu_array,
            final(self).cpu_array.spec_index(cpu_id).view()
                .wlocked_by(final(lctx)),
            final(self).scheduler_map == old(self).scheduler_map,
            final(self).pcid_allocator_map == old(self).pcid_allocator_map,
    {
        let (found, slot) = self.scan_caches_and_alloc(
            alloc_ptr_4k,
            thread_ptr,
            container_ptr,
            Tracked(&mut *lctx),
            Tracked(cache_perms),
            Tracked(thread_lock_perm),
        );

        if found {
            let (_cache_cpu, page_ptr, Tracked(page_lock_perm)) = slot.unwrap();
            return (page_ptr, Tracked(page_lock_perm));
        }

        assert(
            self.allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().len() > 0
        ) by {
            assert(self.container_map.spec_index(container_ptr)
                .view_user_ghost().owned_threads.view().contains(thread_ptr)) by { reveal(container_thread_wf); };
            lemma_scan_fail_pool_nonempty(
                self,
                container_ptr,
                alloc_ptr_4k,
                thread_ptr,
            );
            reveal(allocator_perms_wf);
            self.allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.view().lemma_len_view();
        };
        assert(lctx.lock_id_acyclic(
            self.page_array.lock_id_by_index(page_ptr2page_index(
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view().spec_index(0),
            )),
        )) by {
            assert(page_ptr_valid(
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view().spec_index(0),
            )) by {
                reveal(allocator_free_page_ptrs_wf);
                reveal(allocator_perms_wf);
            };
            assert(page_index_wf(page_ptr2page_index(
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.view().view().spec_index(0),
            ))) by { page_ptr_lemma1(); };
            reveal(allocator_perms_wf);
            reveal(container_allocator_free_4k_page_wf);
        };
        let (page_ptr, Tracked(page_lock_perm)) = self.pop_stage_global_4k_page(
            alloc_ptr_4k,
            thread_ptr,
            container_ptr,
            Tracked(&mut *lctx),
            Tracked(global_pool_lock_perm),
            Tracked(thread_lock_perm),
        );
        assert(Self::cache_perms_match_lctx(
            self.allocator_4k_map,
            alloc_ptr_4k,
            &*lctx,
            cache_perms,
        )) by { reveal(KernelK::cache_perms_match_lctx); };
        (page_ptr, Tracked(page_lock_perm))
    }
}

} // verus!
