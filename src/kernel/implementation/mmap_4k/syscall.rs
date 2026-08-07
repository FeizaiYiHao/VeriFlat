use vstd::prelude::*;
use crate::*;

use super::syscall_def::*;

verus! {

impl KernelK {
    /// Every permission already collected for the current mapping bundle still
    /// names a staged page owned by `thread_ptr`.  The predicate is opaque so
    /// repeated allocator boundaries do not expose its quantifier globally.
    #[verifier::opaque]
    pub open spec fn mmap_4k_staged_page_perms_match(
        &self,
        thread_ptr: RwLockThreadPtr,
        lctx: &LocalContext,
        page_lock_perms: &Map<PagePtr, LockPerm>,
    ) -> bool {
        forall|page_ptr: PagePtr|
            #![trigger page_lock_perms.dom().contains(page_ptr)]
            #![trigger self.create_4k_entry_page_ready(
                page_ptr,
                thread_ptr,
                lctx,
                page_lock_perms,
            )]
            page_lock_perms.dom().contains(page_ptr)
            ==> self.create_4k_entry_page_ready(
                page_ptr,
                thread_ptr,
                lctx,
                page_lock_perms,
            )
    }

    /// Stage one allocator page and immediately close its kernel-only atomic
    /// section. All allocator sources and the process PageTable stay locked,
    /// so the following bundle page can be selected without reopening any
    /// lower-order lock.
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
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
        Tracked(staged_page_lock_perms): Tracked<&Map<PagePtr, LockPerm>>,
    ) -> (ret: (PagePtr, Tracked<LockPerm>))
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).user_view_locking_state() is Acquire,
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            cpu_id_valid(cpu_id),
            old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).container_map.dom().contains(container_ptr),
            old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
            old(self).process_map.dom().contains(process_ptr),
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == process_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == pagetable_ptr,
            old(self).process_map.spec_index(process_ptr).view_rodata().view()
                .owning_container == container_ptr,
            old(self).container_map.spec_index(container_ptr).view_rodata().view()
                .allocator_ptr_4k == alloc_ptr_4k,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id()
                == old(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
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
            old(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
            old(self).mmap_4k_staged_page_perms_match(
                thread_ptr,
                old(lctx),
                staged_page_lock_perms,
            ),
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
            final(lctx).wf(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).user_view_locking_state() is Acquire,
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(lctx).lock_maps_inserted(
                old(lctx),
                KernelObjId::Page(page_ptr2page_index(ret.0)),
                final(self).page_array.lock_id_by_index(
                    page_ptr2page_index(ret.0),
                ),
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            final(self).mmap_4k_staged_page_perms_match(
                thread_ptr,
                final(lctx),
                staged_page_lock_perms,
            ),
            !old(lctx).page_lock_map().dom().contains(
                page_ptr2page_index(ret.0),
            ),
            !staged_page_lock_perms.dom().contains(ret.0),
            page_ptr_valid(ret.0),
            page_index_wf(page_ptr2page_index(ret.0)),
            final(self).container_map.dom().contains(container_ptr),
            final(self).container_map.spec_index(container_ptr).wlocked_by(final(lctx)),
            final(self).container_map.spec_index(container_ptr)
                == old(self).container_map.spec_index(container_ptr),
            final(self).container_map.spec_index(container_ptr).view_rodata()
                == old(self).container_map.spec_index(container_ptr).view_rodata(),
            final(self).process_map.dom().contains(process_ptr),
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).pagetable_map.dom().contains(pagetable_ptr),
            final(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().state == (PageState::Owned4k { thread_ptr }),
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().view().owning_container == container_ptr,
            final(self).page_array.spec_index(page_ptr2page_index(ret.0))
                .view().wlocked_by(final(lctx)),
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
            final(self).thread_map.spec_index(thread_ptr).view().owning_container
                == old(self).thread_map.spec_index(thread_ptr).view().owning_container,
            final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == old(self).thread_map.spec_index(thread_ptr).view().owning_proc,
            final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr,
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            thread_lock_perm.lock_id()
                == final(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr)
                == old(self).pagetable_map.spec_index(pagetable_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(final(lctx)),
            pagetable_lock_perm.lock_id()
                == final(self).pagetable_map.spec_index(pagetable_ptr)
                    .locking_thread()->Write_lock_id,
            final(self).cpu_array.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(self).cpu_array.spec_index(cpu_id).view()
                == old(self).cpu_array.spec_index(cpu_id).view(),
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
            forall|held_lock_id: LockId|
                #![trigger final(lctx).lock_id_set().contains(held_lock_id)]
                final(lctx).lock_id_set().contains(held_lock_id)
                ==> held_lock_id.major < FREE_PAGE_LOCK_MAJOR,
    {
        let (page_ptr, Tracked(page_lock_perm)) =
            self.pop_stage_4k_page_with_allocator_locked(
                alloc_ptr_4k,
                thread_ptr,
                process_ptr,
                container_ptr,
                cpu_id,
                pagetable_ptr,
                Tracked(&mut *lctx),
                Tracked(cache_perms),
                Tracked(global_pool_lock_perm),
                Tracked(thread_lock_perm),
                Tracked(pagetable_lock_perm),
            );
        proof {
            assert(!staged_page_lock_perms.dom().contains(page_ptr)) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
            assert(!old(lctx).page_lock_map().dom().contains(
                page_ptr2page_index(page_ptr),
            )) by {
                reveal(LocalContext::wf);
                reveal(page_lock_id_aligned);
            };
            self.kernel_step_boundary(&mut *lctx, &mut *steps);
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
            }) by { reveal(page_locked_match_lctx); };
            assert({
                &&& self.container_map.dom().contains(container_ptr)
                &&& self.container_map.spec_index(container_ptr).wlocked_by(&*lctx)
                &&& self.container_map.spec_index(container_ptr)
                    == old(self).container_map.spec_index(container_ptr)
                &&& self.container_map.spec_index(container_ptr).view_rodata()
                    == old(self).container_map.spec_index(container_ptr).view_rodata()
                &&& self.process_map.dom().contains(process_ptr)
                &&& self.process_map.spec_index(process_ptr)
                    == old(self).process_map.spec_index(process_ptr)
                &&& self.process_map.spec_index(process_ptr).wlocked_by(&*lctx)
                &&& self.thread_map.dom().contains(thread_ptr)
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
                &&& self.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                    == old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                &&& self.thread_map.spec_index(thread_ptr).being_killed() == false
                &&& self.thread_map.spec_index(thread_ptr).wlocked_by(&*lctx)
            }) by {
                reveal(container_process_wf);
                reveal(container_locked_match_lctx);
                reveal(process_locked_match_lctx);
                reveal(thread_locked_match_lctx);
            };
            assert(self.mmap_4k_staged_page_perms_match(
                thread_ptr,
                &*lctx,
                staged_page_lock_perms,
            )) by {
                assert(boundary_pages_preserved(old(self), self, old(lctx))) by {
                    reveal(LocalContext::wf);
                    reveal(page_locked_match_lctx);
                };
                reveal(KernelK::mmap_4k_staged_page_perms_match);
                reveal(page_locked_match_lctx);
                page_ptr_lemma1();
            };
            assert({
                &&& self.pagetable_map.dom().contains(pagetable_ptr)
                &&& self.pagetable_map.spec_index(pagetable_ptr)
                    == old(self).pagetable_map.spec_index(pagetable_ptr)
                &&& self.pagetable_map.spec_index(pagetable_ptr).wlocked_by(&*lctx)
                &&& self.cpu_array.spec_index(cpu_id).view().wlocked_by(&*lctx)
                &&& self.cpu_array.spec_index(cpu_id).view()
                    == old(self).cpu_array.spec_index(cpu_id).view()
            }) by {
                reveal(pagetable_locked_match_lctx);
                reveal(cpu_locked_match_lctx);
            };
            assert(Self::cache_perms_match_lctx(
                self.allocator_4k_map,
                alloc_ptr_4k,
                &*lctx,
                cache_perms,
            )) by {
                reveal(KernelK::cache_perms_match_lctx);
                reveal(allocator_4k_locked_match_lctx);
            };
            assert({
                &&& self.allocator_4k_map.dom().contains(alloc_ptr_4k)
                &&& self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx)
                &&& global_pool_lock_perm.lock_id()
                    == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.locking_thread()->Write_lock_id
            }) by { reveal(allocator_4k_locked_match_lctx); };
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
                            .kernel_l4_end <= indices.0 < 512
                        &&& 0 <= indices.1 < 512
                        &&& 0 <= indices.2 < 512
                        &&& 0 <= indices.3 < 512
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
