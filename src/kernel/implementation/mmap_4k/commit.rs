use vstd::prelude::*;
use vstd::assert_sets_equal;

use crate::*;

use super::Create4kEntryPages;
use super::range_framing::{
    pagetable_4k_insert_advances_range_prefix_forall,
    pagetable_4k_insert_preserves_range_suffix_forall,
};
use super::raw_range::mmap_4k_range_mapped_implies_raw;
use super::syscall_def::*;

verus! {

impl KernelK {
    /// Commit every mapping in an already checked range.  All allocator
    /// sources and all user-visible objects stay locked between iterations;
    /// only the staged page bundle is acquired and released per VA.
    pub(super) fn commit_mmap_4k_range(
        &mut self,
        range: &VaRange4K,
        credit: usize,
        original_process_quota: usize,
        original_thread_quota: usize,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(cache_perms): Tracked<Map<CpuId, LockPerm>>,
        Tracked(global_pool_lock_perm): Tracked<LockPerm>,
        Tracked(thread_lock_perm): Tracked<LockPerm>,
        Tracked(process_lock_perm): Tracked<LockPerm>,
        Tracked(container_lock_perm): Tracked<LockPerm>,
        Tracked(cpu_lock_perm): Tracked<LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<LockPerm>,
    )
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).user_view_locking_state() is Acquire,
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            range.wf(),
            range.len > 0,
            credit == 4 * range.len,
            original_process_quota >= credit,
            credit <= usize::MAX - original_thread_quota,
            cpu_id_valid(cpu_id),
            old(self).cpu_array.spec_index(cpu_id).view().being_killed() == false,
            old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            cpu_lock_perm.state() is WriteLock,
            cpu_lock_perm.thread_id() == old(lctx).thread_id(),
            cpu_lock_perm.lock_id()
                == old(self).cpu_array.spec_index(cpu_id).view()
                    .locking_thread()->Write_lock_id,
            old(self).container_map.dom().contains(container_ptr),
            old(self).container_map.spec_index(container_ptr).being_killed() == false,
            old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
            old(self).container_map.spec_index(container_ptr).view_rodata().view()
                .allocator_ptr_4k == alloc_ptr_4k,
            container_lock_perm.state() is WriteLock,
            container_lock_perm.thread_id() == old(lctx).thread_id(),
            container_lock_perm.lock_id()
                == old(self).container_map.spec_index(container_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr).view_rodata().view()
                .owning_container == container_ptr,
            old(self).process_map.spec_index(process_ptr).view().pagetable
                == pagetable_ptr,
            old(self).process_map.spec_index(process_ptr).view().quota_4k
                == original_process_quota - credit,
            process_lock_perm.state() is WriteLock,
            process_lock_perm.thread_id() == old(lctx).thread_id(),
            process_lock_perm.lock_id()
                == old(self).process_map.spec_index(process_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == process_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == pagetable_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == original_thread_quota + credit,
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id()
                == old(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.dom().contains(alloc_ptr_4k),
            Self::cache_perms_match_lctx(
                old(self).allocator_4k_map,
                alloc_ptr_4k,
                old(lctx),
                &cache_perms,
            ),
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == old(lctx).thread_id(),
            global_pool_lock_perm.lock_id()
                == old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.locking_thread()->Write_lock_id,
            old(self).allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.wlocked_by(old(lctx)),
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id()
                == old(self).pagetable_map.spec_index(pagetable_ptr)
                    .locking_thread()->Write_lock_id,
            mmap_4k_range_empty(
                old(self).pagetable_map.spec_index(pagetable_ptr).view(),
                range,
            ),
            old(lctx).page_lock_map().dom() =~= Set::<PageIndex>::empty(),
            old(lctx).lock_id_set() =~= set![
                old(lctx).cpu_lock_map().spec_index(cpu_id),
                old(lctx).container_lock_map().spec_index(container_ptr),
                old(lctx).process_lock_map().spec_index(process_ptr),
                old(lctx).thread_lock_map().spec_index(thread_ptr),
                old(lctx).allocator_4k_lock_map().spec_index(
                    AllocatorLockObjId::GlobalPool(alloc_ptr_4k),
                ),
                old(lctx).pagetable_lock_map().spec_index(pagetable_ptr),
            ] + Self::allocator_cache_lock_id_prefix(NUM_CPUS),
            forall|held_lock_id: LockId|
                #![trigger old(lctx).lock_id_set().contains(held_lock_id)]
                old(lctx).lock_id_set().contains(held_lock_id)
                ==> held_lock_id.major < FREE_PAGE_LOCK_MAJOR,
        ensures
            final(self).inv(),
            final(lctx).wf(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Acquire,
            final(lctx).lock_id_set() =~= Set::<LockId>::empty(),
            final(self).locked_objects_match_lctx(final(lctx)),
            lock_id_aligned(final(self), final(lctx)),
            final(steps).steps.len() == old(steps).steps.len() + range.len,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            final(steps).steps.last().new_k == *final(self),
            final(steps).steps.last().new_u
                == kernel_k_to_kernel_u(*final(self)),
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
        let mut i: usize = 0;
        while i + 1 < range.len
            invariant
                self.inv(),
                lctx.wf(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
                self.locked_objects_match_lctx(&*lctx),
                lock_id_aligned(self, &*lctx),
                steps.snap_shot == kernel_k_to_kernel_u(*self),
                range.wf(),
                range.len > 0,
                0 <= i < range.len,
                steps.steps.len() == old(steps).steps.len() + i,
                credit == 4 * range.len,
                original_process_quota >= credit,
                credit <= usize::MAX - original_thread_quota,
                cpu_id_valid(cpu_id),
                self.cpu_array.spec_index(cpu_id).view().being_killed() == false,
                self.cpu_array.spec_index(cpu_id).view().wlocked_by(&*lctx),
                cpu_lock_perm.state() is WriteLock,
                cpu_lock_perm.thread_id() == lctx.thread_id(),
                cpu_lock_perm.lock_id()
                    == self.cpu_array.spec_index(cpu_id).view()
                        .locking_thread()->Write_lock_id,
                self.container_map.dom().contains(container_ptr),
                self.container_map.spec_index(container_ptr).being_killed() == false,
                self.container_map.spec_index(container_ptr).wlocked_by(&*lctx),
                self.container_map.spec_index(container_ptr).view_rodata().view()
                    .allocator_ptr_4k == alloc_ptr_4k,
                container_lock_perm.state() is WriteLock,
                container_lock_perm.thread_id() == lctx.thread_id(),
                container_lock_perm.lock_id()
                    == self.container_map.spec_index(container_ptr)
                        .locking_thread()->Write_lock_id,
                self.process_map.dom().contains(process_ptr),
                self.process_map.spec_index(process_ptr).being_killed() == false,
                self.process_map.spec_index(process_ptr).wlocked_by(&*lctx),
                self.process_map.spec_index(process_ptr).view_rodata().view()
                    .owning_container == container_ptr,
                self.process_map.spec_index(process_ptr).view().pagetable
                    == pagetable_ptr,
                self.process_map.spec_index(process_ptr).view().quota_4k
                    == original_process_quota - credit,
                process_lock_perm.state() is WriteLock,
                process_lock_perm.thread_id() == lctx.thread_id(),
                process_lock_perm.lock_id()
                    == self.process_map.spec_index(process_ptr)
                        .locking_thread()->Write_lock_id,
                self.thread_map.dom().contains(thread_ptr),
                self.thread_map.spec_index(thread_ptr).being_killed() == false,
                self.thread_map.spec_index(thread_ptr).wlocked_by(&*lctx),
                self.thread_map.spec_index(thread_ptr).view().owning_proc
                    == process_ptr,
                self.thread_map.spec_index(thread_ptr).view().owning_container
                    == container_ptr,
                self.thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                    == pagetable_ptr,
                self.thread_map.spec_index(thread_ptr).view().quota_4k
                    >= original_thread_quota + 4 * (range.len - i),
                self.thread_map.spec_index(thread_ptr).view().quota_4k
                    <= original_thread_quota + credit,
                self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                self.thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_clean(),
                thread_lock_perm.state() is WriteLock,
                thread_lock_perm.thread_id() == lctx.thread_id(),
                thread_lock_perm.lock_id()
                    == self.thread_map.spec_index(thread_ptr)
                        .locking_thread()->Write_lock_id,
                self.allocator_4k_map.dom().contains(alloc_ptr_4k),
                Self::cache_perms_match_lctx(
                    self.allocator_4k_map,
                    alloc_ptr_4k,
                    &*lctx,
                    &cache_perms,
                ),
                global_pool_lock_perm.state() is WriteLock,
                global_pool_lock_perm.thread_id() == lctx.thread_id(),
                global_pool_lock_perm.lock_id()
                    == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.locking_thread()->Write_lock_id,
                self.allocator_4k_map.spec_index(alloc_ptr_4k)
                    .global_pool.wlocked_by(&*lctx),
                self.pagetable_map.dom().contains(pagetable_ptr),
                self.pagetable_map.spec_index(pagetable_ptr).wlocked_by(&*lctx),
                pagetable_lock_perm.state() is WriteLock,
                pagetable_lock_perm.thread_id() == lctx.thread_id(),
                pagetable_lock_perm.lock_id()
                    == self.pagetable_map.spec_index(pagetable_ptr)
                        .locking_thread()->Write_lock_id,
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
                lctx.page_lock_map().dom() =~= Set::<PageIndex>::empty(),
                lctx.lock_id_set() =~= old(lctx).lock_id_set(),
                lctx.lock_maps_equal(old(lctx)),
                forall|held_lock_id: LockId|
                    #![trigger lctx.lock_id_set().contains(held_lock_id)]
                    lctx.lock_id_set().contains(held_lock_id)
                    ==> held_lock_id.major < FREE_PAGE_LOCK_MAJOR,
            decreases range.len - i,
        {
            let current_va = range.index(i);
            assert(self.pagetable_map.spec_index(pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
            let (pages, _, Tracked(page_lock_perms)) =
                self.allocate_mmap_4k_bundle(
                    alloc_ptr_4k,
                    thread_ptr,
                    process_ptr,
                    container_ptr,
                    cpu_id,
                    pagetable_ptr,
                    current_va,
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    Tracked(&cache_perms),
                    Tracked(&global_pool_lock_perm),
                    Tracked(&thread_lock_perm),
                    Tracked(&pagetable_lock_perm),
                );

            proof {
                steps.begin_user_view_step(&*self, &mut *lctx);
            }
            self.create_4k_entry(
                pages,
                thread_ptr,
                pagetable_ptr,
                current_va,
                true,
                true,
                Tracked(&mut *lctx),
                Tracked(&page_lock_perms),
                Tracked(&thread_lock_perm),
                Tracked(&pagetable_lock_perm),
            );
            assert(self.pagetable_map.spec_index(pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
            assert(
                mmap_4k_range_mapped_prefix(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    (i + 1) as int,
                    true,
                    true,
                )
                && mmap_4k_range_empty_from(
                    self.pagetable_map.spec_index(pagetable_ptr).view(),
                    range,
                    (i + 1) as int,
                )
            ) by { pagetable_4k_insert_advances_range_prefix_forall(); pagetable_4k_insert_preserves_range_suffix_forall(); };
            self.wunlock_mmap_4k_bundle_pages(
                pages,
                Tracked(&mut *lctx),
                Tracked(page_lock_perms),
            );
            assert(
                self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean()
                && lctx.page_lock_map().dom() =~= Set::<PageIndex>::empty()
                && lctx.lock_id_set() =~= old(lctx).lock_id_set()
                && lctx.lock_maps_equal(old(lctx))
            ) by {
                reveal(LocalContext::wf);
                match pages {
                    Create4kEntryPages::DataOnly { .. } => {},
                    Create4kEntryPages::L1AndData { .. } => {},
                    Create4kEntryPages::L2L1AndData { .. } => {},
                    Create4kEntryPages::L3L2L1AndData { .. } => {},
                }
            };
            proof {
                steps.end_user_view_step(&*self, &mut *lctx);
                assert(Self::cache_perms_match_lctx(
                    self.allocator_4k_map,
                    alloc_ptr_4k,
                    &*lctx,
                    &cache_perms,
                )
                    && self.allocator_4k_map.spec_index(alloc_ptr_4k)
                        .global_pool.wlocked_by(&*lctx)
                ) by { reveal(KernelK::cache_perms_match_lctx); };
                self.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(Self::cache_perms_match_lctx(
                    self.allocator_4k_map,
                    alloc_ptr_4k,
                    &*lctx,
                    &cache_perms,
                )) by { reveal(KernelK::cache_perms_match_lctx); };
                assert(
                    self.thread_map.spec_index(thread_ptr).view()
                        .temp_alloc_clean()
                    && lctx.page_lock_map().dom() =~= Set::<PageIndex>::empty()
                    && lctx.lock_id_set() =~= old(lctx).lock_id_set()
                    && lctx.lock_maps_equal(old(lctx))
                ) by {
                    reveal(LocalContext::wf);
                    reveal(container_locked_match_lctx);
                    reveal(process_locked_match_lctx);
                    reveal(thread_locked_match_lctx);
                    reveal(pagetable_locked_match_lctx);
                    reveal(cpu_locked_match_lctx);
                    reveal(allocator_4k_locked_match_lctx);
                };
                assert(
                    mmap_4k_range_mapped_prefix(
                        self.pagetable_map.spec_index(pagetable_ptr).view(),
                        range,
                        (i + 1) as int,
                        true,
                        true,
                    )
                    && mmap_4k_range_empty_from(
                        self.pagetable_map.spec_index(pagetable_ptr).view(),
                        range,
                        (i + 1) as int,
                    )
                ) by { reveal(pagetable_locked_match_lctx); };
            }
            i = i + 1;
        }

        let current_va = range.index(i);
        assert(self.pagetable_map.spec_index(pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
        let (pages, _, Tracked(page_lock_perms)) =
            self.allocate_mmap_4k_bundle(
                alloc_ptr_4k,
                thread_ptr,
                process_ptr,
                container_ptr,
                cpu_id,
                pagetable_ptr,
                current_va,
                Tracked(&mut *lctx),
                Tracked(&mut *steps),
                Tracked(&cache_perms),
                Tracked(&global_pool_lock_perm),
                Tracked(&thread_lock_perm),
                Tracked(&pagetable_lock_perm),
            );
        proof {
            steps.begin_user_view_step(&*self, &mut *lctx);
        }
        self.create_4k_entry(
            pages,
            thread_ptr,
            pagetable_ptr,
            current_va,
            true,
            true,
            Tracked(&mut *lctx),
            Tracked(&page_lock_perms),
            Tracked(&thread_lock_perm),
            Tracked(&pagetable_lock_perm),
        );
        assert(
            mmap_4k_range_mapped(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range,
                true,
                true,
            )
        ) by { pagetable_4k_insert_advances_range_prefix_forall(); };
        self.wunlock_mmap_4k_bundle_pages(
            pages,
            Tracked(&mut *lctx),
            Tracked(page_lock_perms),
        );

        assert(
            self.thread_map.perms_wf()
            && self.thread_map.spec_index(thread_ptr).is_init()
        ) by { reveal(thread_perms_wf); };
        assert(
            self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean()
            && lctx.page_lock_map().dom() =~= Set::<PageIndex>::empty()
            && lctx.lock_id_set() =~= old(lctx).lock_id_set()
            && lctx.lock_maps_equal(old(lctx))
        ) by {
            reveal(LocalContext::wf);
            match pages {
                Create4kEntryPages::DataOnly { .. } => {},
                Create4kEntryPages::L1AndData { .. } => {},
                Create4kEntryPages::L2L1AndData { .. } => {},
                Create4kEntryPages::L3L2L1AndData { .. } => {},
            }
        };
        let thread = self.thread_map.borrow(
            thread_ptr,
            Tracked(&thread_lock_perm),
        );
        let unused_credit = thread.quota_4k - original_thread_quota;
        self.refund_thread_4k_quota_to_process(
            process_ptr,
            thread_ptr,
            unused_credit,
            Tracked(&mut *lctx),
            Tracked(&process_lock_perm),
            Tracked(&thread_lock_perm),
        );
        assert(
            lctx.cpu_lock_map().spec_index(cpu_id)
                == self.cpu_array.lock_id_by_index(cpu_id)
            && lctx.container_lock_map().spec_index(container_ptr)
                == self.container_map.lock_id_by_key(container_ptr)
            && lctx.process_lock_map().spec_index(process_ptr)
                == self.process_map.lock_id_by_key(process_ptr)
            && lctx.thread_lock_map().spec_index(thread_ptr)
                == self.thread_map.lock_id_by_key(thread_ptr)
            && lctx.allocator_4k_lock_map().spec_index(
                AllocatorLockObjId::GlobalPool(alloc_ptr_4k),
            ) == self.allocator_4k_map.spec_index(alloc_ptr_4k)
                .global_pool.lock_id()
            && lctx.pagetable_lock_map().spec_index(pagetable_ptr)
                == self.pagetable_map.lock_id_by_key(pagetable_ptr)
        ) by {
            reveal(cpu_locked_match_lctx);
            reveal(container_locked_match_lctx);
            reveal(process_locked_match_lctx);
            reveal(thread_locked_match_lctx);
            reveal(allocator_4k_locked_match_lctx);
            reveal(pagetable_locked_match_lctx);
            reveal(pagetable_perms_wf);
        };
        self.wunlock_pagetable(
            pagetable_ptr,
            Tracked(&mut *lctx),
            Tracked(pagetable_lock_perm),
        );
        assert(Self::cache_perms_match_lctx(
            self.allocator_4k_map,
            alloc_ptr_4k,
            &*lctx,
            &cache_perms,
        )) by {
            reveal(KernelK::cache_perms_match_lctx);
            reveal(allocator_4k_locked_match_lctx);
        };
        self.wunlock_all_caches(
            alloc_ptr_4k,
            Tracked(&mut *lctx),
            Tracked(cache_perms),
        );
        self.wunlock_allocator_global_pool(
            alloc_ptr_4k,
            Tracked(&mut *lctx),
            Tracked(global_pool_lock_perm),
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
            assert(lctx.lock_id_set() =~= Set::<LockId>::empty()) by {
                broadcast use vstd::set::group_set_lemmas;
                assert_sets_equal!(
                    lctx.lock_id_set() == Set::<LockId>::empty(),
                    lock_id => {}
                );
            };
            steps.end_user_view_step(&*self, &mut *lctx);
            assert(mmap_4k_raw_range_mapped(
                self.pagetable_map.spec_index(pagetable_ptr).view(),
                range.start,
                range.len,
                true,
                true,
            )) by { mmap_4k_range_mapped_implies_raw(self.pagetable_map.spec_index(pagetable_ptr).view(), range, true, true); };
        }
    }
}

} // verus!
