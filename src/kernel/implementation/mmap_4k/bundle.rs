use vstd::prelude::*;
use crate::*;

use super::{Create4kEntryPages, mmap_4k_bundle_locks_match};

verus! {

impl KernelK {
    /// Resolve the current walk shape and stage exactly the pages needed for
    /// one fresh 4K mapping.  Earlier mappings in the same syscall may have
    /// installed shared directory pages, so this helper deliberately resolves
    /// the path again for every VA.
    pub(super) fn allocate_mmap_4k_bundle(
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
        Tracked(cache_perms): Tracked<&Map<CpuId, LockPerm>>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (
        Create4kEntryPages,
        usize,
        Tracked<Map<PagePtr, LockPerm>>,
    ))
        requires
            old(self).inv(),
            old(lctx).wf(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).user_view_locking_state() is Acquire,
            old(self).locked_objects_match_lctx(old(lctx)),
            lock_id_aligned(old(self), old(lctx)),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            cpu_id_valid(cpu_id),
            va_4k_valid(va),
            old(self).cpu_array.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).container_map.dom().contains(container_ptr),
            old(self).container_map.spec_index(container_ptr).wlocked_by(old(lctx)),
            old(self).process_map.dom().contains(process_ptr),
            old(self).process_map.spec_index(process_ptr).wlocked_by(old(lctx)),
            old(self).process_map.spec_index(process_ptr).being_killed() == false,
            old(self).process_map.spec_index(process_ptr).view_rodata().view()
                .owning_container == container_ptr,
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == process_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr,
            old(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == pagetable_ptr,
            thread_effective_quota_4k(
                old(self).thread_map.spec_index(thread_ptr),
            ) >= 4,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id()
                == old(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).container_map.spec_index(container_ptr).view_rodata().view()
                .allocator_ptr_4k == alloc_ptr_4k,
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
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id()
                == old(self).pagetable_map.spec_index(pagetable_ptr)
                    .locking_thread()->Write_lock_id,
            old(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_va2index(va).0 < 512,
            0 <= spec_va2index(va).1 < 512,
            0 <= spec_va2index(va).2 < 512,
            0 <= spec_va2index(va).3 < 512,
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_4k_entry_useable(
                    spec_va2index(va).0,
                    spec_va2index(va).1,
                    spec_va2index(va).2,
                    spec_va2index(va).3,
                ),
            old(lctx).page_lock_map().dom() =~= Set::<PageIndex>::empty(),
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
            final(lctx).container_lock_map() =~= old(lctx).container_lock_map(),
            final(lctx).process_lock_map() =~= old(lctx).process_lock_map(),
            final(lctx).thread_lock_map() =~= old(lctx).thread_lock_map(),
            final(lctx).endpoint_lock_map() =~= old(lctx).endpoint_lock_map(),
            final(lctx).scheduler_lock_map() =~= old(lctx).scheduler_lock_map(),
            final(lctx).pcid_allocator_lock_map()
                =~= old(lctx).pcid_allocator_lock_map(),
            final(lctx).pagetable_lock_map() =~= old(lctx).pagetable_lock_map(),
            final(lctx).iommu_table_lock_map() =~= old(lctx).iommu_table_lock_map(),
            final(lctx).cpu_lock_map() =~= old(lctx).cpu_lock_map(),
            final(lctx).allocator_4k_lock_map()
                =~= old(lctx).allocator_4k_lock_map(),
            final(lctx).allocator_2m_lock_map()
                =~= old(lctx).allocator_2m_lock_map(),
            final(lctx).allocator_1g_lock_map()
                =~= old(lctx).allocator_1g_lock_map(),
            final(lctx).page_lock_map() =~= match ret.0 {
                Create4kEntryPages::DataOnly { data_page } =>
                    old(lctx).page_lock_map().insert(
                        page_ptr2page_index(data_page),
                        final(self).page_array.lock_id_by_index(
                            page_ptr2page_index(data_page),
                        ),
                    ),
                Create4kEntryPages::L1AndData { l1_page, data_page } =>
                    old(lctx).page_lock_map().insert(
                        page_ptr2page_index(l1_page),
                        final(self).page_array.lock_id_by_index(
                            page_ptr2page_index(l1_page),
                        ),
                    ).insert(
                        page_ptr2page_index(data_page),
                        final(self).page_array.lock_id_by_index(
                            page_ptr2page_index(data_page),
                        ),
                    ),
                Create4kEntryPages::L2L1AndData {
                    l2_page, l1_page, data_page,
                } => old(lctx).page_lock_map().insert(
                    page_ptr2page_index(l2_page),
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(l2_page),
                    ),
                ).insert(
                    page_ptr2page_index(l1_page),
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(l1_page),
                    ),
                ).insert(
                    page_ptr2page_index(data_page),
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(data_page),
                    ),
                ),
                Create4kEntryPages::L3L2L1AndData {
                    l3_page, l2_page, l1_page, data_page,
                } => old(lctx).page_lock_map().insert(
                    page_ptr2page_index(l3_page),
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(l3_page),
                    ),
                ).insert(
                    page_ptr2page_index(l2_page),
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(l2_page),
                    ),
                ).insert(
                    page_ptr2page_index(l1_page),
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(l1_page),
                    ),
                ).insert(
                    page_ptr2page_index(data_page),
                    final(self).page_array.lock_id_by_index(
                        page_ptr2page_index(data_page),
                    ),
                ),
            },
            final(lctx).page_lock_map().dom() =~= match ret.0 {
                Create4kEntryPages::DataOnly { data_page } =>
                    old(lctx).page_lock_map().dom().insert(
                        page_ptr2page_index(data_page),
                    ),
                Create4kEntryPages::L1AndData { l1_page, data_page } =>
                    old(lctx).page_lock_map().dom()
                        .insert(page_ptr2page_index(l1_page))
                        .insert(page_ptr2page_index(data_page)),
                Create4kEntryPages::L2L1AndData {
                    l2_page, l1_page, data_page,
                } => old(lctx).page_lock_map().dom()
                    .insert(page_ptr2page_index(l2_page))
                    .insert(page_ptr2page_index(l1_page))
                    .insert(page_ptr2page_index(data_page)),
                Create4kEntryPages::L3L2L1AndData {
                    l3_page, l2_page, l1_page, data_page,
                } => old(lctx).page_lock_map().dom()
                    .insert(page_ptr2page_index(l3_page))
                    .insert(page_ptr2page_index(l2_page))
                    .insert(page_ptr2page_index(l1_page))
                    .insert(page_ptr2page_index(data_page)),
            },
            final(lctx).page_lock_map().dom() =~= ret.0.page_index_set(),
            final(lctx).lock_id_set() =~= match ret.0 {
                Create4kEntryPages::DataOnly { data_page } =>
                    old(lctx).lock_id_set().insert(
                        final(lctx).page_lock_map().spec_index(
                            page_ptr2page_index(data_page),
                        ),
                    ),
                Create4kEntryPages::L1AndData { l1_page, data_page } =>
                    old(lctx).lock_id_set().insert(
                        final(lctx).page_lock_map().spec_index(
                            page_ptr2page_index(l1_page),
                        ),
                    ).insert(
                        final(lctx).page_lock_map().spec_index(
                            page_ptr2page_index(data_page),
                        ),
                    ),
                Create4kEntryPages::L2L1AndData {
                    l2_page, l1_page, data_page,
                } => old(lctx).lock_id_set().insert(
                    final(lctx).page_lock_map().spec_index(
                        page_ptr2page_index(l2_page),
                    ),
                ).insert(
                    final(lctx).page_lock_map().spec_index(
                        page_ptr2page_index(l1_page),
                    ),
                ).insert(
                    final(lctx).page_lock_map().spec_index(
                        page_ptr2page_index(data_page),
                    ),
                ),
                Create4kEntryPages::L3L2L1AndData {
                    l3_page, l2_page, l1_page, data_page,
                } => old(lctx).lock_id_set().insert(
                    final(lctx).page_lock_map().spec_index(
                        page_ptr2page_index(l3_page),
                    ),
                ).insert(
                    final(lctx).page_lock_map().spec_index(
                        page_ptr2page_index(l2_page),
                    ),
                ).insert(
                    final(lctx).page_lock_map().spec_index(
                        page_ptr2page_index(l1_page),
                    ),
                ).insert(
                    final(lctx).page_lock_map().spec_index(
                        page_ptr2page_index(data_page),
                    ),
                ),
            },
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            ret.1 == ret.0.count(),
            1 <= ret.1 <= 4,
            ret.0.roles_distinct(),
            ret.2.view().dom() =~= match ret.0 {
                Create4kEntryPages::DataOnly { data_page } =>
                    Set::empty().insert(data_page),
                Create4kEntryPages::L1AndData { l1_page, data_page } =>
                    Set::empty().insert(l1_page).insert(data_page),
                Create4kEntryPages::L2L1AndData {
                    l2_page, l1_page, data_page,
                } => Set::empty().insert(l2_page).insert(l1_page)
                    .insert(data_page),
                Create4kEntryPages::L3L2L1AndData {
                    l3_page, l2_page, l1_page, data_page,
                } => Set::empty().insert(l3_page).insert(l2_page)
                    .insert(l1_page).insert(data_page),
            },
            ret.2.view().dom() =~= ret.0.page_set(),
            final(self).mmap_4k_staged_page_perms_match(
                thread_ptr,
                final(lctx),
                &ret.2.view(),
            ),
            final(self).create_4k_entry_pages_ready(
                ret.0,
                thread_ptr,
                final(lctx),
                &ret.2.view(),
            ),
            mmap_4k_bundle_locks_match(
                ret.0,
                final(lctx),
                &ret.2.view(),
            ),
            final(self).create_4k_entry_path_matches(
                ret.0,
                pagetable_ptr,
                va,
            ),
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                >= ret.1,
            final(self).thread_map.spec_index(thread_ptr).view().quota_4k
                == old(self).thread_map.spec_index(thread_ptr).view().quota_4k,
            final(self).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_4k.view()
                =~= old(self).thread_map.spec_index(thread_ptr).view()
                    .temp_alloc_cache_4k.view() + ret.2.view().dom(),
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean()
                ==> {
                    &&& final(self).thread_map.spec_index(thread_ptr).view()
                        .temp_alloc_cache_4k.view() =~= ret.0.page_set()
                    &&& final(self).thread_map.spec_index(thread_ptr).view()
                        .temp_alloc_cache_2m.view().len() == 0
                    &&& final(self).thread_map.spec_index(thread_ptr).view()
                        .temp_alloc_cache_1g.view().len() == 0
                },
            final(self).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_2m.view()
                =~= old(self).thread_map.spec_index(thread_ptr).view()
                    .temp_alloc_cache_2m.view(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .temp_alloc_cache_1g.view()
                =~= old(self).thread_map.spec_index(thread_ptr).view()
                    .temp_alloc_cache_1g.view(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_fields_equal(
                    &old(self).thread_map.spec_index(thread_ptr).view(),
                ),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(self).cpu_array.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(self).cpu_array.spec_index(cpu_id).view()
                == old(self).cpu_array.spec_index(cpu_id).view(),
            final(self).container_map.dom().contains(container_ptr),
            final(self).container_map.spec_index(container_ptr).wlocked_by(final(lctx)),
            final(self).container_map.spec_index(container_ptr)
                == old(self).container_map.spec_index(container_ptr),
            final(self).container_map.spec_index(container_ptr).view_rodata().view()
                .allocator_ptr_4k == alloc_ptr_4k,
            final(self).process_map.dom().contains(process_ptr),
            final(self).process_map.spec_index(process_ptr).wlocked_by(final(lctx)),
            final(self).process_map.spec_index(process_ptr).being_killed() == false,
            final(self).process_map.spec_index(process_ptr)
                == old(self).process_map.spec_index(process_ptr),
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(self).thread_map.spec_index(thread_ptr).being_killed() == false,
            final(self).thread_map.spec_index(thread_ptr).view().owning_proc
                == process_ptr,
            final(self).thread_map.spec_index(thread_ptr).view().owning_container
                == container_ptr,
            final(self).thread_map.spec_index(thread_ptr).view().proc_pagetable_ptr
                == pagetable_ptr,
            thread_lock_perm.lock_id()
                == final(self).thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
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
            final(self).pagetable_map.dom().contains(pagetable_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr).wlocked_by(final(lctx)),
            final(self).pagetable_map.spec_index(pagetable_ptr)
                == old(self).pagetable_map.spec_index(pagetable_ptr),
            pagetable_lock_perm.lock_id()
                == final(self).pagetable_map.spec_index(pagetable_ptr)
                    .locking_thread()->Write_lock_id,
            forall|held_lock_id: LockId|
                #![trigger final(lctx).lock_id_set().contains(held_lock_id)]
                final(lctx).lock_id_set().contains(held_lock_id)
                ==> held_lock_id.major < FREE_PAGE_LOCK_MAJOR,
    {
        proof {
            assert(
                self.pagetable_map.perms_wf()
                && self.pagetable_map.spec_index(pagetable_ptr).inv()
                && self.pagetable_map.spec_index(pagetable_ptr).view().wf()
                && !self.pagetable_map.spec_index(pagetable_ptr).view()
                    .mapping_4k().dom().contains(va)
            ) by {
                reveal(pagetable_perms_wf);
                broadcast use PageTable::reveal_page_table_wf;
                broadcast use PageTable::reveal_page_table_mappings_wf;
                va_lemma();
            };
        }
        let indices = va2index(va);
        let pagetable = self.pagetable_map.borrow(
            pagetable_ptr,
            Tracked(pagetable_lock_perm),
        );
        let (_, error_code, _) = pagetable.resolve_mapping_4k_l1(
            indices.0,
            indices.1,
            indices.2,
            indices.3,
        );

        let tracked mut page_lock_perms: Map<PagePtr, LockPerm> =
            Map::tracked_empty();
        proof {
            assert(self.mmap_4k_staged_page_perms_match(
                thread_ptr,
                &*lctx,
                &page_lock_perms,
            )) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
        }

        match error_code {
            PageTableErrorCode::L4EntryNotExist => {
                let (l3_page, Tracked(l3_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                proof {
                    page_lock_perms.tracked_insert(l3_page, l3_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~=
                            Set::empty().insert(l3_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                let (l2_page, Tracked(l2_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                proof {
                    page_lock_perms.tracked_insert(l2_page, l2_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~=
                            Set::empty().insert(l3_page).insert(l2_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                let (l1_page, Tracked(l1_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                proof {
                    page_lock_perms.tracked_insert(l1_page, l1_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~= Set::empty()
                            .insert(l3_page).insert(l2_page).insert(l1_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                let (data_page, Tracked(data_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                let pages = Create4kEntryPages::L3L2L1AndData {
                    l3_page, l2_page, l1_page, data_page,
                };
                proof {
                    assert(pages.roles_distinct()) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                    page_lock_perms.tracked_insert(data_page, data_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~= Set::empty()
                            .insert(l3_page).insert(l2_page).insert(l1_page)
                            .insert(data_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                    assert(self.create_4k_entry_pages_ready(
                        pages, thread_ptr, &*lctx, &page_lock_perms,
                    )) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                (pages, 4, Tracked(page_lock_perms))
            },
            PageTableErrorCode::L3EntryNotExist => {
                let (l2_page, Tracked(l2_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                proof {
                    page_lock_perms.tracked_insert(l2_page, l2_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~=
                            Set::empty().insert(l2_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                let (l1_page, Tracked(l1_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                proof {
                    page_lock_perms.tracked_insert(l1_page, l1_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~=
                            Set::empty().insert(l2_page).insert(l1_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                let (data_page, Tracked(data_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                let pages = Create4kEntryPages::L2L1AndData {
                    l2_page, l1_page, data_page,
                };
                proof {
                    assert(pages.roles_distinct()) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                    page_lock_perms.tracked_insert(data_page, data_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~= Set::empty()
                            .insert(l2_page).insert(l1_page).insert(data_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                    assert(self.create_4k_entry_pages_ready(
                        pages, thread_ptr, &*lctx, &page_lock_perms,
                    )) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                (pages, 3, Tracked(page_lock_perms))
            },
            PageTableErrorCode::L2EntryNotExist => {
                let (l1_page, Tracked(l1_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                proof {
                    page_lock_perms.tracked_insert(l1_page, l1_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~=
                            Set::empty().insert(l1_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                let (data_page, Tracked(data_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                let pages = Create4kEntryPages::L1AndData {
                    l1_page, data_page,
                };
                proof {
                    assert(pages.roles_distinct()) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                    page_lock_perms.tracked_insert(data_page, data_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~= Set::empty()
                            .insert(l1_page).insert(data_page)
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                    assert(self.create_4k_entry_pages_ready(
                        pages, thread_ptr, &*lctx, &page_lock_perms,
                    )) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                (pages, 2, Tracked(page_lock_perms))
            },
            PageTableErrorCode::L1EntryNotExist => {
                let (data_page, Tracked(data_perm)) = self.stage_mmap_4k_page(
                    alloc_ptr_4k, thread_ptr, process_ptr, container_ptr,
                    cpu_id, pagetable_ptr, Tracked(&mut *lctx),
                    Tracked(&mut *steps), Tracked(cache_perms),
                    Tracked(global_pool_lock_perm), Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm), Tracked(&page_lock_perms),
                );
                let pages = Create4kEntryPages::DataOnly { data_page };
                proof {
                    page_lock_perms.tracked_insert(data_page, data_perm);
                    assert(
                        self.mmap_4k_staged_page_perms_match(
                            thread_ptr, &*lctx, &page_lock_perms,
                        )
                        && page_lock_perms.dom() =~=
                            Set::empty().insert(data_page)
                        && self.create_4k_entry_pages_ready(
                            pages, thread_ptr, &*lctx, &page_lock_perms,
                        )
                    ) by { reveal(KernelK::mmap_4k_staged_page_perms_match); };
                }
                (pages, 1, Tracked(page_lock_perms))
            },
            PageTableErrorCode::NoError
            | PageTableErrorCode::EntryTakenBy4k
            | PageTableErrorCode::EntryTakenBy2m
            | PageTableErrorCode::EntryTakenBy1g => {
                (
                    Create4kEntryPages::DataOnly { data_page: 0 },
                    0,
                    Tracked(page_lock_perms),
                )
            },
        }
    }
}

} // verus!
