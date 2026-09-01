use vstd::prelude::*;
use crate::*;
use super::mmap_4k_context::{
    mmap_4k_held_context,
    mmap_4k_allocation_ready,
};
use super::mmap_4k_create_entry_install::{
    install_staged_4k_page_table_page,
    MissingPageTableLevel,
};
use super::mmap_4k_stage_page::stage_mmap_4k_page;

verus! {

    /// Allocate and install one missing directory page, then end the krnl
    /// section.  Directory topology is absent from `PageTableU`, so this
    /// boundary is a stuttering user step.
    pub(super) fn install_one_mmap_4k_directory_page(
        krnl: &mut KernelK,
        level: MissingPageTableLevel,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        indices: (L4Index, L3Index, L2Index),
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
        requires
            mmap_4k_held_context(old(krnl), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            match level {
                MissingPageTableLevel::L4 =>
                    old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is Some
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
            mmap_4k_allocation_ready(old(krnl), old(lctx)),
        ensures
            mmap_4k_held_context(final(krnl), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            mmap_4k_allocation_ready(final(krnl), final(lctx)),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR) ==> final(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR),
            final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)]
                #![trigger final(krnl).thr_mp.spec_index(t)]
                (old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(final(lctx).thread_id())),
            forall|t: RwLockThreadPtr|
                #![trigger old(krnl).thr_mp.spec_index(t)]
                #![trigger final(krnl).thr_mp.spec_index(t)]
                t != thread_ptr
                    && old(krnl).thr_mp.dom().contains(t)
                    && old(krnl).thr_mp.spec_index(t)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).thr_mp.dom().contains(t)
                    && final(krnl).thr_mp.spec_index(t)
                        == old(krnl).thr_mp.spec_index(t)
                    && final(krnl).thr_mp.lock_id_by_key(t)
                        == old(krnl).thr_mp.lock_id_by_key(t),
            forall|p: RwLockPageTableRoot|
                #![trigger old(krnl).pt_mp.spec_index(p)]
                #![trigger final(krnl).pt_mp.spec_index(p)]
                (old(krnl).pt_mp.dom().contains(p)
                    && old(krnl).pt_mp.spec_index(p)
                        .locked_by_thread(old(lctx).thread_id()))
                == (final(krnl).pt_mp.dom().contains(p)
                    && final(krnl).pt_mp.spec_index(p)
                        .locked_by_thread(final(lctx).thread_id())),
            forall|p: RwLockPageTableRoot|
                #![trigger old(krnl).pt_mp.spec_index(p)]
                #![trigger final(krnl).pt_mp.spec_index(p)]
                p != pagetable_ptr
                    && old(krnl).pt_mp.dom().contains(p)
                    && old(krnl).pt_mp.spec_index(p)
                        .locked_by_thread(old(lctx).thread_id())
                ==> final(krnl).pt_mp.dom().contains(p)
                    && final(krnl).pt_mp.spec_index(p)
                        == old(krnl).pt_mp.spec_index(p)
                    && final(krnl).pt_mp.lock_id_by_key(p)
                        == old(krnl).pt_mp.lock_id_by_key(p),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq,
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
            allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
            final(krnl).pt_mp.spec_index(pagetable_ptr).inv(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().user_view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().user_view(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() =~= old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l4(indices.0) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 =>
                    final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
    {
        let (page_ptr, Tracked(page_lock_perm)) = stage_mmap_4k_page(krnl, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr));
        install_staged_4k_page_table_page(krnl, level, page_ptr, thread_ptr, pagetable_ptr, indices, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        let ghost installed_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr));
        proof {
            assert(page_objects_unlocked_except(krnl.pg_arr, lctx.thread_id(), set![page_ptr2page_index(page_ptr)])) by { reveal(page_objects_unlocked_except); };
        }
        krnl.wunlock_page(page_ptr2page_index(page_ptr), Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedHeldLock {
                    lock_id: staged_page_lock_id, mode: TypedLockMode::Write,
                }, TypedHeldLock {
                    lock_id: installed_page_lock_id, mode: TypedLockMode::Write,
                });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedHeldLock {
                    lock_id: installed_page_lock_id, mode: TypedLockMode::Write,
                });
            };
            assert(lctx.lock_id_set() =~= old(lctx).lock_id_set()) by {
                assert(!old(lctx).lock_id_set().contains((staged_page_lock_id, KernelObjId::Page(page_ptr2page_index(page_ptr))))) by { reveal(lock_id_set_aligned); reveal(mmap_4k_allocation_ready); };
                assert(!old(lctx).lock_id_set().contains((installed_page_lock_id, KernelObjId::Page(page_ptr2page_index(page_ptr))))) by { reveal(lock_id_set_aligned); reveal(mmap_4k_allocation_ready); };
                set_insert_remove_absent_lemma(old(lctx).lock_id_set(), (staged_page_lock_id, KernelObjId::Page(page_ptr2page_index(page_ptr))));
                set_insert_remove_absent_lemma(old(lctx).lock_id_set(), (installed_page_lock_id, KernelObjId::Page(page_ptr2page_index(page_ptr))));
            };
            assert(old(lctx).held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR) ==> lctx.held_lock_majors_lt(MAPPED_PAGE_LOCK_MAJOR)) by { reveal(LocalContext::held_lock_majors_lt); };
            assert(mmap_4k_allocation_ready(krnl, &*lctx)) by { reveal(LocalContext::holds_no_allocator_locks); assert(PAGE_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR && IOMMU_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR && ALLOCATED_PAGE_MAJOR < ALLOCATOR_CACHE_MAJOR) by (compute); };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(mmap_4k_allocation_ready(krnl, &*lctx)) by { reveal(LocalContext::holds_no_allocator_locks); assert(PAGE_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR && IOMMU_TABLE_LOCK_MAJOR < ALLOCATOR_CACHE_MAJOR && ALLOCATED_PAGE_MAJOR < ALLOCATOR_CACHE_MAJOR) by (compute); };
            assert({
                &&& krnl.pt_mp.spec_index(pagetable_ptr).inv()
                &&& krnl.pt_mp.spec_index(pagetable_ptr).view().wf()
            }) by { reveal(pagetable_perms_wf); };
            assert(mmap_4k_held_context(krnl, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm)) by { reveal(cpu_array_wf); reveal(container_thread_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(process_thread_wf); reveal(thread_perms_wf); reveal(pagetable_perms_wf); };
        }
    }

} // verus!
