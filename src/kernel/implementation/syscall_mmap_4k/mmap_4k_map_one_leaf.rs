use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_owned::map_owned_4k_page;
use super::syscall_mmap_4k_spec::mmap_4k_lock_scope;

verus! {

    /// Allocate and publish one 4K leaf after its directory walk is prepared.
    /// The physical leaf is published with both present bits set, then the
    /// completed user-visible mapping is recorded as exactly one krnl step.
    pub(super) fn map_one_mmap_4k_page(
        krnl: &mut KernelK,
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
            mmap_4k_held_context(old(krnl), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            mmap_4k_allocation_ready(old(krnl), old(lctx)),
            old(krnl).ctn_mp.spec_index(container_ptr).locked_by_thread(old(lctx).thread_id()),
            old(krnl).prc_mp.spec_index(process_ptr).locked_by_thread(old(lctx).thread_id()),
            va_4k_valid(va),
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= spec_va2index(va).0,
            pei_valid(spec_va2index(va).0),
            pei_valid(spec_va2index(va).1),
            pei_valid(spec_va2index(va).2),
            pei_valid(spec_va2index(va).3),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va) == false,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) is Some,
        ensures
            mmap_4k_held_context(final(krnl), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm),
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            mmap_4k_allocation_ready(final(krnl), final(lctx)),
            mmap_4k_lock_scope(old(krnl), old(lctx), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable_ptr) ==> mmap_4k_lock_scope(final(krnl), final(lctx), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable_ptr),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 1,
            final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr),
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            thread_objects_unlocked_except(old(krnl).thr_mp, old(lctx).thread_id(), set![thread_ptr]) ==> thread_objects_unlocked_except(final(krnl).thr_mp, final(lctx).thread_id(), set![thread_ptr]),
            pagetable_objects_unlocked_except(old(krnl).pt_mp, old(lctx).thread_id(), set![pagetable_ptr]) ==> pagetable_objects_unlocked_except(final(krnl).pt_mp, final(lctx).thread_id(), set![pagetable_ptr]),
            allocator_objects_unlocked(old(krnl).allc_2m_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_2m_mp, final(lctx).thread_id()),
            allocator_objects_unlocked(old(krnl).allc_1g_mp, old(lctx).thread_id()) ==> allocator_objects_unlocked(final(krnl).allc_1g_mp, final(lctx).thread_id()),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().insert(va, final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va)),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(krnl).pt_mp.spec_index(pagetable_ptr)
                    .view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i)
                ==> final(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i)
                    == old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        .spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va).present,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va).write,
            !final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va).execute_disable,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3) is Some,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3)->0.perm.present,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3)->0.perm.kernel_present,
    {
        let (page_ptr, Tracked(page_lock_perm)) = stage_mmap_4k_page(krnl, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        let page_index = page_ptr2page_index(page_ptr);
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        map_owned_4k_page(krnl, page_ptr, thread_ptr, pagetable_ptr, va, true, false, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                reveal(typed_lock_maps_inserted); reveal(typed_lock_maps_removed); reveal(mmap_4k_allocation_ready);
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            };
            assert(mmap_4k_allocation_ready(krnl, lctx)) by { reveal(mmap_4k_allocation_ready); reveal(LocalContext::holds_no_allocator_locks); };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(krnl.pt_mp.spec_index(pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
            assert(mmap_4k_held_context(krnl, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, thread_lock_perm, pagetable_lock_perm)) by { reveal(cpu_array_wf); reveal(container_thread_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(process_thread_wf); reveal(thread_perms_wf); reveal(pagetable_perms_wf); };
            if mmap_4k_lock_scope(old(krnl), old(lctx), cpu_id, container_ptr, process_ptr, thread_ptr, pagetable_ptr) {
            }
        }
    }

} // verus!
