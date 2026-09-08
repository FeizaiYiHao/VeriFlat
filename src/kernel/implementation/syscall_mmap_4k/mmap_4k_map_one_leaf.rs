use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_owned::map_owned_4k_page;

verus! {
    /// Allocate and publish one 4K leaf after its directory walk is prepared.
    /// The physical leaf is published with both present bits set, then the
    /// completed user-visible mapping is recorded as exactly one krnl step.
    pub(super) fn map_one_mmap_4k_page(krnl: &mut KernelK, alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>)
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            lock_id_set_aligned(old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            old(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(old(lctx)),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            ((old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr && old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || old(krnl).prc_mp.spec_index(process_ptr).wlocked_by(old(lctx))),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            old(krnl).pt_mp.spec_index(pagetable_ptr).wlocked_by(old(lctx)),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
            mmap_4k_allocation_ready(old(lctx)),
            old(lctx).container_lock_map().dom().contains(container_ptr),
            old(lctx).process_lock_map().dom().contains(process_ptr),
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
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            lock_id_set_aligned(final(lctx)),
            final(krnl).cpu_arr.spec_index(cpu_id).view().wlocked_by(final(lctx)),
            final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            final(krnl).prc_mp.dom().contains(process_ptr),
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            final(krnl).thr_mp.dom().contains(thread_ptr),
            final(krnl).thr_mp.spec_index(thread_ptr).wlocked_by(final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            ((final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr && final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || final(krnl).prc_mp.spec_index(process_ptr).wlocked_by(final(lctx))),
            thread_lock_perm.thread_id() == final(lctx).thread_id(),
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            final(krnl).pt_mp.spec_index(pagetable_ptr).wlocked_by(final(lctx)),
            pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(steps).steps.len() == old(steps).steps.len() + 1,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
            mmap_4k_allocation_ready(final(lctx)),
            old(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![process_ptr], set![thread_ptr], Set::empty(), Set::empty(), Set::empty(), set![pagetable_ptr], Set::empty()) ==> final(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![process_ptr], set![thread_ptr], Set::empty(), Set::empty(), Set::empty(), set![pagetable_ptr], Set::empty()),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
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
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().insert(va, final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va)),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i)]
                final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= l4i && pei_valid(l4i)
                    && pei_valid(l3i)
                    && pei_valid(l2i) ==> final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i) == old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(l4i, l3i, l2i),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().dom().contains(va),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va).present,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va).write,
            !final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k().spec_index(va).execute_disable,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3) is Some,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3)->0.perm.present,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_4k_l1(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, spec_va2index(va).3)->0.perm.kernel_present,
    {
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
        let page_index = page_ptr2page_index(page_ptr);
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        proof {
            assert(old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)) by { reveal(LockedMap::typed_lock_map_aligned); };
        }
        map_owned_4k_page(krnl, page_ptr, thread_ptr, pagetable_ptr, va, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            };
            assert({
                &&& old(lctx).cpu_lock_map().dom().contains(cpu_id)
                &&& lctx.thread_lock_map().dom().contains(thread_ptr)
                &&& lctx.pagetable_lock_map().dom().contains(pagetable_ptr)
            }) by {
                reveal(LockedArray::typed_lock_map_aligned);
                reveal(LockedMap::typed_lock_map_aligned);
            };
            assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()) by { set_insert_remove_absent_lemma(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), page_ptr); };
            krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { reveal(container_allocator_wf); };
            assert(mmap_4k_allocation_ready(lctx)) by { reveal(LocalContext::holds_no_allocator_locks); };
            assert(krnl.pt_mp.spec_index(pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
            if old(lctx).object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![process_ptr], set![thread_ptr], Set::empty(), Set::empty(), Set::empty(), set![pagetable_ptr], Set::empty()) {
                assert(lctx.object_lock_scope(Set::empty(), set![cpu_id], set![container_ptr], set![process_ptr], set![thread_ptr], Set::empty(), Set::empty(), Set::empty(), set![pagetable_ptr], Set::empty())) by {
                    reveal(typed_lock_maps_unchanged);
                    reveal(LocalContext::object_lock_scope);
                };
            }
        }
    }

} // verus!
