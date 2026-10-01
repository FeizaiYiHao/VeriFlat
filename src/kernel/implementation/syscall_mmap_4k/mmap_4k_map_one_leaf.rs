use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_owned::map_owned_4k_page;
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::mmap_4k_leaf_step_from_u;

verus! {
    /// Allocate and publish one 4K leaf after its directory walk is prepared.
    /// The physical leaf is published with both present bits set, then the
    /// completed user-visible mapping is recorded as exactly one krnl step.
    pub(super) fn map_one_mmap_4k_page(krnl: &mut KernelK, alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>)
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).prc_mp.dom().contains(process_ptr),
            !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            old(steps).snapshot_k() == *old(krnl),
            old(lctx).page_lock_map().dom().is_empty(),
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
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
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped < old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range.len,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range.view()[old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped as int] == va,
        ensures
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            final(krnl).prc_mp.dom().contains(process_ptr),
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            final(krnl).thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
            final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == false,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
            thread_lock_perm.thread_id() == final(lctx).thread_id(),
            thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            final(lctx).page_lock_map().dom().is_empty(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_leaf(old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()),
            final(steps).view() == old(steps).view().push(final(steps).view().last()),
            mmap_4k_leaf_step_pre(final(steps).view().last().old_u, cpu_id),
            mmap_4k_leaf_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
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
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
        let page_index = page_ptr2page_index(page_ptr);
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        let ghost section_start = *krnl;
        proof { assert(krnl.prc_mp.dom().contains(process_ptr) && !krnl.prc_mp.spec_index(process_ptr).view().zombie && krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr && krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by { reveal(process_cpu_wf); reveal(process_pagetable_match); }; }
        map_owned_4k_page(krnl, page_ptr, thread_ptr, pagetable_ptr, va, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            };
            assert(kernel_process_4k_mapping_changed(&steps.snapshot_k(), &*krnl, process_ptr, pagetable_ptr, va)) by {
                reveal(kernel_process_4k_mapping_changed);
                reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                reveal(kernel_pagetable_nonlock_fields_unchanged); reveal(kernel_process_nonlock_fields_unchanged);
                reveal(process_pagetable_match);
            };
            assert({
                &&& krnl.prc_mp.dom().contains(process_ptr)
                &&& !krnl.prc_mp.spec_index(process_ptr).view().zombie
                &&& krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr
            }) by { reveal(process_cpu_wf); reveal(process_pagetable_match); };
            assert(mmap_4k_leaf_step_pre(kernel_k_to_kernel_u(section_start), cpu_id)
                && mmap_4k_leaf_step(kernel_k_to_kernel_u(section_start), kernel_k_to_kernel_u(*krnl), cpu_id)) by {
                kernel_thread_quota_4k_progress_and_4k_mapping_added_implies_u_step(&section_start, &*krnl, &*lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr, va);
                mmap_4k_leaf_step_from_u(kernel_k_to_kernel_u(section_start), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, va);
            };
            krnl.kernel_step_boundary_process_4k_mapping_changed(
                &mut *lctx, &mut *steps, process_ptr, pagetable_ptr, va, process_ptr, pagetable_ptr, thread_ptr,
            );
            assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.prc_mp.dom().contains(process_ptr)) by { reveal(container_thread_wf); reveal(process_thread_wf); };
            assert(krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view()) by { set_insert_remove_absent_lemma(old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k.view(), page_ptr); };
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { reveal(container_allocator_wf); };
            assert(krnl.pt_mp.spec_index(pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
        }
    }
} // verus!
