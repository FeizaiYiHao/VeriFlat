use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_owned::map_owned_4k_page;
use super::syscall_mmap_4k_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_4k_trace::mmap_4k_leaf_step_from_u;

verus! {
    /// Allocate and publish one 4K leaf after its directory walk is prepared.
    /// The physical leaf is published with both present bits set, then the
    /// completed user-visible mapping is recorded as exactly one krnl step.
    pub(super) fn map_one_mmap_4k_page(
        krnl: &mut KernelK, alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
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
            !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
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
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
            va_4k_valid(va),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_va2index(va).0,
            pei_valid(spec_va2index(va).0),
            pei_valid(spec_va2index(va).1),
            pei_valid(spec_va2index(va).2),
            pei_valid(spec_va2index(va).3),
            old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(thread_ptr)) >= 1,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va) == false,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2) is Some,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() is Some,
            !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped < old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range.len,
            old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range.view()[old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped as int] == va,
        ensures
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt))]
                old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pt))
                    ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pt)),
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
            !thread_is_dangling(final(krnl).thr_mp.spec_index(thread_ptr)),
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
            final(steps).snapshot_k() == *final(krnl),
            final(lctx).page_lock_map().dom().is_empty(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_leaf(old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()),
            !final(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
            final(steps).view() == old(steps).view().push(final(steps).view().last()),
            mmap_4k_leaf_step_pre(final(steps).view().last().old_u, cpu_id),
            mmap_4k_leaf_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k()
                == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().insert(va, pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va)),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).present,
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).write,
            !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).execute_disable,
    {
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
        let page_index = page_ptr2page_index(page_ptr);
        let indices = va2index(va);
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
        let ghost section_start = *krnl;
        let ghost window_va = spec_index2va((indices.0, indices.1, indices.2, 0usize));
        proof {
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr)) by {
                old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
                pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            };
            let (l4i, l3i, l2i) = (indices.0, indices.1, indices.2);
            assert(KERNEL_MEM_END_L4INDEX <= l4i && spec_index2va(indices) == va) by { spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3); };
            assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
        }
        let Tracked(window_lock_perm) = krnl.lock_pagetable_window(pagetable_ptr, indices.0, indices.1, indices.2, Tracked(pagetable_lock_perm), Tracked(&mut *lctx));
        proof {
            assert(pagetable_tlb_entries_present(section_start.cpu_tlb, section_start.cpu_arr, section_start.pcid_needflush, pagetable_ptr, pagetable_c(section_start.pt_mp, section_start.pt_lower.view(), pagetable_ptr))
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable_ptr, pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr)));
        }
        map_owned_4k_page(krnl, page_ptr, thread_ptr, pagetable_ptr, va, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
        let ghost window_held_k = *krnl;
        krnl.unlock_pagetable_window(pagetable_ptr, indices.0, indices.1, indices.2, Tracked(pagetable_lock_perm), Tracked(&mut *lctx), Tracked(window_lock_perm));
        proof {
            assert(pagetable_tlb_entries_present(window_held_k.cpu_tlb, window_held_k.cpu_arr, window_held_k.pcid_needflush, pagetable_ptr, pagetable_c(window_held_k.pt_mp, window_held_k.pt_lower.view(), pagetable_ptr))
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable_ptr, pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr)));
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_va), TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, window_va), mode: TypedLockMode::Write });
            };
            assert(krnl.pt_lower.view() =~= section_start.pt_lower.view().insert(pagetable_ptr, krnl.pt_lower.view().spec_index(pagetable_ptr)));
            assert(kernel_process_4k_mapping_changed(&steps.snapshot_k(), &*krnl, process_ptr, pagetable_ptr, va)) by {
                process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); reveal(kernel_process_4k_mapping_changed); reveal(process_pagetable_match);
            };
            assert({
                &&& krnl.prc_mp.dom().contains(process_ptr)
                &&& !krnl.prc_mp.spec_index(process_ptr).view().zombie
                &&& krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
                &&& krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr
            }) by {
                process_cpu_wf_at(old(krnl).prc_mp, old(krnl).cpu_arr, cpu_id); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id);
                process_pagetable_match_process_at(old(krnl).prc_mp, old(krnl).pt_mp, process_ptr); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr);
            };
            let leaf_k = *krnl;
            let leaf_lctx = *lctx;
            krnl.kernel_step_boundary_process_4k_mapping_changed(&mut *lctx, &mut *steps, process_ptr, pagetable_ptr, va, process_ptr, pagetable_ptr, thread_ptr, thread_ptr);
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr) == pagetable_c(leaf_k.pt_mp, leaf_k.pt_lower.view(), pagetable_ptr)) by { assert(leaf_lctx.pagetable_lock_map().dom().contains(pagetable_ptr)); };
            assert(mmap_4k_leaf_step_pre(steps.view().last().old_u, cpu_id) && mmap_4k_leaf_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id)) by {
                kernel_thread_quota_4k_progress_and_4k_mapping_added_implies_u_step(&section_start, &leaf_k, &leaf_lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr, va);
                mmap_4k_leaf_step_from_u(kernel_k_to_kernel_u(section_start), kernel_k_to_kernel_u(leaf_k), cpu_id, process_ptr, thread_ptr, va);
            };
            assert(krnl.ctn_mp.dom().contains(container_ptr) && krnl.prc_mp.dom().contains(process_ptr)) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); };
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()) by { pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); };
        }
    }
} // verus!
