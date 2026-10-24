use vstd::prelude::*;
use crate::*;
use super::mmap_4k_map_owned::map_owned_4k_page;
use super::syscall_mmap_4k_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_4k_trace::{mmap_4k_leaf_step_from_u, mmap_4k_range_steps_from_directory, mmap_4k_range_steps_from_leaf};

verus! {
/// Map `va`, page `mapped` of `range`, under the pagetable's big read lock and the held 2M window of `va`: install the
/// window's L1 table when it is missing, then allocate a page and publish its present, writable, executable leaf. The L1
/// table, if installed, is one directory step and the leaf is one leaf step; inside the held windows only `va` changes.
pub(super) fn map_one_mmap_4k_page(
    krnl: &mut KernelK, alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId,
    pagetable_ptr: RwLockPageTableRoot, va: VAddr, Ghost(range): Ghost<VaRange4K>, Ghost(mapped): Ghost<usize>, Ghost(phase): Ghost<Mmap4kPhase>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 2,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range, mapped, directory: Mmap4kDirectory::None, phase }),
        !(phase is Fill),
        mapped < range.len,
        range.view()[mapped as int] == va,
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(steps).snapshot_k() == *old(krnl),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        va_4k_valid(va),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va))),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(window_of(va).va),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va),
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + 1 <= final(steps).view().len() <= old(steps).view().len() + 2,
        final(steps).nonlock_view().len() - old(steps).nonlock_view().len() == final(steps).view().len() - old(steps).view().len(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_4k_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).ctn_mp.dom().contains(container_ptr),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        final(krnl).prc_mp.dom().contains(process_ptr),
        !final(krnl).prc_mp.spec_index(process_ptr).view().zombie,
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        final(krnl).thr_mp.dom().contains(thread_ptr),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !thread_is_dangling(final(krnl).thr_mp.spec_index(thread_ptr)),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k - 2 <= final(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k < old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k,
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range, mapped: (mapped + 1) as usize, directory: Mmap4kDirectory::None, phase }),
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
            let pre = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let post = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.window_view(w).lock_state == pre.window_view(w).lock_state
            &&& post.window_view(w).stale_cpus == pre.window_view(w).stale_cpus
            &&& post.mapping_2m().dom().contains(w.va) == pre.mapping_2m().dom().contains(w.va)
            &&& pre.mapping_2m().dom().contains(w.va) ==> post.mapping_2m().spec_index(w.va) == pre.mapping_2m().spec_index(w.va)
            &&& pre.window_leaves_present(w) ==> post.window_leaves_present(w)
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va)
                && spec_v2l2index(v) == spec_v2l2index(w.va) && v != va ==> {
                let pre = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
                let post = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
                &&& post.mapping_4k().dom().contains(v) == pre.mapping_4k().dom().contains(v)
                &&& pre.mapping_4k().dom().contains(v) ==> post.mapping_4k().spec_index(v) == pre.mapping_4k().spec_index(v)
            },
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).present,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).write,
        !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(va).execute_disable,
{
    let indices = va2index(va);
    let ghost entry_steps = steps.view();
    let ghost window = window_of(va);
    proof {
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3);
        spec_index2va_2m_valid(indices.0, indices.1, indices.2);
        spec_va_4k_index_roundtrip_at(window.va, indices.0, indices.1, indices.2, 0usize);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf_mapping_2m_at(indices.0, indices.1, indices.2);
    }
    let l2_present = {
        let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
        let l4_entry = pagetable.get_entry_l4(indices.0).unwrap();
        let l3_entry = pagetable.get_entry_l3(indices.0, indices.1, &l4_entry).unwrap();
        pagetable.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3_entry).is_some()
    };
    if !l2_present {
        let _ = install_one_mmap_4k_directory_page(
            krnl, MissingPageTableLevel::L2, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (indices.0, indices.1, indices.2), indices.2, indices.2, false, None,
            Ghost(thread_ptr), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(None), Tracked(None),
        );
        proof { mmap_4k_range_steps_from_directory(&*steps, entry_steps, entry_steps.len() as int, cpu_id); }
    }
    let ghost leaf_steps = steps.view();
    let ghost installed = *krnl;
    let ghost installed_lctx = *lctx;
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thread_ptr, container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
    let page_index = page_ptr2page_index(page_ptr);
    let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    let ghost section_start = *krnl;
    proof {
        pagetable_window_typed_lock_map_aligned_at(krnl.pt_mp, krnl.pt_lower.view(), lctx.pagetable_window_lock_map(), lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr, window);
    }
    map_owned_4k_page(krnl, page_ptr, thread_ptr, pagetable_ptr, va, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_lock_perm));
    proof {
        let leaf_k = *krnl;
        let leaf_lctx = *lctx;
        assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
            map_insert_overwrite_lemma(installed_lctx.page_lock_map(), page_index, TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write }, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
            map_insert_remove_absent_lemma(installed_lctx.page_lock_map(), page_index, TypedHeldLock { lock_id: krnl.pg_arr.lock_id_by_index(page_index), mode: TypedLockMode::Write });
        };
        assert(kernel_process_4k_mapping_changed(&steps.snapshot_k(), &*krnl, process_ptr, pagetable_ptr, va)) by {
            process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); reveal(kernel_process_4k_mapping_changed); reveal(process_pagetable_match);
        };
        process_thread_wf_at(section_start.prc_mp, section_start.thr_mp, thread_ptr); process_pagetable_match_process_at(section_start.prc_mp, section_start.pt_mp, process_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr);
        krnl.kernel_step_boundary_process_4k_mapping_changed_windowed(&mut *lctx, &mut *steps, process_ptr, pagetable_ptr, va, process_ptr, pagetable_ptr, thread_ptr, thread_ptr);
        held_pagetable_window_mapping_4k_unchanged_at(leaf_k.pt_mp, leaf_k.pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), &leaf_lctx, pagetable_ptr, window, va);
        assert(mmap_4k_leaf_step_pre(steps.view().last().old_u, cpu_id) && mmap_4k_leaf_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id)) by {
            kernel_thread_quota_4k_progress_and_4k_mapping_added_pagetable_rlocked_implies_u_step(&section_start, &leaf_k, &leaf_lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr, va);
            mmap_4k_leaf_step_from_u(kernel_k_to_kernel_u(section_start), kernel_k_to_kernel_u(leaf_k), cpu_id, process_ptr, thread_ptr, va);
        };
        mmap_4k_range_steps_from_leaf(&*steps, leaf_steps, entry_steps.len() as int, cpu_id);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr);
        container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr);
        container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr);
    }
}
} // verus!
