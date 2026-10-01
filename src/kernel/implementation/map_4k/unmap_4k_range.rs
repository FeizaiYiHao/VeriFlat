use vstd::prelude::*;
use crate::*;
use super::unmap_4k_spec::*;
use super::unmap_4k_trace::*;
use super::unmap_4k_present::clear_4k_mapping_present;
use super::unmap_4k_flush_all::flush_pagetable_tlbs;
use super::unmap_4k_reclaim_one::reclaim_unmapped_4k_page;

verus! {
pub fn unmap_4k_range(krnl: &mut KernelK, range: &VaRange4K, pagetable: RwLockPageTableRoot, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_published[cpu_id as int].view() == (cr3, pcid),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: *range, unmapped: 0, flushed: false }),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        range.wf(),
        range.len > 0,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
        forall|j: int| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j))]
            #![trigger old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j))] 0 <= j < range.len
            ==> old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j)) && old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j)).present,
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + range.len + 1 <= final(steps).view().len() <= old(steps).view().len() + range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 2,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> unmap_4k_range_step(final(steps).view()[j], cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        old(steps).nonlock_view().len() + range.len + 1 <= final(steps).nonlock_view().len(),
        final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 2,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: *range, unmapped: range.len, flushed: true }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
        final(krnl).pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
        pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pagetable, final(krnl).pt_mp.spec_index(pagetable).view()),
{
    let ghost process_ptr = krnl.thr_mp.spec_index(thread_ptr).view().owning_proc;
    let ghost container_ptr = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.thr_mp.spec_index(thread_ptr).inv()) by { reveal(thread_perms_wf); };
    assert(krnl.prc_mp.dom().contains(process_ptr) && !krnl.prc_mp.spec_index(process_ptr).view().zombie && krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable
        && krnl.pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr) by { reveal(process_pagetable_match); reveal(process_thread_wf); };
    let start = range.start;
    let mut i = 0usize;
    while i < range.len
        invariant
            process_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            container_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            old(krnl).prc_mp.dom().contains(process_ptr),
            !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
            old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
            steps.snapshot_k() == *krnl,
            steps.view().len() == old(steps).view().len() + i,
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.page_lock_map().dom().is_empty(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_MAJOR),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            index_valid(NUM_CPUS, cpu_id),
            lctx.cpu_id() == cpu_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == lctx.thread_id(),
            cpu_perm.view().lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            krnl.cpu_published[cpu_id as int].view() == (cr3, pcid),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == lctx.thread_id(),
            pagetable_perm.view().lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            krnl.pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
            range.wf(),
            range.len > 0,
            start == range.start,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()) == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()),
            i <= range.len,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).inv(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).pt_mp.dom().contains(pagetable),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: *range, unmapped: i, flushed: false }),
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            steps.nonlock_view().len() == old(steps).nonlock_view().len() + i,
            krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().dom(),
            forall|j: int| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j))] #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j))] 0 <= j < range.len ==> { &&& krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j)) &&& krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j)).present == (i <= j) },
        decreases range.len - i,
    {
        let va = range.index(i);
        proof {
            assert(va_4k_valid(va) && range.start <= va && spec_va_4k_valid(range.start) && spec_va_4k_valid(va)) by { range.va_range_lemma(); };
            assert(krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0) by { spec_v2l4index_monotonic(start, va); };
            assert(lctx.thread_lock_map().dom().subset_of(krnl.thr_mp.dom())) by { krnl.thr_mp.typed_lock_map_aligned_held_in_dom(lctx.thread_lock_map(), lctx.thread_id()); };
            use_type_invariant(&*steps);
            assert(unmap_4k_locked(steps.snapshot_u(), cpu_id) && steps.snapshot_u().cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
                && steps.snapshot_u().thread_map[thread_ptr].owning_proc == krnl.thr_mp.spec_index(thread_ptr).view().owning_proc
                && steps.snapshot_u().thread_map[thread_ptr].syscall_progress == krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()) by {
                kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, thread_ptr, None);
            };
        }
        clear_4k_mapping_present(krnl, pagetable, va, Tracked(&mut *lctx), pagetable_perm);
        krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Unmap4k { range: *range, unmapped: (i + 1) as usize, flushed: false })), Tracked(&*lctx), thread_perm);
        proof {
            assert(kernel_process_4k_mapping_changed(&steps.snapshot_k(), &*krnl, process_ptr, pagetable, va)) by { reveal(kernel_process_4k_mapping_changed); };
            assert(unmap_4k_leaf_step_pre(steps.snapshot_u(), cpu_id) && unmap_4k_leaf_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id)) by {
                range.va_range_lemma();
                kernel_pagetable_4k_present_cleared_and_progress_changed_implies_u_step(&steps.snapshot_k(), &*krnl, pagetable, va, thread_ptr);
                unmap_4k_leaf_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, process_ptr, thread_ptr, va);
            };
            let ghost leaf_before = steps.view();
            let ghost leaf_pre = steps.snapshot_u();
            let ghost leaf_k = *krnl;
            krnl.kernel_step_boundary_process_4k_mapping_changed(&mut *lctx, &mut *steps, process_ptr, pagetable, va, process_ptr, pagetable, thread_ptr);
            assert(forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id)) by {
                unmap_4k_range_steps_from_leaf(&*steps, leaf_before, old(steps).view().len() as int, leaf_pre, kernel_k_to_kernel_u(leaf_k), cpu_id);
            };
        }
        i = i + 1;
    }
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, thread_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm);
    proof {
        use_type_invariant(&*steps);
        assert(unmap_4k_flush_step_pre(steps.snapshot_u(), cpu_id) && steps.snapshot_u().cpu_array[cpu_id as int].current_thread == Some(thread_ptr)
            && steps.snapshot_u().thread_map[thread_ptr].syscall_progress == krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()) by {
            kernel_write_held_context_projection(&*krnl, &*lctx, cpu_id, process_ptr, thread_ptr, None);
            unmap_4k_flush_step_pre_from_u(steps.snapshot_u(), cpu_id, thread_ptr);
        };
    }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Unmap4k { range: *range, unmapped: range.len, flushed: true })), Tracked(&*lctx), thread_perm);
    proof {
        assert(unmap_4k_flush_step_pre(steps.snapshot_u(), cpu_id) && unmap_4k_flushed_step(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id)) by {
            kernel_thread_syscall_progress_changed_implies_u_step(&steps.snapshot_k(), &*krnl, thread_ptr);
            unmap_4k_flushed_step_from_u(steps.snapshot_u(), kernel_k_to_kernel_u(*krnl), cpu_id, thread_ptr);
        };
        let ghost flushed_before = steps.view();
        let ghost flushed_pre = steps.snapshot_u();
        let ghost flushed_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        assert(forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id)) by {
            unmap_4k_range_steps_from_flushed(&*steps, flushed_before, old(steps).view().len() as int, flushed_pre, kernel_k_to_kernel_u(flushed_k), cpu_id);
        };
    }
    assert(krnl.thr_mp.spec_index(thread_ptr).inv()) by { reveal(thread_perms_wf); };
    assert(krnl.thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH) by { reveal(container_thread_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    i = 0;
    while i < range.len
        invariant
            process_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
            container_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container,
            old(krnl).prc_mp.dom().contains(process_ptr),
            !old(krnl).prc_mp.spec_index(process_ptr).view().zombie,
            old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable,
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write),
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
            steps.snapshot_k() == *krnl,
            old(steps).view().len() + range.len + 1 <= steps.view().len() <= old(steps).view().len() + range.len + NUM_CPUS + 1,
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.page_lock_map().dom().is_empty(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_MAJOR),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            index_valid(NUM_CPUS, cpu_id),
            lctx.cpu_id() == cpu_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == lctx.thread_id(),
            cpu_perm.view().lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == lctx.thread_id(),
            pagetable_perm.view().lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            range.wf(),
            range.len > 0,
            start == range.start,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_2m(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable).view().mapping_1g(),
            krnl.pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()) == old(krnl).pt_mp.spec_index(pagetable).view().mapping_4k().remove_keys(range.view().to_set()),
            i <= range.len,
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).inv(),
            old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            old(krnl).pt_mp.dom().contains(pagetable),
            old(steps).nonlock_view().len() + range.len + 1 <= steps.nonlock_view().len() <= old(steps).nonlock_view().len() + range.len + NUM_CPUS + 1,
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
                syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view()
            }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: *range, unmapped: range.len, flushed: true }),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pagetable, krnl.pt_mp.spec_index(pagetable).view()),
            forall|j: int| #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j))] #![trigger krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j))] 0 <= j < range.len ==> (if j < i { !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j)) } else { krnl.pt_mp.spec_index(pagetable).view().mapping_4k().dom().contains(range.view().spec_index(j)) && !krnl.pt_mp.spec_index(pagetable).view().mapping_4k().spec_index(range.view().spec_index(j)).present }),
        decreases range.len - i,
    {
        let va = range.index(i);
        proof {
            assert(va_4k_valid(va) && range.start <= va && spec_va_4k_valid(range.start) && spec_va_4k_valid(va)) by { range.va_range_lemma(); };
            assert(krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0) by { spec_v2l4index_monotonic(start, va); };
            kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        }
        reclaim_unmapped_4k_page(krnl, pagetable, va, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
        i = i + 1;
    }
    proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
    let ghost refund_before = steps.view();
    let ghost refund_progress = krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()) by { reveal(thread_perms_wf); };
        assert(forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id)) by {
            unmap_4k_range_steps_from_refund(&*steps, refund_before, old(steps).view().len() as int, cpu_id, thread_ptr, process_ptr, container_ptr, refund_progress);
        };
    }
}
}
