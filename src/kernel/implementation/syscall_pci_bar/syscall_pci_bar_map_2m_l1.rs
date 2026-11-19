use vstd::prelude::*;
use crate::*;
use super::syscall_pci_bar_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_pci_bar_map_2m_trace::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::{hide_empty_l1_in_window::hide_empty_l1_in_window_wlocked, reclaim_hidden_l1_page_in_window::reclaim_hidden_l1_page_in_window_wlocked,
    unmap_4k_flush_all::flush_pagetable_tlbs};
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::{hide_empty_l1_in_window::hide_empty_l1_in_window_wlocked, reclaim_hidden_l1_page_in_window::reclaim_hidden_l1_page_in_window_wlocked,
    unmap_4k_flush_all::flush_pagetable_tlbs};

verus! {
/// After the enter step of a 2M BAR map whose window, held through `window_perm`, links an empty L1 page: hides the page, flushes the
/// process's PCID on every cpu, records the flush, and reclaims the page with one quota step, leaving the window with no L1 page.
pub(super) fn map_pci_bar_2m_drop_empty_l1(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, slot: usize, index: usize, va: VAddr,
    prc_ptr: RwLockProcessPtr, thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pagetable: RwLockPageTableRoot, cr3: PageTableRoot, pcid: Pcid,
    Tracked(cpu_perm): Tracked<&LockPerm>, Tracked(thread_perm): Tracked<&LockPerm>, Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(window_perm): Tracked<&LockPerm>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        map_pci_bar_2m_trace_after_range(old(steps).view(), cpu_id, slot, index, va),
        old(steps).view().len() == 1,
        va_2m_valid(va),
        spec_va_4k_valid(va),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.state() is WriteLock,
        cpu_perm.thread_id() == old(lctx).thread_id(),
        cpu_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.state() is WriteLock,
        thread_perm.thread_id() == old(lctx).thread_id(),
        thread_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: false }),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        !old(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == old(lctx).thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().higher.kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        old(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
        forall|l1i: L1Index|
            #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, l1i)))]
            pei_valid(l1i)
                ==> !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(spec_index2va((spec_va2index(va).0, spec_va2index(va).1, spec_va2index(va).2, l1i))),
        typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(va)), TypedLockMode::Write),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() }),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        map_pci_bar_2m_trace_after_range(final(steps).view(), cpu_id, slot, index, va),
        final(steps).view()[0] == old(steps).view()[0],
        final(krnl).pci_bars == old(krnl).pci_bars,
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
            syscall_progress: Ghost(Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: true })), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
        }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).view().higher ==
            (PageTableHigher { table_stale_cpus: final(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus, ..old(krnl).pt_mp.spec_index(pagetable).view().higher }),
        final(krnl).pt_mp.spec_index(pagetable).view().higher.table_stale_cpus.view() == Set::<CpuId>::empty(),
        ({
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& post.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& post.lower.hidden_l1_tables_in_locked_windows()
            &&& post.mapping_4k() == pre.mapping_4k() && post.mapping_2m() == pre.mapping_2m() && post.mapping_1g() == pre.mapping_1g()
            &&& post.lower.pagetable_window_locks == pre.lower.pagetable_window_locks
            &&& post.window_view(window_of(va)).l1_table is None
            &&& !post.lower.l2_entry_hides_l1(post.window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
            &&& post.lower.l2_owner(post.window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))
                == (RwLockState::Write { thread_id: window_perm.thread_id(), lock_id: window_perm.lock_id() })
        }),
{
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    let (l2_ptr, l1_ptr) = hide_empty_l1_in_window_wlocked(krnl, pagetable, va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(pagetable_perm), Tracked(window_perm));
    let ghost hidden_steps = steps.view();
    proof {
        kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        assert(krnl.thrd_mp.spec_index(thrd_ptr).inv() && !thread_is_dangling(krnl.thrd_mp.spec_index(thrd_ptr))) by {
            thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
        };
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
    }
    let ghost flush_before = steps.view();
    let ghost flush_entry = *krnl;
    let ghost flush_lctx = *lctx;
    flush_pagetable_tlbs::<true>(krnl, pagetable, cr3, pcid, cpu_id, thrd_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_perm), Tracked(pagetable_perm));
    proof {
        map_pci_bar_2m_tlb_flush_steps_from_k(&*steps, flush_before, &flush_entry, &flush_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, slot, index, va);
        assert(krnl.thrd_mp.spec_index(thrd_ptr).inv() && !thread_is_dangling(krnl.thrd_mp.spec_index(thrd_ptr))) by {
            thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
        };
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr);
    }
    let ghost flushed_before = steps.view();
    let ghost flushed_snap = steps.snapshot_k();
    let ghost flushed_pre = *krnl;
    let ghost flushed_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::MapPciBar2m { va, directory: Mmap2mDirectory::None, flushed: true })), Tracked(&*lctx),
        Tracked(thread_perm));
    let ghost flushed_k = *krnl;
    proof {
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        map_pci_bar_2m_flushed_step_from_k(&*steps, flushed_before, &flushed_snap, &flushed_pre, &flushed_k, &flushed_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, slot,
            index, va);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
    }
    let ghost reclaim_before = steps.view();
    let (_, Ghost(mid), Ghost(mid_lctx)) = reclaim_hidden_l1_page_in_window_wlocked(krnl, pagetable, va, l2_ptr, l1_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(pagetable_perm), Tracked(window_perm));
    proof {
        assert(mid.thrd_mp.spec_index(thrd_ptr).inv() && !thread_is_dangling(mid.thrd_mp.spec_index(thrd_ptr))) by {
            thread_perms_wf_at(mid.thrd_mp, thrd_ptr); thread_cpu_wf_cpu_at(mid.thrd_mp, mid.cpu_arr, cpu_id);
        };
        process_thread_wf_thread_at(mid.prc_mp, mid.thrd_mp, thrd_ptr); container_process_wf_process_at(mid.ctn_mp, mid.prc_mp, prc_ptr); process_perms_wf_at(mid.prc_mp, prc_ptr);
        process_pagetable_wf_process_at(mid.prc_mp, mid.pt_mp, prc_ptr);
        thread_cpu_wf_cpu_at(mid.thrd_mp, mid.cpu_arr, cpu_id); process_cpu_wf_at(mid.prc_mp, mid.cpu_arr, cpu_id);
        map_pci_bar_2m_reclaim_step_from_k(&*steps, reclaim_before, &mid, &mid_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, slot, index, va);
        let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
        let flushed = whole_pagetable(flushed_k.pt_mp, flushed_k.pt_lower.view(), pagetable);
        assert(window_of(va).va == va) by { broadcast use spec_va_2m_valid_index_roundtrip; };
    }
}
} // verus!
