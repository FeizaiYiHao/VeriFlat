use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_4k_map_one_leaf::map_one_mmap_4k_page;
use super::syscall_mmap_4k_spec::*;
use super::syscall_mmap_4k_trace::*;

verus! {
/// Under the pagetable's big read lock, holding exactly the 2M windows of `range` through `window_perms`, publish a present, writable, executable
/// leaf for every page of `range` in order, installing a missing L1 table first; each page records its L1 table, if
/// installed, as a directory step and its leaf as a leaf step. Every held window keeps its lock state and stale CPUs, and
/// its leaves stay present.
pub(super) fn mmap_4k_map_leaf_range(
    krnl: &mut KernelK, range: &VaRange4K, alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, Ghost(phase): Ghost<Mmap4kPhase>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(window_perms): Tracked<&Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
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
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 2 * range.len,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range: *range, mapped: 0, directory: Mmap4kDirectory::None, phase }),
        !(phase is Fill),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        range.wf(),
        range.len > 0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.start),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher.spec_mapping_4k_va_range_windows_exist(range),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(*range).contains(w)),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
            let table = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& table.window_leaves_present(w)
            &&& window_perms.dom().contains(w)
            &&& table.window_view(w).lock_state == (SpinLockState::Some { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
        },
        forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), range.view()[j]]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && 0 <= j < range.len && spec_v2l4index(range.view()[j]) == spec_v2l4index(w.va)
                && spec_v2l3index(range.view()[j]) == spec_v2l3index(w.va) && spec_v2l2index(range.view()[j]) == spec_v2l2index(w.va) ==> {
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(range.view()[j])
            },
    ensures
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + range.len <= final(steps).view().len() <= old(steps).view().len() + 2 * range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_4k_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        final(krnl).prc_mp.dom().contains(process_ptr),
        final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        final(krnl).thr_mp.dom().contains(thread_ptr),
        !final(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        final(krnl).thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range: *range, mapped: range.len, directory: Mmap4kDirectory::None, phase }),
        thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
            let pre = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let post = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.window_view(w).lock_state == pre.window_view(w).lock_state
            &&& post.window_view(w).stale_cpus == pre.window_view(w).stale_cpus
            &&& post.window_leaves_present(w)
        },
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            let post = pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.mapping_4k().dom().contains(range.view()[j])
            &&& post.mapping_4k().spec_index(range.view()[j]).present
            &&& post.mapping_4k().spec_index(range.view()[j]).write
            &&& !post.mapping_4k().spec_index(range.view()[j]).execute_disable
        },
{
    let ghost entry = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let range_len = range.len;
    let mut i: usize = 0;
    while i < range_len
        invariant
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            steps.snapshot_k() == *krnl,
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            lctx.page_lock_map().dom().is_empty(),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            entry == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            !krnl.cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] is InStep,
            krnl.ctn_mp.dom().contains(container_ptr),
            krnl.ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            krnl.ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            krnl.allc_4k_mp.dom().contains(alloc_ptr_4k),
            krnl.prc_mp.dom().contains(process_ptr),
            krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            krnl.thr_mp.dom().contains(thread_ptr),
            !krnl.thr_mp.spec_index(thread_ptr).being_killed(),
            !thread_is_dangling(krnl.thr_mp.spec_index(thread_ptr)),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            !krnl.thr_mp.spec_index(thread_ptr).view_ghost().exited,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            krnl.thr_mp.spec_index(thread_ptr).view().state == old(krnl).thr_mp.spec_index(thread_ptr).view().state,
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            krnl.thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
            krnl.thr_mp.spec_index(thread_ptr).view().quota_4k >= 2 * (range_len - i),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k { range: *range, mapped: i, directory: Mmap4kDirectory::None, phase }),
            !(phase is Fill),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.state() is ReadLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            krnl.pt_mp.dom().contains(pagetable_ptr),
            krnl.pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
            krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            range.wf(),
            range_len == range.len,
            i <= range_len,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(range.start),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher.spec_mapping_4k_va_range_windows_exist(range),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(*range).contains(w)),
            forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), range.view()[j]]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && 0 <= j < range.len && spec_v2l4index(range.view()[j]) == spec_v2l4index(w.va)
                    && spec_v2l3index(range.view()[j]) == spec_v2l3index(w.va) && spec_v2l2index(range.view()[j]) == spec_v2l2index(w.va)
                    ==> !entry.mapping_2m().dom().contains(w.va),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> {
                &&& old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(range.view()[j])))
                &&& spec_va2index(window_of(range.view()[j]).va) == (spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j]), spec_v2l2index(range.view()[j]), 0usize)
            },
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
                let cur = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& window_perms.dom().contains(w)
                &&& entry.window_view(w).lock_state == (SpinLockState::Some { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
                &&& cur.window_view(w).lock_state == entry.window_view(w).lock_state
                &&& cur.window_view(w).stale_cpus == entry.window_view(w).stale_cpus
                &&& cur.mapping_2m().dom().contains(w.va) == entry.mapping_2m().dom().contains(w.va)
                &&& cur.window_leaves_present(w)
            },
            forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), range.view()[j]]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && i <= j < range.len && spec_v2l4index(range.view()[j]) == spec_v2l4index(w.va)
                    && spec_v2l3index(range.view()[j]) == spec_v2l3index(w.va) && spec_v2l2index(range.view()[j]) == spec_v2l2index(w.va)
                    ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(range.view()[j]),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> {
                let cur = pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& cur.mapping_4k().dom().contains(range.view()[j])
                &&& cur.mapping_4k().spec_index(range.view()[j]).present
                &&& cur.mapping_4k().spec_index(range.view()[j]).write
                &&& !cur.mapping_4k().spec_index(range.view()[j]).execute_disable
            },
            old(steps).view().len() + i <= steps.view().len() <= old(steps).view().len() + 2 * i,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> mmap_4k_range_step(steps.view()[j], cpu_id),
        decreases range_len - i,
    {
        let va = range.index(i);
        let ghost win = window_of(va);
        proof {
            assert(va_4k_valid(va) && range.start <= va && spec_va_4k_valid(range.start) && spec_va_4k_valid(va)) by { range.va_range_lemma(); };
            spec_v2l4index_monotonic(range.start, va);
            assert(old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, win)) && spec_va2index(win.va) == (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize)) by {
                let last_va = range.view().spec_index(range.len - 1);
                range.va_range_lemma();
                broadcast use spec_va_4k_valid_index_roundtrip;
                spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(range.start), spec_va2index(va));
                spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(va), spec_va2index(last_va));
                va_range_2m_windows_contains_window_of_every_va_in_range(*range);
            };
        }
        map_one_mmap_4k_page(krnl, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, va, Ghost(*range), Ghost(i), Ghost(phase), Tracked(&mut *lctx),
            Tracked(&mut *steps), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(window_perms.tracked_borrow(win)));
        i = i + 1;
    }
}

/// Holding the mmap locks, the big read lock on `pagetable_ptr`, and exactly the 2M windows of `va_range` after the partial
/// trace `entered` after entering in `enter_phase` and the range steps that follow it: maps every page, clears the progress,
/// releases the windows and every lock, and records the exiting step.
pub(super) fn mmap_4k_map_leaves_and_finish(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va: VAddr, range: usize, va_range: &VaRange4K,
    alloc_ptr_4k: RwLockPageAllocatorPtr, thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    Ghost(enter_phase): Ghost<Mmap4kPhase>, Ghost(entered): Ghost<Seq<KernelStep>>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        old(krnl).inv(),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        range > 0,
        va_4k_valid(va),
        *va_range == mmap_4k_syscall_va_range(va, range),
        va_range.wf(),
        enter_phase is Read || enter_phase is Fill,
        mmap_4k_trace_after_enter(entered, cpu_id, *va_range, enter_phase),
        entered.len() == if enter_phase is Fill { 2int } else { 1int },
        entered.len() <= old(steps).view().len() <= entered.len() + 2 * range + 1,
        forall|j: int| #![trigger old(steps).view()[j]] 0 <= j < entered.len() ==> old(steps).view()[j] == entered[j],
        forall|j: int| #![trigger old(steps).view()[j]] entered.len() <= j < old(steps).view().len() ==> mmap_4k_range_step(old(steps).view()[j], cpu_id),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
        old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
        old(krnl).prc_mp.dom().contains(process_ptr),
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        old(krnl).thr_mp.spec_index(thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 2 * range,
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap4k {
            range: *va_range, mapped: 0, directory: Mmap4kDirectory::None, phase: if enter_phase is Read { Mmap4kPhase::Read } else { Mmap4kPhase::Filled },
        }),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va_range.start),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher.spec_mapping_4k_va_range_windows_exist(va_range),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && va_range_2m_windows(*va_range).contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*va_range).contains(w)] va_range_2m_windows(*va_range).contains(w) ==> {
            let table = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& window_perms.dom().contains(w)
            &&& window_perms.index(w).state() is WriteLock
            &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
            &&& table.lower.l2_owner(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)) == (SpinLockState::Some { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
            &&& table.window_leaves_present(w)
            &&& !table.lower.window_stale_cpus.dom().contains((table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
        },
        forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), va_range.view()[j]]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && 0 <= j < range && spec_v2l4index(va_range.view()[j]) == spec_v2l4index(w.va)
                && spec_v2l3index(va_range.view()[j]) == spec_v2l3index(w.va) && spec_v2l2index(va_range.view()[j]) == spec_v2l2index(w.va) ==> {
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va_range.view()[j])
            },
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).thread_lock_map().dom() =~= set![thread_ptr],
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_cache_1g_lock_map().dom().is_empty(),
        old(lctx).allocator_global_pool_1g_lock_map().dom().is_empty(),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        entered.len() + range + 1 <= final(steps).view().len() <= entered.len() + 4 * range + 2,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < entered.len() ==> final(steps).view()[j] == entered[j],
        mmap_4k_syscall_trace(final(steps).view(), cpu_id, va, range, enter_phase),
        mmap_4k_syscall_success_mapped(final(krnl), cpu_id, va, range),
{
    let ghost leaf_phase = if enter_phase is Read { Mmap4kPhase::Read } else { Mmap4kPhase::Filled };
    mmap_4k_map_leaf_range(krnl, va_range, alloc_ptr_4k, thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, Ghost(leaf_phase), Tracked(&mut *lctx), Tracked(&mut *steps),
        Tracked(&thread_lock_perm), Tracked(&pagetable_lock_perm), Tracked(&window_perms));
    let ghost range_steps = steps.view();
    let ghost exit_start = *krnl;
    let ghost exit_lctx = *lctx;
    proof { mmap_4k_trace_range_steps(&*steps, entered, cpu_id, *va_range, enter_phase); }
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(None), Tracked(&*lctx), Tracked(&thread_lock_perm));
    krnl.unlock_pagetable_range_windows(pagetable_ptr, va_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx), Tracked(window_perms));
    proof { krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr); }
    krnl.runlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    krnl.wunlock_thread(thread_ptr, Tracked(&mut *lctx), Tracked(thread_lock_perm));
    proof { cpu_op_wf_at(old(krnl).cpu_op.view().view(), old(krnl).cpu_arr, cpu_id); cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }
    krnl.wunlock_own_cpu(cpu_id, Tracked(&mut *lctx), Tracked(cpu_lock_perm));
    let ghost exit_k = *krnl;
    proof {
        steps.end_kernel_step_thread_syscall_progress_changed(&*krnl, &*lctx, thread_ptr);
        assert(mmap_4k_syscall_trace(steps.view(), cpu_id, va, range, enter_phase)) by {
            kernel_cpu_thread_unlocked_pagetable_runlocked_and_progress_changed_implies_u_step(&exit_start, &exit_k, &exit_lctx, cpu_id, thread_ptr, process_ptr, pagetable_ptr);
            process_cpu_wf_at(exit_start.prc_mp, exit_start.cpu_arr, cpu_id); process_pagetable_match_process_at(exit_start.prc_mp, exit_start.pt_mp, process_ptr);
            mmap_4k_exit_step_from_u(&exit_start, kernel_k_to_kernel_u(exit_k), cpu_id, process_ptr, thread_ptr, pagetable_ptr, *va_range, exit_k.pt_mp.spec_index(pagetable_ptr).lock_state_u(),
                pagetable_c(exit_k.pt_mp, exit_k.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks);
            mmap_4k_trace_exit_step(&*steps, range_steps, kernel_k_to_kernel_u(exit_start), kernel_k_to_kernel_u(exit_k), cpu_id, va, range, enter_phase);
        };
        assert(mmap_4k_syscall_success_mapped(krnl, cpu_id, va, range)) by { va_range.va_range_lemma(); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr); };
    }
}
} // verus!
