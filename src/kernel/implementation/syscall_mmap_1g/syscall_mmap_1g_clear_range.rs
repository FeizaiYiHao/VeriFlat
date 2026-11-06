use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_clear_trace::*;
use super::syscall_mmap_1g_hide_entry::mmap_1g_hide_l3_entry;
use super::syscall_mmap_1g_clear_reclaim::mmap_1g_reclaim_range;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;

verus! {
/// Clear the 1G slots of `range` in the write-held page table `pagetable`, none of which maps a leaf: hide each L3 entry that links an L2 page, one recorded step per slot; when any slot was hidden, flush the PCID on every cpu, record the flush in the progress, and reclaim every L1 and L2
/// page below the hidden entries. Returns whether any slot was hidden; afterwards no slot of `range` holds an L3 entry or a 1G leaf, and every leaf mapping of the table is unchanged.
pub(super) fn mmap_1g_clear_range(
    krnl: &mut KernelK, range: &VaRange1G, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId,
    cr3: PageTableRoot, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>,
    pagetable_perm: Tracked<&LockPerm>,
) -> (hidden: Ghost<bool>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == old(lctx).thread_id(),
        cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pcid != KERNEL_DEFAULT_PCID,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *range, mapped: 0, directory: false, hidden: false, flushed: false }),
        old(krnl).prc_mp.dom().contains(prc_ptr),
        old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        old(krnl).ctn_mp.dom().contains(ctn_ptr),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i)
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
        forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
            ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
            ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        range.wf(),
        range.len > 0,
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let idx = spec_va2index(range.view()[j]);
            &&& !table.mapping_1g().dom().contains(range.view()[j])
            &&& forall|l2i: L2Index| #![trigger table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))] pei_valid(l2i)
                ==> !table.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))
            &&& forall|l2i: L2Index, l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))] pei_valid(l2i) && pei_valid(l1i)
                ==> !table.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))
        },
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 514 * range.len + NUM_CPUS + 1,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_1g_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *range, mapped: 0, directory: false, hidden: hidden@, flushed: hidden@ }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).prc_mp.dom().contains(prc_ptr),
        !final(krnl).prc_mp.spec_index(prc_ptr).view().zombie,
        !(final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied),
        final(krnl).prc_mp.spec_index(prc_ptr).view().pagetable == pagetable,
        final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pcid == pcid,
        final(krnl).ctn_mp.dom().contains(ctn_ptr),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        ({
            let entry = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& c.mapping_4k() == entry.mapping_4k() && c.mapping_2m() == entry.mapping_2m() && c.mapping_1g() == entry.mapping_1g()
            &&& c.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& c.leaves_present()
            &&& c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|l4i: L4Index| #![trigger c.spec_held_l4(l4i)] #![trigger c.spec_resolve_mapping_l4(l4i)]
                entry.kernel_l4_end() <= l4i && pei_valid(l4i) ==> c.spec_held_l4(l4i) == entry.spec_held_l4(l4i) && c.spec_resolve_mapping_l4(l4i) == entry.spec_resolve_mapping_l4(l4i)
            &&& forall|l4i: L4Index| #![trigger c.spec_held_l4(l4i)] c.kernel_l4_end() <= l4i && pei_valid(l4i) && c.spec_held_l4(l4i) is Some ==> c.spec_resolve_mapping_l4(l4i) is Some
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger c.spec_held_l3(l4i, l3i)]
                c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && c.spec_held_l3(l4i, l3i) is Some ==> c.spec_resolve_mapping_l3(l4i, l3i) is Some
            &&& forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len
                ==> c.spec_held_l3(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])) is None && c.spec_held_1g_l3(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])) is None
        }),
{
    proof { broadcast use spec_va_1g_valid_index_roundtrip; }
    let ghost entry = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    let ghost start = steps.view().len() as int;
    let mut hid_any = false;
    let mut i = 0usize;
    while i < range.len
        invariant
            entry == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
            start == old(steps).view().len(),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).cpu_id() == cpu_id,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).pt_mp.dom().contains(pagetable),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == old(lctx).thread_id(),
            thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
            entry.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            entry.lower.hidden_l1_tables_in_locked_windows(),
            forall|p: PageMapPtr, i: L2Index| #![trigger entry.lower.l2_owner(p, i)] entry.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> entry.lower.l2_owner(p, i) is None,
            forall|l4i: L4Index| #![trigger entry.spec_held_l4(l4i)] entry.kernel_l4_end() <= l4i && pei_valid(l4i) && entry.spec_held_l4(l4i) is Some ==> entry.spec_resolve_mapping_l4(l4i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger entry.spec_held_l3(l4i, l3i)]
                entry.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && entry.spec_held_l3(l4i, l3i) is Some ==> entry.spec_resolve_mapping_l3(l4i, l3i) is Some,
            range.wf(),
            i <= range.len,
            forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
                let idx = spec_va2index(range.view()[j]);
                &&& !entry.mapping_1g().dom().contains(range.view()[j])
                &&& forall|l2i: L2Index| #![trigger entry.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))] pei_valid(l2i)
                    ==> !entry.mapping_2m().dom().contains(spec_index2va((idx.0, idx.1, l2i, 0)))
                &&& forall|l2i: L2Index, l1i: L1Index| #![trigger entry.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))] pei_valid(l2i) && pei_valid(l1i)
                    ==> !entry.mapping_4k().dom().contains(spec_index2va((idx.0, idx.1, l2i, l1i)))
            },
            !hid_any ==> *krnl == *old(krnl) && steps.view() == old(steps).view(),
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + i,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
            krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *range, mapped: 0, directory: false, hidden: hid_any, flushed: false }),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
            krnl.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == KERNEL_MEM_END_L4INDEX,
            krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty() || krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
            ({
                let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                &&& c.mapping_4k() == entry.mapping_4k() && c.mapping_2m() == entry.mapping_2m() && c.mapping_1g() == entry.mapping_1g()
                &&& c.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
                &&& c.lower.hidden_l1_tables_in_locked_windows()
                &&& c.lower.l2_perms == entry.lower.l2_perms
                &&& forall|l4i: L4Index| #![trigger c.spec_held_l4(l4i)] #![trigger c.spec_resolve_mapping_l4(l4i)]
                    entry.kernel_l4_end() <= l4i && pei_valid(l4i) ==> c.spec_held_l4(l4i) == entry.spec_held_l4(l4i) && c.spec_resolve_mapping_l4(l4i) == entry.spec_resolve_mapping_l4(l4i)
                &&& forall|l4i: L4Index, l3i: L3Index| #![trigger c.spec_held_l3(l4i, l3i)]
                    entry.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && c.spec_held_l3(l4i, l3i) is Some
                    ==> c.spec_resolve_mapping_l3(l4i, l3i) is Some || range.view().contains(spec_index2va((l4i, l3i, 0, 0)))
                &&& forall|j: int| #![trigger range.view()[j]] i <= j < range.len ==> {
                    let l4i = spec_v2l4index(range.view()[j]);
                    let l3i = spec_v2l3index(range.view()[j]);
                    &&& c.spec_held_l3(l4i, l3i) == entry.spec_held_l3(l4i, l3i)
                    &&& c.spec_resolve_mapping_l3(l4i, l3i) == entry.spec_resolve_mapping_l3(l4i, l3i)
                }
                &&& forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> {
                    let l4i = spec_v2l4index(range.view()[j]);
                    let l3i = spec_v2l3index(range.view()[j]);
                    &&& c.spec_resolve_mapping_l3(l4i, l3i) is None
                    &&& c.spec_held_1g_l3(l4i, l3i) is None
                    &&& forall|l2i: L2Index| #![trigger c.spec_held_2m_l2(l4i, l3i, l2i)] pei_valid(l2i) ==> c.spec_held_2m_l2(l4i, l3i, l2i) is None
                    &&& forall|l2i: L2Index, l1i: L1Index| #![trigger c.spec_held_4k_l1(l4i, l3i, l2i, l1i)] pei_valid(l2i) && pei_valid(l1i) ==> c.spec_held_4k_l1(l4i, l3i, l2i, l1i) is None
                }
            }),
        decreases range.len - i,
    {
        let va = range.index(i);
        let l4i = v2l4index(va);
        let l3i = v2l3index(va);
        proof {
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable); krnl.default_pagetable_wf_at(pagetable);
            krnl.thrd_mp.typed_lock_map_aligned_held_in_dom(lctx.thread_lock_map(), lctx.thread_id());
            broadcast use spec_va_1g_valid_index_roundtrip;
            assert(spec_va2index(va).0 == l4i && spec_va2index(va).1 == l3i && spec_index2va((l4i, l3i, 0, 0)) == va) by { spec_va_1g_valid_index_roundtrip(va); };
        }
        let table = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
        let l3 = match table.get_entry_l4(l4i) {
            Some(l4_entry) => table.get_entry_l3(l4i, l3i, &l4_entry),
            None => None,
        };
        proof {
            let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            c.mapping_free_l3_slot_implies_no_leaf_below(l4i, l3i); c.higher.wf_mapping_1g_at(l4i, l3i);
            if c.spec_resolve_mapping_l4(l4i) is Some { c.higher.spec_held_l4_resolves_implies_spec_held_1g_l3_eq_resolve(l4i, l3i); }
        }
        if l3.is_some() {
            proof { process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); }
            let ghost pre = *krnl;
            let ghost pre_lctx = *lctx;
            let ghost before = steps.view();
            let ret = mmap_1g_hide_l3_entry(krnl, pagetable, l4i, l3i, thrd_ptr, Ghost(SyscallProgress::Mmap1g { range: *range, mapped: 0, directory: false, hidden: hid_any, flushed: false }),
                Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
            proof {
                let ghost old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
                let ghost removed = old_c.lower.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i);
                mmap_1g_hide_range_steps_from_k(&*steps, before, start, &pre, &ret.0@, &pre_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, *range, i as int, removed, hid_any);
            }
            hid_any = true;
        }
        i = i + 1;
    }
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
    }
    if hid_any {
        let ghost hc = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        let ghost flush_entry = *krnl;
        let ghost flush_lctx = *lctx;
        let ghost flush_before = steps.view();
        flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, thrd_ptr, true, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm, pagetable_perm);
        proof {
            mmap_1g_tlb_flush_range_steps_from_k(&*steps, flush_before, start, &flush_entry, &flush_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, *range);
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
            container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
        }
        let ghost flushed_snap = steps.snapshot_k();
        let ghost flushed_pre = *krnl;
        let ghost flushed_lctx = *lctx;
        krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::Mmap1g { range: *range, mapped: 0, directory: false, hidden: true, flushed: true })), Tracked(&*lctx),
            thread_perm);
        proof {
            let ghost flushed_before = steps.view();
            let ghost flushed_k = *krnl;
            krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
            mmap_1g_flushed_range_steps_from_k(&*steps, flushed_before, start, &flushed_snap, &flushed_pre, &flushed_k, &flushed_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable,
                *range);
        }
        mmap_1g_reclaim_range(krnl, range, pagetable, thrd_ptr, cpu_id, Ghost(prc_ptr), Ghost(ctn_ptr), Ghost(start), Ghost(hc), Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm);
    }
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr); container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
    }
    Ghost(hid_any)
}
} // verus!
