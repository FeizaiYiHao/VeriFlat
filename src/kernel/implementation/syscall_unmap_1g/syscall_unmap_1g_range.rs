use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_unmap_1g_trace::*;
use super::syscall_unmap_1g_leaf::unmap_1g_hide_leaf;
use super::syscall_unmap_1g_reclaim::unmap_1g_reclaim_range;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;

verus! {
/// Unmap every page of `range`, each a present 1G leaf of the write-held page table `pagetable`: hide each leaf, flush the PCID on every cpu, then reclaim each page and refund its quota. Only the range's 1G leaves change.
pub(super) fn unmap_1g_range(
    krnl: &mut KernelK, range: &VaRange1G, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>,
)
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
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap1g { range: *range, unmapped: 0, flushed: false }),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).leaves_present(),
        forall|l4i: L4Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
            ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && old(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
            ==> old(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        range.wf(),
        range.len > 0,
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(range.view()[j])
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g().spec_index(range.view()[j]).present
        },
        old(krnl).prc_mp.spec_index(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + range.len + 1 <= final(steps).view().len() <= old(steps).view().len() + range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 2,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> unmap_1g_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap1g { range: *range, unmapped: range.len, flushed: true }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower,
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).leaves_present(),
        forall|l4i: L4Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
            final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
            ==> final(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
            final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && final(krnl).pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
            ==> final(krnl).pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g().dom().contains(range.view()[j]),
{
    let ghost prc_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
    let ghost ctn_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container;
    let ghost entry = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    let ghost start = steps.view().len() as int;
    assert(krnl.thrd_mp.spec_index(thrd_ptr).inv() && !thread_is_dangling(krnl.thrd_mp.spec_index(thrd_ptr))) by { thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); };
    let mut i = 0usize;
    while i < range.len
        invariant
            prc_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc,
            ctn_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
            entry == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
            start == old(steps).view().len(),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).cpu_id() == cpu_id,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pagetable_window_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).pt_mp.dom().contains(pagetable),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == old(lctx).thread_id(),
            cpu_perm.view().lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == old(lctx).thread_id(),
            thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            old(krnl).prc_mp.spec_index(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
            entry.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            entry.leaves_present(),
            range.len > 0,
            forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> entry.mapping_1g().dom().contains(range.view()[j]) && entry.mapping_1g().spec_index(range.view()[j]).present,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_1g_range_step(steps.view()[j], cpu_id),
            steps.view().len() == old(steps).view().len() + i,
            steps.snapshot_k() == *krnl,
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
            krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap1g { range: *range, unmapped: i, flushed: false }),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            old(krnl).thrd_mp.spec_index(thrd_ptr).inv(),
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr,
            krnl.pt_mp.spec_index(pagetable).view().cr3 == cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
            krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty() || krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0usize, NUM_CPUS),
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower == entry.lower,
            forall|l4i: L4Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().spec_held_l4(l4i)]
                krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && krnl.pt_mp.spec_index(pagetable).view().spec_held_l4(l4i) is Some
                ==> krnl.pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l4(l4i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger krnl.pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i)]
                krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= l4i && pei_valid(l4i) && pei_valid(l3i) && krnl.pt_mp.spec_index(pagetable).view().spec_held_l3(l4i, l3i) is Some
                ==> krnl.pt_mp.spec_index(pagetable).view().spec_resolve_mapping_l3(l4i, l3i) is Some,
            range.wf(),
            i <= range.len,
            whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().dom() == entry.mapping_1g().dom(),
            forall|v: VAddr| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().spec_index(v)]
                !range.view().contains(v) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().spec_index(v) == entry.mapping_1g().spec_index(v),
            forall|j: int| #![trigger range.view()[j]] i <= j < range.len ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().spec_index(range.view()[j]) == entry.mapping_1g().spec_index(range.view()[j]),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_1g().spec_index(range.view()[j]).present,
        decreases range.len - i,
    {
        let va = range.index(i);
        proof {
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
            krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
            krnl.thrd_mp.typed_lock_map_aligned_held_in_dom(lctx.thread_lock_map(), lctx.thread_id()); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        }
        let ghost leaf_pre = *krnl;
        let ghost leaf_lctx = *lctx;
        let ghost leaf_before = steps.view();
        let leaf = unmap_1g_hide_leaf(krnl, pagetable, va, thrd_ptr, Ghost(*range), Ghost(i), Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm);
        proof {
            assert(leaf.0@.pt_lower.view() =~= leaf_pre.pt_lower.view().insert(pagetable, leaf.0@.pt_lower.view().spec_index(pagetable)));
            unmap_1g_leaf_range_steps_from_k(&*steps, leaf_before, start, &leaf_pre, &leaf.0@, &leaf_lctx, cpu_id, prc_ptr, thrd_ptr, pagetable, *range, i, va);
        }
        i = i + 1;
    }
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
    }
    let ghost hv = krnl.pt_mp.spec_index(pagetable).view();
    let ghost flush_entry = *krnl;
    let ghost flush_lctx = *lctx;
    let ghost flush_before = steps.view();
    flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, thrd_ptr, true, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm, pagetable_perm);
    proof {
        unmap_1g_tlb_flush_range_steps_from_k(&*steps, flush_before, start, &flush_entry, &flush_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, *range);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
    }
    let ghost flushed_snap = steps.snapshot_k();
    let ghost flushed_pre = *krnl;
    let ghost flushed_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::Unmap1g { range: *range, unmapped: range.len, flushed: true })), Tracked(&*lctx), thread_perm);
    proof {
        let ghost flushed_before = steps.view();
        let ghost flushed_k = *krnl;
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        unmap_1g_flushed_range_steps_from_k(&*steps, flushed_before, start, &flushed_snap, &flushed_pre, &flushed_k, &flushed_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid,
            *range);
    }
    assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k() == entry.mapping_4k() && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m() == entry.mapping_2m());
    unmap_1g_reclaim_range(krnl, range, pagetable, thrd_ptr, cpu_id, Ghost(start), Ghost(hv), Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm, pagetable_perm);
}
} // verus!
