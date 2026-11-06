use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_mmap_1g_clear_trace::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::mmap_1g_reclaim_table_page::mmap_1g_reclaim_table_page;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::mmap_1g_reclaim_table_page::mmap_1g_reclaim_table_page;

verus! {
/// After every L3 entry of `range` that linked an L2 page was hidden and flushed in the write-held page table `pagetable`: reclaim, slot by slot, each L1 page the hidden L2 page links and then the L2 page, one recorded quota step per page. `hc` is the table at the end of the hide pass;
/// the table differs from it only in its stale-CPU set.
pub(super) fn mmap_1g_reclaim_range(
    krnl: &mut KernelK, range: &VaRange1G, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, Ghost(prc_ptr): Ghost<RwLockProcessPtr>,
    Ghost(ctn_ptr): Ghost<RwLockContainerPtr>, Ghost(start): Ghost<int>, Ghost(hc): Ghost<WholePageTable<PT_TYPE>>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, pagetable_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        forall|j: int| #![trigger old(steps).view()[j]] start <= j < old(steps).view().len() ==> mmap_1g_range_step(old(steps).view()[j], cpu_id),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *range, mapped: 0, directory: false, hidden: true, flushed: true }),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        old(krnl).pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus, ..hc.higher }),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower == hc.lower,
        hc.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
        hc.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        hc.lower.hidden_l1_tables_in_locked_windows(),
        forall|p: PageMapPtr, i: L2Index| #![trigger hc.lower.l2_owner(p, i)] hc.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> hc.lower.l2_owner(p, i) is None,
        forall|l4i: L4Index| #![trigger hc.spec_held_l4(l4i)] hc.kernel_l4_end() <= l4i && pei_valid(l4i) && hc.spec_held_l4(l4i) is Some ==> hc.spec_resolve_mapping_l4(l4i) is Some,
        forall|l4i: L4Index, l3i: L3Index| #![trigger hc.spec_held_l3(l4i, l3i)]
            hc.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && hc.spec_held_l3(l4i, l3i) is Some
            ==> hc.spec_resolve_mapping_l3(l4i, l3i) is Some || range.view().contains(spec_index2va((l4i, l3i, 0, 0))),
        range.wf(),
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            let l4i = spec_v2l4index(range.view()[j]);
            let l3i = spec_v2l3index(range.view()[j]);
            &&& hc.spec_resolve_mapping_l3(l4i, l3i) is None
            &&& hc.spec_held_1g_l3(l4i, l3i) is None
            &&& forall|i: L2Index| #![trigger hc.spec_held_2m_l2(l4i, l3i, i)] pei_valid(i) ==> hc.spec_held_2m_l2(l4i, l3i, i) is None
            &&& forall|i: L2Index, i1: L1Index| #![trigger hc.spec_held_4k_l1(l4i, l3i, i, i1)] pei_valid(i) && pei_valid(i1) ==> hc.spec_held_4k_l1(l4i, l3i, i, i1) is None
        },
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 513 * range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] start <= j < final(steps).view().len() ==> mmap_1g_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr) == old(krnl).thrd_mp.spec_index(thrd_ptr),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        ({
            let c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& c.mapping_4k() == hc.mapping_4k() && c.mapping_2m() == hc.mapping_2m() && c.mapping_1g() == hc.mapping_1g()
            &&& c.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|l4i: L4Index| #![trigger c.spec_held_l4(l4i)] #![trigger c.spec_resolve_mapping_l4(l4i)]
                hc.kernel_l4_end() <= l4i && pei_valid(l4i) ==> c.spec_held_l4(l4i) == hc.spec_held_l4(l4i) && c.spec_resolve_mapping_l4(l4i) == hc.spec_resolve_mapping_l4(l4i)
            &&& forall|l4i: L4Index, l3i: L3Index| #![trigger c.spec_held_l3(l4i, l3i)]
                c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && c.spec_held_l3(l4i, l3i) is Some ==> c.spec_resolve_mapping_l3(l4i, l3i) is Some
            &&& forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len
                ==> c.spec_held_l3(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])) is None && c.spec_held_1g_l3(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])) is None
        }),
{
    proof { broadcast use spec_va_1g_valid_index_roundtrip; }
    let ghost oc = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    let mut j = 0usize;
    while j < range.len
        invariant
            oc == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
            0 <= start <= old(steps).view().len(),
            forall|k: int| #![trigger old(steps).view()[k]] start <= k < old(steps).view().len() ==> mmap_1g_range_step(old(steps).view()[k], cpu_id),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).cpu_id() == cpu_id,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).pt_mp.dom().contains(pagetable),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range: *range, mapped: 0, directory: false, hidden: true, flushed: true }),
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            old(krnl).pt_mp.spec_index(pagetable).view() == (PageTableHigher { table_stale_cpus: old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus, ..hc.higher }),
            hc.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
            hc.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
            forall|l4i: L4Index| #![trigger hc.spec_held_l4(l4i)] hc.kernel_l4_end() <= l4i && pei_valid(l4i) && hc.spec_held_l4(l4i) is Some ==> hc.spec_resolve_mapping_l4(l4i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger hc.spec_held_l3(l4i, l3i)]
                hc.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && hc.spec_held_l3(l4i, l3i) is Some
                ==> hc.spec_resolve_mapping_l3(l4i, l3i) is Some || range.view().contains(spec_index2va((l4i, l3i, 0, 0))),
            range.wf(),
            j <= range.len,
            forall|k: int| #![trigger range.view()[k]] 0 <= k < range.len ==> {
                let l4i = spec_v2l4index(range.view()[k]);
                let l3i = spec_v2l3index(range.view()[k]);
                &&& hc.spec_resolve_mapping_l3(l4i, l3i) is None
                &&& hc.spec_held_1g_l3(l4i, l3i) is None
                &&& forall|i: L2Index| #![trigger hc.spec_held_2m_l2(l4i, l3i, i)] pei_valid(i) ==> hc.spec_held_2m_l2(l4i, l3i, i) is None
                &&& forall|i: L2Index, i1: L1Index| #![trigger hc.spec_held_4k_l1(l4i, l3i, i, i1)] pei_valid(i) && pei_valid(i1) ==> hc.spec_held_4k_l1(l4i, l3i, i, i1) is None
            },
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + 513 * j,
            forall|k: int| #![trigger steps.view()[k]] 0 <= k < old(steps).view().len() ==> steps.view()[k] == old(steps).view()[k],
            forall|k: int| #![trigger steps.view()[k]] start <= k < steps.view().len() ==> mmap_1g_range_step(steps.view()[k], cpu_id),
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr) == old(krnl).thrd_mp.spec_index(thrd_ptr),
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
            krnl.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == hc.kernel_l4_end(),
            krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            ({
                let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                &&& c.mapping_4k() == hc.mapping_4k() && c.mapping_2m() == hc.mapping_2m() && c.mapping_1g() == hc.mapping_1g()
                &&& c.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
                &&& c.lower.hidden_l1_tables_in_locked_windows()
                &&& forall|p: PageMapPtr, i: L2Index| #![trigger c.lower.l2_owner(p, i)] c.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> c.lower.l2_owner(p, i) is None
                &&& forall|l4i: L4Index| #![trigger c.spec_held_l4(l4i)] #![trigger c.spec_resolve_mapping_l4(l4i)]
                    hc.kernel_l4_end() <= l4i && pei_valid(l4i) ==> c.spec_held_l4(l4i) == hc.spec_held_l4(l4i) && c.spec_resolve_mapping_l4(l4i) == hc.spec_resolve_mapping_l4(l4i)
                &&& forall|l4i: L4Index, l3i: L3Index| #![trigger c.spec_held_l3(l4i, l3i)]
                    hc.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> c.spec_held_l3(l4i, l3i) == hc.spec_held_l3(l4i, l3i) || c.spec_held_l3(l4i, l3i) is None
                &&& forall|l4i: L4Index, l3i: L3Index| #![trigger c.spec_held_1g_l3(l4i, l3i)]
                    hc.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) ==> c.spec_held_1g_l3(l4i, l3i) == hc.spec_held_1g_l3(l4i, l3i)
                &&& forall|l4i: L4Index, l3i: L3Index, i: L2Index| #![trigger c.spec_held_2m_l2(l4i, l3i, i)]
                    hc.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(i) ==> c.spec_held_2m_l2(l4i, l3i, i) == hc.spec_held_2m_l2(l4i, l3i, i)
                &&& forall|l4i: L4Index, l3i: L3Index, i: L2Index, i1: L1Index| #![trigger c.spec_held_4k_l1(l4i, l3i, i, i1)]
                    hc.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(i) && pei_valid(i1) ==> c.spec_held_4k_l1(l4i, l3i, i, i1) == hc.spec_held_4k_l1(l4i, l3i, i, i1)
                &&& forall|k: int| #![trigger range.view()[k]] 0 <= k < j ==> c.spec_held_l3(spec_v2l4index(range.view()[k]), spec_v2l3index(range.view()[k])) is None
            }),
        decreases range.len - j,
    {
        let va = range.index(j);
        let l4i = v2l4index(va);
        let l3i = v2l3index(va);
        proof {
            broadcast use spec_va_1g_valid_index_roundtrip;
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        }
        let table = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
        let l3 = match table.get_held_entry_l4(l4i) {
            Some(l4_entry) => table.get_held_entry_l3(l4i, l3i, &l4_entry),
            None => None,
        };
        if let Some(l3_entry) = l3 {
            proof {
                let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                assert(c.spec_resolve_mapping_l3(l4i, l3i) is None) by {
                    if c.spec_resolve_mapping_l3(l4i, l3i) is Some {
                        c.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(l4i, l3i); c.higher.spec_resolve_mapping_l4_some_implies_spec_held_l4_eq(l4i);
                        hc.higher.spec_resolve_mapping_l4_some_implies_spec_held_l4_eq(l4i);
                    }
                };
            }
            mmap_1g_reclaim_slot(krnl, pagetable, l4i, l3i, &l3_entry, thrd_ptr, cpu_id, Ghost(prc_ptr), Ghost(ctn_ptr), Ghost(*range), Ghost(start), Tracked(&mut *lctx), Tracked(&mut *steps),
                pagetable_perm);
        }
        j = j + 1;
    }
    proof {
        broadcast use PageTableHigher::spec_resolve_mapping_l4_some_implies_spec_held_l4_eq, PageTableHigher::spec_resolve_mapping_l3_some_implies_spec_held_l3_eq;
        spec_index2va_injective();
    }
}

/// Reclaim, in the write-held page table `pagetable`, each L1 page that the L2 page `l3_entry` links under the hidden L3 entry `(l4i, l3i)` and then that L2 page, which drops the entry: one recorded quota step per page. Every other entry and every leaf stays.
fn mmap_1g_reclaim_slot(
    krnl: &mut KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index, l3i: L3Index, l3_entry: &PageEntry, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, Ghost(prc_ptr): Ghost<RwLockProcessPtr>,
    Ghost(ctn_ptr): Ghost<RwLockContainerPtr>, Ghost(range): Ghost<VaRange1G>, Ghost(start): Ghost<int>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    pagetable_perm: Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        forall|j: int| #![trigger old(steps).view()[j]] start <= j < old(steps).view().len() ==> mmap_1g_range_step(old(steps).view()[j], cpu_id),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: true }),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        ({
            let c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            &&& c.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i)
            &&& c.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger c.lower.l2_owner(p, i)] c.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> c.lower.l2_owner(p, i) is None
            &&& c.spec_held_l3(l4i, l3i) == Some(*l3_entry)
            &&& c.spec_resolve_mapping_l3(l4i, l3i) is None
            &&& forall|i: L2Index| #![trigger c.spec_held_2m_l2(l4i, l3i, i)] pei_valid(i) ==> c.spec_held_2m_l2(l4i, l3i, i) is None
            &&& forall|i: L2Index, i1: L1Index| #![trigger c.spec_held_4k_l1(l4i, l3i, i, i1)] pei_valid(i) && pei_valid(i1) ==> c.spec_held_4k_l1(l4i, l3i, i, i1) is None
        }),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 513,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] start <= j < final(steps).view().len() ==> mmap_1g_range_step(final(steps).view()[j], cpu_id),
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr) == old(krnl).thrd_mp.spec_index(thrd_ptr),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
        final(krnl).pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
        final(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        final(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.mapping_4k() == old_c.mapping_4k() && new_c.mapping_2m() == old_c.mapping_2m() && new_c.mapping_1g() == old_c.mapping_1g()
            &&& new_c.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
            &&& new_c.lower.hidden_l1_tables_in_locked_windows()
            &&& forall|p: PageMapPtr, i: L2Index| #![trigger new_c.lower.l2_owner(p, i)] new_c.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> new_c.lower.l2_owner(p, i) is None
            &&& forall|i4: L4Index| #![trigger new_c.spec_held_l4(i4)] #![trigger new_c.spec_resolve_mapping_l4(i4)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) ==> new_c.spec_held_l4(i4) == old_c.spec_held_l4(i4) && new_c.spec_resolve_mapping_l4(i4) == old_c.spec_resolve_mapping_l4(i4)
            &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_l3(i4, i3)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && (i4, i3) != (l4i, l3i) ==> new_c.spec_held_l3(i4, i3) == old_c.spec_held_l3(i4, i3)
            &&& new_c.spec_held_l3(l4i, l3i) is None
            &&& forall|i4: L4Index, i3: L3Index| #![trigger new_c.spec_held_1g_l3(i4, i3)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> new_c.spec_held_1g_l3(i4, i3) == old_c.spec_held_1g_l3(i4, i3)
            &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger new_c.spec_held_2m_l2(i4, i3, i2)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> new_c.spec_held_2m_l2(i4, i3, i2) == old_c.spec_held_2m_l2(i4, i3, i2)
            &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger new_c.spec_held_4k_l1(i4, i3, i2, i1)]
                old_c.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> new_c.spec_held_4k_l1(i4, i3, i2, i1) == old_c.spec_held_4k_l1(i4, i3, i2, i1)
        }),
{
    let ghost oc = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
    let l2_ptr = l3_entry.addr;
    let mut l2i = 0usize;
    while l2i < 512
        invariant
            oc == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
            l2_ptr == l3_entry.addr,
            0 <= start <= old(steps).view().len(),
            forall|j: int| #![trigger old(steps).view()[j]] start <= j < old(steps).view().len() ==> mmap_1g_range_step(old(steps).view()[j], cpu_id),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).cpu_id() == cpu_id,
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).pt_mp.dom().contains(pagetable),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap1g { range, mapped: 0, directory: false, hidden: true, flushed: true }),
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            oc.kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i),
            oc.spec_held_l3(l4i, l3i) == Some(*l3_entry),
            forall|i: L2Index| #![trigger oc.spec_held_2m_l2(l4i, l3i, i)] pei_valid(i) ==> oc.spec_held_2m_l2(l4i, l3i, i) is None,
            forall|i: L2Index, i1: L1Index| #![trigger oc.spec_held_4k_l1(l4i, l3i, i, i1)] pei_valid(i) && pei_valid(i1) ==> oc.spec_held_4k_l1(l4i, l3i, i, i1) is None,
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + l2i,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] start <= j < steps.view().len() ==> mmap_1g_range_step(steps.view()[j], cpu_id),
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.kernel_view_locking_state() is Acquire,
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            krnl.cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
            krnl.thrd_mp.dom().contains(thrd_ptr),
            krnl.thrd_mp.spec_index(thrd_ptr) == old(krnl).thrd_mp.spec_index(thrd_ptr),
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            krnl.pt_mp.spec_index(pagetable).view().cr3 == old(krnl).pt_mp.spec_index(pagetable).view().cr3,
            krnl.pt_mp.spec_index(pagetable).view().pcid == old(krnl).pt_mp.spec_index(pagetable).view().pcid,
            krnl.pt_mp.spec_index(pagetable).view().proc_ptr == prc_ptr,
            krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end == oc.kernel_l4_end(),
            krnl.pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::<CpuId>::empty(),
            ({
                let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                &&& c.mapping_4k() == oc.mapping_4k() && c.mapping_2m() == oc.mapping_2m() && c.mapping_1g() == oc.mapping_1g()
                &&& c.lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty()
                &&& c.lower.hidden_l1_tables_in_locked_windows()
                &&& forall|p: PageMapPtr, i: L2Index| #![trigger c.lower.l2_owner(p, i)] c.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> c.lower.l2_owner(p, i) is None
                &&& c.spec_resolve_mapping_l3(l4i, l3i) is None
                &&& forall|i4: L4Index| #![trigger c.spec_held_l4(i4)] #![trigger c.spec_resolve_mapping_l4(i4)]
                    oc.kernel_l4_end() <= i4 && pei_valid(i4) ==> c.spec_held_l4(i4) == oc.spec_held_l4(i4) && c.spec_resolve_mapping_l4(i4) == oc.spec_resolve_mapping_l4(i4)
                &&& forall|i4: L4Index, i3: L3Index| #![trigger c.spec_held_l3(i4, i3)]
                    oc.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> c.spec_held_l3(i4, i3) == oc.spec_held_l3(i4, i3)
                &&& forall|i4: L4Index, i3: L3Index| #![trigger c.spec_held_1g_l3(i4, i3)]
                    oc.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> c.spec_held_1g_l3(i4, i3) == oc.spec_held_1g_l3(i4, i3)
                &&& forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger c.spec_held_2m_l2(i4, i3, i2)]
                    oc.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> c.spec_held_2m_l2(i4, i3, i2) == oc.spec_held_2m_l2(i4, i3, i2)
                &&& forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger c.spec_held_4k_l1(i4, i3, i2, i1)]
                    oc.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1) ==> c.spec_held_4k_l1(i4, i3, i2, i1) == oc.spec_held_4k_l1(i4, i3, i2, i1)
                &&& forall|i: L2Index| #![trigger c.spec_held_l2(l4i, l3i, i)] #![trigger c.lower.l2_page(l2_ptr).entry_lock(i).l1()]
                    0 <= i < l2i ==> c.spec_held_l2(l4i, l3i, i) is None && c.lower.l2_page(l2_ptr).entry_lock(i).l1() is None
            }),
            l2i <= 512,
        decreases 512 - l2i,
    {
        proof {
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        }
        proof {
            let c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
            c.higher.wf_l4_at(l4i); c.l3_links_l2_wf_at(c.spec_held_l4(l4i)->0.addr, l3i);
        }
        let table = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm);
        let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable);
        let word = table.get_l2_entry_word(Tracked(lower), l4i, l3i, l2i, l3_entry);
        if word.perm.present && !word.perm.ps {
            proof { process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); }
            let ghost before = steps.view();
            let ret = mmap_1g_reclaim_table_page(krnl, pagetable, l4i, l3i, l2i, true, l2_ptr, word.addr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm);
            proof {
                let ghost mid = ret.1@;
                process_thread_wf_thread_at(mid.prc_mp, mid.thrd_mp, thrd_ptr); container_thread_wf_thread_at(mid.ctn_mp, mid.thrd_mp, thrd_ptr);
                krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
                mmap_1g_reclaim_range_steps_from_k(&*steps, before, start, &mid, &ret.2@, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, range);
            }
        }
        l2i = l2i + 1;
    }
    proof { process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); }
    let ghost before = steps.view();
    let ret = mmap_1g_reclaim_table_page(krnl, pagetable, l4i, l3i, 0, false, l2_ptr, l2_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm);
    proof {
        let ghost mid = ret.1@;
        process_thread_wf_thread_at(mid.prc_mp, mid.thrd_mp, thrd_ptr); container_thread_wf_thread_at(mid.ctn_mp, mid.thrd_mp, thrd_ptr);
        krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable);
        mmap_1g_reclaim_range_steps_from_k(&*steps, before, start, &mid, &ret.2@, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, range);
    }
}
} // verus!
