use vstd::prelude::*;
use crate::*;
use super::syscall_unmap_2m_spec::*;
use super::syscall_unmap_2m_trace::*;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::unmap_2m_present_in_window::clear_2m_mapping_present_in_window;
#[cfg(feature = "split-crates")]
use veriflat_map_4k::map_4k::unmap_2m_reclaim_in_window::reclaim_unmapped_2m_page_in_window;
#[cfg(feature = "split-crates")]
use veriflat_alloc_page::free_2m_page::refund_unmap_2m_quota;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::unmap_2m_present_in_window::clear_2m_mapping_present_in_window;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::map_4k::unmap_2m_reclaim_in_window::reclaim_unmapped_2m_page_in_window;
#[cfg(not(feature = "split-crates"))]
use crate::kernel::implementation::free_2m_page::refund_unmap_2m_quota;

verus! {
/// Unmap every page of `range`, each a present 2M leaf of the read-held page table `pagetable` whose window this thread holds
/// among the 2M windows of `cover`, the 4K range covering `range`: clear each leaf, flush the TLBs, then reclaim each page and
/// refund its quota. Inside the held windows only the range's leaves change.
pub(super) fn unmap_2m_range(
    krnl: &mut KernelK, range: &VaRange2M, cover: &VaRange4K, pagetable: RwLockPageTableRoot, thrd_ptr: RwLockThreadPtr, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_perm: Tracked<&LockPerm>, thread_perm: Tracked<&LockPerm>, pagetable_perm: Tracked<&LockPerm>,
    Tracked(window_perms): Tracked<&Map<WindowVa, LockPerm>>,
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
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range: *range, unmapped: 0, flushed: false }),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        range.wf(),
        range.len > 0,
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(range.view()[j])
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(range.view()[j]).present
            &&& old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(range.view()[j])
            &&& window_of(range.view()[j]).va == range.view()[j]
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(range.view()[j])), TypedLockMode::Write)
            &&& window_perms.dom().contains(window_of(range.view()[j]))
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])), spec_v2l2index(range.view()[j]))
                == (RwLockState::Write { thread_id: window_perms.index(window_of(range.view()[j])).thread_id(), lock_id: window_perms.index(window_of(range.view()[j])).lock_id() })
        },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None,
        old(krnl).prc_mp.spec_index(old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + range.len + 1 <= final(steps).view().len() <= old(steps).view().len() + range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 2,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> unmap_2m_range_step(final(steps).view()[j], cpu_id),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).thrd_mp.dom().contains(thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range: *range, unmapped: range.len, flushed: true }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_leaves_present(w) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_leaves_present(w)
            &&& pei_valid(spec_v2l2index(w.va))
                && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
        },
        forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> !whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(range.view()[j]),
{
    let ghost prc_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_proc;
    let ghost ctn_ptr = krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container;
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.thrd_mp.spec_index(thrd_ptr).inv() && !thread_is_dangling(krnl.thrd_mp.spec_index(thrd_ptr))) by { thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id); };
    let mut i = 0usize;
    while i < range.len
        invariant
            prc_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc,
            ctn_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
            steps.snapshot_k() == *krnl,
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.page_lock_map().dom().is_empty(),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            index_valid(NUM_CPUS, cpu_id),
            lctx.cpu_id() == cpu_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == lctx.thread_id(),
            cpu_perm.view().lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.thrd_mp.dom().contains(thrd_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            krnl.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
            pagetable_perm.view().state() is ReadLock,
            pagetable_perm.view().thread_id() == lctx.thread_id(),
            krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
            krnl.pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
            old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            range.wf(),
            range.len > 0,
            forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(range.view()[j])
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(range.view()[j]).present
                &&& old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(range.view()[j])
                &&& window_of(range.view()[j]).va == range.view()[j]
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(range.view()[j])), TypedLockMode::Write)
                &&& window_perms.dom().contains(window_of(range.view()[j]))
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])),
                        spec_v2l2index(range.view()[j]))
                    == (RwLockState::Write { thread_id: window_perms.index(window_of(range.view()[j])).thread_id(), lock_id: window_perms.index(window_of(range.view()[j])).lock_id() })
            },
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).inv(),
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            i <= range.len,
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread { syscall_progress: krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
            krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range: *range, unmapped: i, flushed: false }),
            steps.view().len() == old(steps).view().len() + i,
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus is None || whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(0usize, NUM_CPUS))
                &&& !range.view().contains(w.va) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                &&& !range.view().contains(w.va) && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                    ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
                &&& pei_valid(spec_v2l2index(w.va))
                    && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                    ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.l2_entry_hides_l1(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            },
            forall|w: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                    &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                        ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
                },
            forall|j: int| #![trigger range.view()[j]] i <= j < range.len ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(range.view()[j])
                && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(range.view()[j]) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(range.view()[j]),
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(range.view()[j]) && !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(range.view()[j]).present,
        decreases range.len - i,
    {
        let va = range.index(i);
        proof {
            process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
            assert(lctx.thread_lock_map().dom().subset_of(krnl.thrd_mp.dom())) by { krnl.thrd_mp.typed_lock_map_aligned_held_in_dom(lctx.thread_lock_map(), lctx.thread_id()); };
        }
        let ghost leaf_pre = *krnl;
        let ghost leaf_lctx = *lctx;
        let ghost leaf_before = steps.view();
        let leaf = clear_2m_mapping_present_in_window(krnl, pagetable, va, thrd_ptr, Ghost(*range), Ghost(i), Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm,
            Tracked(window_perms.tracked_borrow(window_of(va))));
        proof {
            assert(range.view().contains(va));
            unmap_2m_leaf_range_steps_from_k(&*steps, leaf_before, old(steps).view().len() as int, &leaf_pre, kernel_k_to_kernel_u(leaf.0@), &leaf_lctx, cpu_id, prc_ptr, thrd_ptr, pagetable,
                *range, i, va);
        }
        i = i + 1;
    }
    let ghost flush_before = steps.view();
    let ghost flush_entry = *krnl;
    let ghost flush_lctx = *lctx;
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
    }
    flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, thrd_ptr, false, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm, pagetable_perm);
    proof {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        unmap_2m_tlb_flush_range_steps_from_k(&*steps, flush_before, old(steps).view().len() as int, &flush_entry, &flush_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable, pcid, *range);
    }
    let ghost flushed_snap = steps.snapshot_k();
    let ghost flushed_pre = *krnl;
    let ghost flushed_lctx = *lctx;
    krnl.set_thread_syscall_progress(thrd_ptr, Ghost(Some(SyscallProgress::Unmap2m { range: *range, unmapped: range.len, flushed: true })), Tracked(&*lctx), thread_perm);
    proof {
        let ghost flushed_before = steps.view();
        let ghost flushed_k = *krnl;
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thrd_ptr);
        unmap_2m_flushed_range_steps_from_k(&*steps, flushed_before, old(steps).view().len() as int, &flushed_snap, &flushed_pre, &flushed_k, &flushed_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable,
            pcid, *range);
    }
    assert(krnl.thrd_mp.spec_index(thrd_ptr).inv()) by { thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); };
    assert(krnl.thrd_mp.spec_index(thrd_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH) by {
        container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr); container_perms_wf_at(krnl.ctn_mp, krnl.thrd_mp.spec_index(thrd_ptr).view().owning_container);
    };
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let mut i = 0usize;
    while i < range.len
        invariant
            prc_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc,
            ctn_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_2m_range_step(steps.view()[j], cpu_id),
            steps.snapshot_k() == *krnl,
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.page_lock_map().dom().is_empty(),
            lctx.scheduler_lock_map().dom().is_empty(),
            lctx.cpu_set_lock_map().dom().is_empty(),
            index_valid(NUM_CPUS, cpu_id),
            lctx.cpu_id() == cpu_id,
            typed_lock_map_contains_mode(lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
            cpu_perm.view().state() is WriteLock,
            cpu_perm.view().thread_id() == lctx.thread_id(),
            cpu_perm.view().lock_id() == krnl.cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
            krnl.cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
            old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (cr3, pcid),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            pcid != KERNEL_DEFAULT_PCID,
            krnl.thrd_mp.dom().contains(thrd_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            krnl.thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable,
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
            pagetable_perm.view().state() is ReadLock,
            pagetable_perm.view().thread_id() == lctx.thread_id(),
            krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
            krnl.pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
            old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
            range.wf(),
            range.len > 0,
            forall|j: int| #![trigger range.view()[j]] 0 <= j < range.len ==> {
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(range.view()[j])
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(range.view()[j]).present
                &&& old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_v2l4index(range.view()[j])
                &&& window_of(range.view()[j]).va == range.view()[j]
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(range.view()[j])), TypedLockMode::Write)
                &&& window_perms.dom().contains(window_of(range.view()[j]))
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(range.view()[j]), spec_v2l3index(range.view()[j])),
                        spec_v2l2index(range.view()[j]))
                    == (RwLockState::Write { thread_id: window_perms.index(window_of(range.view()[j])).thread_id(), lock_id: window_perms.index(window_of(range.view()[j])).lock_id() })
            },
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
            krnl.thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            krnl.thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            krnl.thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).inv(),
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            i <= range.len,
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_2M_MAJOR),
            old(steps).view().len() + range.len + 1 <= steps.view().len() <= old(steps).view().len() + range.len + NUM_CPUS + 1,
            krnl.thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                direct_free_quota_pending_2m: krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m, indirect_free_quota_pending_2m: krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m,
                syscall_progress: krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap2m { range: *range, unmapped: range.len, flushed: true }),
            direct == krnl.thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(d)] 0 <= d < krnl.thrd_mp.spec_index(thrd_ptr).view().container_depth
                ==> indirect[d] == krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().spec_index(d),
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).lock_state == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
                &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                &&& !range.view().contains(w.va) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                &&& !range.view().contains(w.va) && whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                    ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
                &&& pei_valid(spec_v2l2index(w.va))
                    && !whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_entry_hides_l1(whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                    ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).lower.l2_entry_hides_l1(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
            },
            forall|w: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                    &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                        ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
                },
            forall|j: int| #![trigger range.view()[j]] i <= j < range.len ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(range.view()[j])
                && !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(range.view()[j]).present,
            forall|j: int| #![trigger range.view()[j]] 0 <= j < i ==> !whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(range.view()[j]),
        decreases range.len - i,
    {
        let va = range.index(i);
        reclaim_unmapped_2m_page_in_window(krnl, pagetable, va, thrd_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm,
            Tracked(window_perms.tracked_borrow(window_of(va))));
        i = i + 1;
    }
    let ghost refund_before = steps.view();
    let ghost refund_progress = krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view();
    proof { process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); }
    refund_unmap_2m_quota(krnl, thrd_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
    proof {
        assert(krnl.thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view() =~= old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view()) by { thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); };
        unmap_2m_range_steps_from_refund(&*steps, refund_before, old(steps).view().len() as int, cpu_id, thrd_ptr, prc_ptr, ctn_ptr, refund_progress);
    }
}
}
