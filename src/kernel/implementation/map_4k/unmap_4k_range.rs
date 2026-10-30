use vstd::prelude::*;
use crate::*;
use super::unmap_4k_spec::*;
use super::unmap_4k_trace::*;
use super::unmap_4k_present::clear_4k_mapping_present_in_window;
use super::unmap_4k_flush_all::flush_pagetable_tlbs;
use super::unmap_4k_reclaim_one::reclaim_unmapped_4k_page_in_window;

verus! {
/// First phase of `unmap_4k_range`: clear the present bit of each page of `range` in order, recording one step per page,
/// while every 2M window of the range stays held; the cleared leaves keep their entries otherwise.
fn clear_4k_range_present(
    krnl: &mut KernelK, range: &VaRange4K, pagetable: RwLockPageTableRoot, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, Ghost(checked_table): Ghost<PageTableC<PT_TYPE>>,
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
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
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
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        range.wf(),
        range.len > 0,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
        checked_table.wf_mapping_4k(),
        checked_table.higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher,
        forall|j: int| #![trigger checked_table.mapping_4k().dom().contains(range.view().spec_index(j))] 0 <= j < range.len ==> checked_table.mapping_4k().dom().contains(range.view().spec_index(j)),
        forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), range.view().spec_index(j)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && 0 <= j < range.len
                && spec_v2l4index(range.view().spec_index(j)) == spec_v2l4index(w.va) && spec_v2l3index(range.view().spec_index(j)) == spec_v2l3index(w.va) && spec_v2l2index(range.view().spec_index(j)) == spec_v2l2index(w.va)
            ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view().spec_index(j)) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(range.view().spec_index(j)).present,
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            ==> typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, w), TypedLockMode::Write),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None,
        forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
            let w = window_of(range.view().spec_index(j));
            &&& window_perms.dom().contains(w)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                == (SpinLockState::Some { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
        },
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
    ensures
        old(krnl).prc_mp.dom().contains(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc),
        !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable == pagetable,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> unmap_4k_range_step(final(steps).view()[j], cpu_id),
        final(steps).snapshot_k() == *final(krnl),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).page_lock_map().dom().is_empty(),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        final(lctx).scheduler_lock_map().dom().is_empty(),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).cpu_id() == cpu_id,
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_perm.view().state() is WriteLock,
        cpu_perm.view().thread_id() == final(lctx).thread_id(),
        cpu_perm.view().lock_id() == final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid,
        final(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == final(lctx).thread_id(),
        thread_perm.view().lock_id() == final(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
        final(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(final(lctx).thread_id(), pagetable_perm.view().lock_id()),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc,
        forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(range.view().spec_index(j))), TypedLockMode::Write)
            &&& spec_va2index(window_of(range.view().spec_index(j)).va) == (spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)), spec_v2l2index(range.view().spec_index(j)), 0usize)
        },
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).inv(),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: *range, unmapped: range.len, flushed: false }),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(steps).view().len() == old(steps).view().len() + range.len,
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None || pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(0usize, NUM_CPUS))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
        },
        forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), range.view().spec_index(j)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && 0 <= j < range.len
            && spec_v2l4index(range.view().spec_index(j)) == spec_v2l4index(w.va) && spec_v2l3index(range.view().spec_index(j)) == spec_v2l3index(w.va) && spec_v2l2index(range.view().spec_index(j)) == spec_v2l2index(w.va) ==> {
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view().spec_index(j))
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(range.view().spec_index(j))
                == (MapEntry { present: range.len <= j, ..pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(range.view().spec_index(j)) })
        },
        forall|w: WindowVa, v: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) && !range.view().contains(v) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    let ghost process_ptr = krnl.thr_mp.spec_index(thread_ptr).view().owning_proc;
    let ghost container_ptr = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.thr_mp.spec_index(thread_ptr).inv() && !thread_is_dangling(krnl.thr_mp.spec_index(thread_ptr))) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); };
    assert(krnl.prc_mp.dom().contains(process_ptr) && !krnl.prc_mp.spec_index(process_ptr).view().zombie && krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable
        && krnl.pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr) by { process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, thread_ptr); };
    proof { va_range_2m_windows_contains_window_of_first_n_pages(*range, range.len as int); }
    let start = range.start;
    let mut i = 0usize;
    while i < range.len
        invariant
            forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                let w = window_of(range.view().spec_index(j));
                &&& window_perms.dom().contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                    == (SpinLockState::Some { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
            },
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
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.page_lock_map().dom().is_empty(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
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
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
            pagetable_perm.view().state() is ReadLock,
            pagetable_perm.view().thread_id() == lctx.thread_id(),
            krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
            krnl.pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            old(krnl).pt_mp.spec_index(pagetable).view().proc_ptr == process_ptr,
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
            range.wf(),
            range.len > 0,
            start == range.start,
            checked_table.wf_mapping_4k(),
            checked_table.higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher,
            forall|j: int| #![trigger checked_table.mapping_4k().dom().contains(range.view().spec_index(j))] 0 <= j < range.len ==> checked_table.mapping_4k().dom().contains(range.view().spec_index(j)),
            forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                &&& va_range_2m_windows(*range).contains(window_of(range.view().spec_index(j)))
                &&& spec_va2index(window_of(range.view().spec_index(j)).va) == (spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)), spec_v2l2index(range.view().spec_index(j)), 0usize)
            },
            forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < i ==> typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(range.view().spec_index(j))), TypedLockMode::Write),
            forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
                va_range_2m_windows(*range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                ==> typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, w), TypedLockMode::Write),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            krnl.cpu_arr.spec_index(cpu_id).view().killer_info() == old(krnl).cpu_arr.spec_index(cpu_id).view().killer_info(),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).inv(),
            !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
            i <= range.len,
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: *range, unmapped: i, flushed: false }),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            steps.view().len() == old(steps).view().len() + i,
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus is None || pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus == Some(Set::range(0usize, NUM_CPUS))
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                    ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
            },
            forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), range.view().spec_index(j)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && 0 <= j < range.len
                && spec_v2l4index(range.view().spec_index(j)) == spec_v2l4index(w.va) && spec_v2l3index(range.view().spec_index(j)) == spec_v2l3index(w.va) && spec_v2l2index(range.view().spec_index(j)) == spec_v2l2index(w.va) ==> {
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view().spec_index(j))
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(range.view().spec_index(j)) == (MapEntry { present: i <= j, ..pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(range.view().spec_index(j)) })
            },
            forall|w: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) && !range.view().contains(v) ==> {
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                        ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
                },
        decreases range.len - i,
    {
        let va = range.index(i);
        proof {
            assert(va_4k_valid(va) && range.start <= va && spec_va_4k_valid(range.start) && spec_va_4k_valid(va)) by { range.va_range_lemma(); };
            assert(krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0) by { spec_v2l4index_monotonic(start, va); };
            assert(lctx.thread_lock_map().dom().subset_of(krnl.thr_mp.dom())) by { krnl.thr_mp.typed_lock_map_aligned_held_in_dom(lctx.thread_lock_map(), lctx.thread_id()); };
            assert(checked_table.mapping_4k().dom().contains(range.view().spec_index(i as int)));
            assert(checked_table.higher.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some) by {
                spec_va_4k_index_roundtrip_at(va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
                checked_table.wf_mapping_4k_at(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va));
            };
            assert(old(lctx).pagetable_window_lock_map().dom().contains((pagetable, window_of(va)))
                && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(window_of(va)).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).lock_state
                && window_perms.dom().contains(window_of(range.view().spec_index(i as int)))) by {
                spec_va_4k_index_roundtrip_at(window_of(va).va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize);
            };
        }
        let ghost leaf_pre = *krnl;
        let ghost leaf_lctx = *lctx;
        clear_4k_mapping_present_in_window(krnl, pagetable, va, Tracked(&mut *lctx), pagetable_perm, Tracked(window_perms.tracked_borrow(window_of(va))));
        krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Unmap4k { range: *range, unmapped: (i + 1) as usize, flushed: false })), Tracked(&*lctx), thread_perm);
        proof {
            assert(kernel_process_4k_mapping_changed(&steps.snapshot_k(), &*krnl, process_ptr, pagetable, va)) by { reveal(kernel_process_4k_mapping_changed); };
            let ghost leaf_before = steps.view();
            let ghost leaf_k = *krnl;
            krnl.kernel_step_boundary_process_4k_mapping_changed_windowed(&mut *lctx, &mut *steps, process_ptr, pagetable, va, process_ptr, pagetable, thread_ptr, thread_ptr);
            assert(range.view().contains(va)) by { range.va_range_lemma(); assert(range.view()[i as int] == va); };
            unmap_4k_leaf_range_steps_from_k(&*steps, leaf_before, old(steps).view().len() as int, &leaf_pre, &leaf_k, &leaf_lctx, cpu_id, process_ptr, thread_ptr, pagetable, *range, i, va);
        }
        i = i + 1;
    }
}

/// Unmap every page of `range` from the read-held page table `pagetable` while this thread holds every 2M window of the range
/// whose L3 entry links an L2 page: clear each leaf, flush the TLBs, then reclaim each page and refund its quota. Every page
/// was mapped in `checked_table`, the table as checked before the held windows were last carried over a step boundary, so
/// each page lies in a held window; inside the held windows only the range's leaves change.
pub fn unmap_4k_range(
    krnl: &mut KernelK, range: &VaRange4K, pagetable: RwLockPageTableRoot, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid, Ghost(checked_table): Ghost<PageTableC<PT_TYPE>>,
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
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
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
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        old(krnl).pt_mp.spec_index(pagetable).view().cr3 == cr3,
        old(krnl).pt_mp.spec_index(pagetable).view().pcid == Some(pcid),
        range.wf(),
        range.len > 0,
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
        checked_table.wf_mapping_4k(),
        checked_table.higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher,
        forall|j: int| #![trigger checked_table.mapping_4k().dom().contains(range.view().spec_index(j))] 0 <= j < range.len ==> checked_table.mapping_4k().dom().contains(range.view().spec_index(j)),
        forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), range.view().spec_index(j)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && 0 <= j < range.len
                && spec_v2l4index(range.view().spec_index(j)) == spec_v2l4index(w.va) && spec_v2l3index(range.view().spec_index(j)) == spec_v2l3index(w.va) && spec_v2l2index(range.view().spec_index(j)) == spec_v2l2index(w.va)
            ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view().spec_index(j)) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(range.view().spec_index(j)).present,
        forall|w: WindowVa| #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            ==> typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, w), TypedLockMode::Write),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None,
        forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
            let w = window_of(range.view().spec_index(j));
            &&& window_perms.dom().contains(w)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                == (SpinLockState::Some { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
        },
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view_rodata().view().pcid == pcid,
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() + range.len + 1 <= final(steps).view().len() <= old(steps).view().len() + range.len + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 2,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> unmap_4k_range_step(final(steps).view()[j], cpu_id),
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
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { syscall_progress: final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: *range, unmapped: range.len, flushed: true }),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_perm.view().lock_id()),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_view(w).stale_cpus is None
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_leaves_present(w) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).window_leaves_present(w)
        },
        forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(range.view().spec_index(j))), TypedLockMode::Write)
            &&& spec_va2index(window_of(range.view().spec_index(j)).va) == (spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)), spec_v2l2index(range.view().spec_index(j)), 0usize)
        },
        forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view().spec_index(j)),
        forall|j: int, v: VAddr|
            #![trigger range.view().spec_index(j), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            #![trigger range.view().spec_index(j), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
            0 <= j < range.len && spec_v2l4index(v) == spec_v2l4index(range.view().spec_index(j)) && spec_v2l3index(v) == spec_v2l3index(range.view().spec_index(j)) && spec_v2l2index(v) == spec_v2l2index(range.view().spec_index(j)) && !range.view().contains(v) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
            },
{
    let ghost process_ptr = krnl.thr_mp.spec_index(thread_ptr).view().owning_proc;
    let ghost container_ptr = krnl.thr_mp.spec_index(thread_ptr).view().owning_container;
    clear_4k_range_present(krnl, range, pagetable, thread_ptr, cpu_id, cr3, pcid, Ghost(checked_table), Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm, thread_perm, pagetable_perm,
        Tracked(window_perms));
    let ghost flush_before = steps.view();
    let ghost flush_entry = *krnl;
    let ghost flush_lctx = *lctx;
    flush_pagetable_tlbs(krnl, pagetable, cr3, pcid, cpu_id, thread_ptr, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_perm);
    proof {
        unmap_4k_tlb_flush_range_steps_from_k(&*steps, flush_before, old(steps).view().len() as int, &flush_entry, &flush_lctx, cpu_id, process_ptr, thread_ptr, container_ptr, pagetable, pcid, *range);
    }
    let ghost flushed_pre = *krnl;
    let ghost flushed_lctx = *lctx;
    krnl.set_thread_syscall_progress(thread_ptr, Ghost(Some(SyscallProgress::Unmap4k { range: *range, unmapped: range.len, flushed: true })), Tracked(&*lctx), thread_perm);
    proof {
        let ghost flushed_before = steps.view();
        let ghost flushed_k = *krnl;
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, thread_ptr);
        unmap_4k_flushed_range_steps_from_k(&*steps, flushed_before, old(steps).view().len() as int, &flushed_pre, &flushed_k, &flushed_lctx, cpu_id, process_ptr, thread_ptr, container_ptr, pagetable, pcid, *range);
    }
    assert(krnl.thr_mp.spec_index(thread_ptr).inv()) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
    assert(krnl.thr_mp.spec_index(thread_ptr).view().container_depth <= MAX_CONTAINER_TREE_DEPTH) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); container_perms_wf_at(krnl.ctn_mp, krnl.thr_mp.spec_index(thread_ptr).view().owning_container); };
    let mut indirect = [0usize; MAX_CONTAINER_TREE_DEPTH];
    let mut direct = 0usize;
    let start = range.start;
    let mut i = 0usize;
    while i < range.len
        invariant
            forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                let w = window_of(range.view().spec_index(j));
                &&& window_perms.dom().contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va))
                    == (SpinLockState::Some { thread_id: window_perms.index(w).thread_id(), lock_id: window_perms.index(w).lock_id() })
            },
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> unmap_4k_range_step(steps.view()[j], cpu_id),
            steps.snapshot_k() == *krnl,
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.page_lock_map().dom().is_empty(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
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
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            krnl.thr_mp.spec_index(thread_ptr).view().proc_pagetable_ptr == pagetable,
            krnl.pt_mp.dom().contains(pagetable),
            typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
            pagetable_perm.view().state() is ReadLock,
            pagetable_perm.view().thread_id() == lctx.thread_id(),
            krnl.pt_mp.spec_index(pagetable).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
            krnl.pt_mp.spec_index(pagetable).view() == old(krnl).pt_mp.spec_index(pagetable).view(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(range.start).0,
            range.wf(),
            range.len > 0,
            start == range.start,
            forall|j: int| #![trigger range.view().spec_index(j)] 0 <= j < range.len ==> {
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable, window_of(range.view().spec_index(j))), TypedLockMode::Write)
                &&& spec_va2index(window_of(range.view().spec_index(j)).va) == (spec_v2l4index(range.view().spec_index(j)), spec_v2l3index(range.view().spec_index(j)), spec_v2l2index(range.view().spec_index(j)), 0usize)
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
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            old(krnl).thr_mp.spec_index(thread_ptr).inv(),
            !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
            i <= range.len,
            old(steps).view().len() + range.len + 1 <= steps.view().len() <= old(steps).view().len() + range.len + NUM_CPUS + 1,
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k,
                syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view()
            }),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::Unmap4k { range: *range, unmapped: range.len, flushed: true }),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth
                ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) ==> {
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(w).lock_state
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(w).stale_cpus is None
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().dom().contains(w.va)
                    ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m().spec_index(w.va)
            },
            forall|w: WindowVa, j: int| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), range.view().spec_index(j)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && 0 <= j < range.len
                && spec_v2l4index(range.view().spec_index(j)) == spec_v2l4index(w.va) && spec_v2l3index(range.view().spec_index(j)) == spec_v2l3index(w.va) && spec_v2l2index(range.view().spec_index(j)) == spec_v2l2index(w.va) ==> {
                &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(range.view().spec_index(j)) == (i <= j)
                &&& i <= j ==> !pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(range.view().spec_index(j)).present
            },
            forall|w: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) && !range.view().contains(v) ==> {
                    &&& pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(v)
                        ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(v)
                },
        decreases range.len - i,
    {
        let va = range.index(i);
        proof {
            assert(va_4k_valid(va) && range.start <= va && spec_va_4k_valid(range.start) && spec_va_4k_valid(va)) by { range.va_range_lemma(); };
            assert(krnl.pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0) by { spec_v2l4index_monotonic(start, va); };
            assert(old(lctx).pagetable_window_lock_map().dom().contains((pagetable, window_of(va)))
                && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).window_view(window_of(va)).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_view(window_of(va)).lock_state
                && window_perms.dom().contains(window_of(range.view().spec_index(i as int)))) by {
                spec_va_4k_index_roundtrip_at(window_of(va).va, spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize);
            };
        }
        reclaim_unmapped_4k_page_in_window(krnl, pagetable, va, thread_ptr, cpu_id, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm, thread_perm,
            Tracked(window_perms.tracked_borrow(window_of(va))));
        i = i + 1;
    }
    let ghost refund_before = steps.view();
    let ghost refund_progress = krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view();
    refund_unmap_4k_quota(krnl, thread_ptr, &mut indirect, &mut direct, Tracked(&mut *lctx), Tracked(&mut *steps), thread_perm);
    proof {
        assert(krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() =~= old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
        unmap_4k_range_steps_from_refund(&*steps, refund_before, old(steps).view().len() as int, cpu_id, thread_ptr, process_ptr, container_ptr, refund_progress);
    }
}
}
