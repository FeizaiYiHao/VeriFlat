use vstd::prelude::*;
use crate::*;
use super::syscall_iommu_map_4k_spec::*;
use super::iommu_map_4k_leaf_step::iommu_map_4k_map_one_page;
use super::iommu_map_4k_exit::iommu_map_4k_exit;

verus! {
/// Map page `i` of `va_range` at page `i` of `iova_range` for every `i`, installing each missing IOMMU directory level first,
/// then clear progress, release the windows and every IOMMU-map lock, and record the exit step.
pub(super) fn iommu_map_4k_map_range_and_exit(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, va_range: &VaRange4K, iova_range: &VaRange4K,
    thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, iommu_table_ptr: RwLockPageTableRoot,
    Tracked(cpu_lock_perm): Tracked<LockPerm>, Tracked(process_lock_perm): Tracked<LockPerm>, Tracked(thread_lock_perm): Tracked<LockPerm>, Tracked(pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(iommu_table_lock_perm): Tracked<LockPerm>, Tracked(window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        old(steps).view().len() == 1,
        iommu_map_4k_enter_step_pre(old(steps).view()[0].old_u, cpu_id, *va_range, *iova_range),
        iommu_map_4k_enter_step(old(steps).view()[0].old_u, old(steps).view()[0].new_u, cpu_id, *va_range, *iova_range),
        index_valid(NUM_CPUS, cpu_id) && cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), iommu_table_ptr, TypedLockMode::Write),
        !thread_is_dangling(old(krnl).thr_mp.spec_index(thread_ptr)),
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            &&& va_4k_valid(va_range.view()[j])
            &&& old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va_range.view()[j])))
        },
        forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < iova_range.len ==> va_4k_valid(iova_range.view()[j]),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc == process_ptr,
        old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container == container_ptr,
        !old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().quota_4k >= 3 * va_range.len,
        old(krnl).thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IommuMap4k { va_range: *va_range, iova_range: *iova_range, mapped: 0, directory: Mmap4kDirectory::None }),
        old(krnl).prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr,
        old(krnl).prc_mp.spec_index(process_ptr).view().iommu_table == Some(iommu_table_ptr),
        va_range.wf() && iova_range.wf() && va_range.len > 0 && iova_range.len == va_range.len,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va_range.start),
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(va_range.view()[j])
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k()[va_range.view()[j]].present
        },
        forall|j: int| #![trigger iova_range.view()[j]] 0 <= j < iova_range.len ==> !old(krnl).it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova_range.view()[j]),
        old(krnl).it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
        old(lctx).cpu_lock_map().dom() == set![cpu_id],
        old(lctx).process_lock_map().dom() == set![process_ptr],
        old(lctx).thread_lock_map().dom() == set![thread_ptr],
        old(lctx).pagetable_lock_map().dom() == set![pagetable_ptr],
        old(lctx).iommu_table_lock_map().dom() == set![iommu_table_ptr],
        old(lctx).page_lock_map().dom().is_empty() && old(lctx).container_lock_map().dom().is_empty() && old(lctx).endpoint_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty() && old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty() && old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty() && old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k) && old(lctx).holds_no_allocator_locks(PageSize::SZ2m) && old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        !(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Off),
        !old(krnl).thr_mp.spec_index(thread_ptr).view_ghost().exited,
        !(old(krnl).thr_mp.spec_index(thread_ptr).view().state is IPC_TRANSIT) && !(old(krnl).thr_mp.spec_index(thread_ptr).view().state is KILLED),
        forall|held_thread: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(held_thread)] old(lctx).thread_lock_map().dom().contains(held_thread)
            ==> old(krnl).thr_mp.spec_index(held_thread).being_killed() || !(old(krnl).thr_mp.spec_index(held_thread).view().state is SCHEDULED),
        !old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().kernel_call_perm() is None,
        !old(krnl).prc_mp.spec_index(process_ptr).being_killed(),
        old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Running || old(krnl).prc_mp.spec_index(process_ptr).view().state.view() is Zombie,
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view()
            == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        cpu_lock_perm.state() is WriteLock && cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        process_lock_perm.state() is WriteLock && process_lock_perm.thread_id() == old(lctx).thread_id(),
        process_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(process_ptr).locking_thread()->Write_lock_id,
        thread_lock_perm.state() is WriteLock && thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        pagetable_lock_perm.state() is ReadLock && pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        iommu_table_lock_perm.state() is WriteLock && iommu_table_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_lock_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == pagetable_ptr && window_perms.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*va_range).contains(w)]
            va_range_2m_windows(*va_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
            ==> window_perms.dom().contains(w),
        forall|w: WindowVa| #![trigger window_perms.dom().contains(w)]
            window_perms.dom().contains(w) ==> {
                &&& va_range_2m_windows(*va_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
                &&& window_perms.index(w).state() is WriteLock
                &&& window_perms.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &window_perms.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
    ensures
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).no_locks_held(),
        final(krnl).all_objects_unlocked(final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view()[0] == old(steps).view()[0],
        iommu_map_4k_syscall_trace(final(steps).view(), cpu_id, *va_range, *iova_range),
        va_range.len + 2 <= final(steps).view().len() <= 4 * va_range.len + 2,
{
    let range = va_range.len;
    let mut i: usize = 0;
    proof {
        krnl.prc_mp.typed_lock_map_aligned_write_at(lctx.process_lock_map(), lctx.thread_id(), process_ptr); krnl.it_mp.typed_lock_map_aligned_write_at(lctx.iommu_table_lock_map(), lctx.thread_id(), iommu_table_ptr);
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
    }
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    while i < range
        invariant
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            steps.snapshot_k() == *krnl,
            0 <= i <= range,
            i + 1 <= steps.view().len() <= 4 * i + 1,
            steps.view()[0] == old(steps).view()[0],
            forall|j: int| #![trigger steps.view()[j]] 0 < j < steps.view().len() ==> iommu_map_4k_range_step(steps.view()[j], cpu_id),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            krnl.cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.prc_mp.dom().contains(process_ptr),
            krnl.prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), krnl.pt_mp, krnl.pt_lower.view(), old(lctx)),
            krnl.thr_mp.dom().contains(thread_ptr),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread {
                quota_4k: krnl.thr_mp.spec_index(thread_ptr).view().quota_4k, temp_alloc_cache_4k: krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_cache_4k,
                syscall_progress: krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(thread_ptr).view()
            }),
            krnl.thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
            !krnl.thr_mp.spec_index(thread_ptr).being_killed(),
            krnl.thr_mp.spec_index(thread_ptr).view().quota_4k >= 3 * (range - i),
            krnl.thr_mp.spec_index(thread_ptr).view().temp_alloc_clean(),
            krnl.thr_mp.spec_index(thread_ptr).view().syscall_progress.view()
                == Some(SyscallProgress::IommuMap4k { va_range: *va_range, iova_range: *iova_range, mapped: i, directory: Mmap4kDirectory::None }),
            thread_lock_perm.lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            iommu_table_lock_perm.lock_id() == krnl.it_mp.spec_index(iommu_table_ptr).locking_thread()->Write_lock_id,
            krnl.it_mp.dom().contains(iommu_table_ptr),
            krnl.it_mp.spec_index(iommu_table_ptr).view().proc_ptr == old(krnl).it_mp.spec_index(iommu_table_ptr).view().proc_ptr,
            krnl.it_mp.spec_index(iommu_table_ptr).view().leaves_present(),
            forall|j: int| #![trigger iova_range.view()[j]] i <= j < range ==> !krnl.it_mp.spec_index(iommu_table_ptr).view().mapping_4k().dom().contains(iova_range.view()[j]),
        decreases range - i,
    {
        proof { assert(krnl.cpu_op.view().view()[cpu_id as int] is InStep) by { cpu_op_wf_at(krnl.cpu_op.view().view(), krnl.cpu_arr, cpu_id); }; }
        iommu_map_4k_map_one_page(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va_range, iova_range, i, thread_ptr, process_ptr, container_ptr, pagetable_ptr, iommu_table_ptr,
            Ghost(*old(krnl)), Ghost(*old(lctx)), Tracked(&pagetable_lock_perm), Tracked(&thread_lock_perm), Tracked(&iommu_table_lock_perm));
        i = i + 1;
    }
    iommu_map_4k_exit(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, va_range, iova_range, thread_ptr, process_ptr, pagetable_ptr, iommu_table_ptr, Ghost(*old(krnl)),
        Ghost(*old(lctx)), Tracked(cpu_lock_perm), Tracked(process_lock_perm), Tracked(thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(iommu_table_lock_perm), Tracked(window_perms));
}
} // verus!
