use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_new_process_spec::{new_process_publish_step, new_process_publish_step_pre};
#[cfg(verus_keep_ghost)]
use super::syscall_new_process_trace::new_process_publish_step_from_u;

verus! {
/// Records the sharing progress on the caller thread and ends the publish step that added `child_ptr` and released its parent.
pub(super) fn end_new_process_publish_step(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId,
    container_ptr: RwLockContainerPtr, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr, source_pagetable_ptr: RwLockPageTableRoot, target_pagetable_ptr: RwLockPageTableRoot,
    iommu_table: Option<RwLockPageTableRoot>, source_range: &VaRange4K, pcid: Pcid, Tracked(current_thread_lock_perm): Tracked<&LockPerm>,
    Ghost(regs): Ghost<Registers>, Ghost(endpoint_index): Ghost<Option<EndpointIdx>>,
)
    requires
        index_valid(NUM_CPUS, cpu_id),
        new_process_publish_step_pre(kernel_k_to_kernel_u(old(steps).snapshot_k()), cpu_id),
        old(steps).snapshot_k().inv(),
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, prc_mp: old(krnl).prc_mp, thr_mp: old(krnl).thr_mp, ctn_mp: old(krnl).ctn_mp,
            pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, it_mp: old(krnl).it_mp, pcid_allc_mp: old(krnl).pcid_allc_mp, ..old(steps).snapshot_k() }),
        old(steps).snapshot_k().cpu_arr.spec_index(cpu_id).value.view().view().current_thread == Some(current_thread_ptr),
        old(steps).snapshot_k().prc_mp.dom().contains(parent_ptr),
        !old(steps).snapshot_k().prc_mp.dom().contains(child_ptr),
        old(krnl).prc_mp.dom() == old(steps).snapshot_k().prc_mp.dom().insert(child_ptr),
        forall|p: RwLockProcessPtr| #![trigger old(krnl).prc_mp.spec_index(p)] old(steps).snapshot_k().prc_mp.dom().contains(p) ==> {
            &&& old(krnl).prc_mp.spec_index(p).view_rodata() == old(steps).snapshot_k().prc_mp.spec_index(p).view_rodata()
            &&& old(krnl).prc_mp.spec_index(p).view_ghost().uppertree_seq == old(steps).snapshot_k().prc_mp.spec_index(p).view_ghost().uppertree_seq
            &&& old(krnl).prc_mp.spec_index(p).view_ghost().owned_pci_functions == old(steps).snapshot_k().prc_mp.spec_index(p).view_ghost().owned_pci_functions
            &&& old(krnl).prc_mp.spec_index(p).view_ghost().subtree_set.view() == if old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr).contains(p) {
                old(steps).snapshot_k().prc_mp.spec_index(p).view_ghost().subtree_set.view().insert(child_ptr)
            } else { old(steps).snapshot_k().prc_mp.spec_index(p).view_ghost().subtree_set.view() }
            &&& old(krnl).prc_mp.spec_index(p).view() == (Process { children: old(krnl).prc_mp.spec_index(p).view().children, ..old(steps).snapshot_k().prc_mp.spec_index(p).view() })
            &&& old(krnl).prc_mp.spec_index(p).view().children.view() == if p == parent_ptr { old(steps).snapshot_k().prc_mp.spec_index(p).view().children.view().push(child_ptr) } else { old(steps).snapshot_k().prc_mp.spec_index(p).view().children.view() }
            &&& old(krnl).prc_mp.spec_index(p).being_killed() == old(steps).snapshot_k().prc_mp.spec_index(p).being_killed()
            &&& if p == parent_ptr { old(krnl).prc_mp.spec_index(p).locking_thread() is None } else { old(krnl).prc_mp.spec_index(p).locking_thread() == old(steps).snapshot_k().prc_mp.spec_index(p).locking_thread() }
        },
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), child_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(child_ptr).being_killed(),
        !old(krnl).prc_mp.spec_index(child_ptr).view().zombie,
        old(krnl).prc_mp.spec_index(child_ptr).view().pagetable == target_pagetable_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view().iommu_table == iommu_table,
        old(krnl).prc_mp.spec_index(child_ptr).view_ghost().owned_pci_functions.view().is_empty(),
        old(krnl).prc_mp.spec_index(child_ptr).view().quota_4k == 0,
        old(krnl).prc_mp.spec_index(child_ptr).view().quota_2m == 0,
        old(krnl).prc_mp.spec_index(child_ptr).view().quota_1g == 0,
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().parent == Some(parent_ptr),
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(child_ptr).view_rodata().view().depth == old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).view_rodata().view().depth + 1,
        old(krnl).prc_mp.spec_index(child_ptr).view().children.view() == Seq::<RwLockProcessPtr>::empty(),
        old(krnl).prc_mp.spec_index(child_ptr).view().owned_threads.view() == Seq::<RwLockThreadPtr>::empty(),
        old(krnl).prc_mp.spec_index(child_ptr).view_ghost().uppertree_seq.view() == old(steps).snapshot_k().prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr),
        old(krnl).prc_mp.spec_index(child_ptr).view_ghost().subtree_set.view().is_empty(),
        old(steps).snapshot_k().thr_mp.dom().contains(current_thread_ptr),
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).view().owning_proc == parent_ptr,
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).view().owning_container == container_ptr,
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::NewProcess(NewProcessProgress { range: *source_range, regs, endpoint_index, with_iommu: iommu_table is Some, child: None })),
        old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).view().quota_4k >= if iommu_table is Some { 5usize } else { 3usize },
        old(krnl).thr_mp.unchanged_except(&old(steps).snapshot_k().thr_mp, current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::NewProcess(NewProcessProgress { range: *source_range, regs, endpoint_index, with_iommu: iommu_table is Some, child: None })),
        kernel_thread_quota_4k_changed(&old(steps).snapshot_k(), old(krnl), current_thread_ptr, if iommu_table is Some { -5 } else { -3 }),
        old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread() == old(steps).snapshot_k().thr_mp.spec_index(current_thread_ptr).locking_thread(),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(steps).snapshot_k().ctn_mp.dom().contains(container_ptr),
        old(krnl).ctn_mp.unchanged_except(&old(steps).snapshot_k().ctn_mp, container_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).view_rodata(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost { owned_processes: old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes, ..old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).view_ghost() }),
        old(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).locking_thread(),
        old(krnl).ctn_mp.spec_index(container_ptr).control() == old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).control(),
        old(krnl).ctn_mp.spec_index(container_ptr).view() == old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).view(),
        old(krnl).ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().insert(child_ptr),
        old(steps).snapshot_k().ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        old(krnl).pcid_allc_mp.unchanged_except(&old(steps).snapshot_k().pcid_allc_mp, pcid_allocator_ptr),
        PcidAllocator::free_pcids(old(steps).snapshot_k().pcid_allc_mp.spec_index(pcid_allocator_ptr).view().ref_counters.view()).contains(pcid),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().alloc_ensures(&old(steps).snapshot_k().pcid_allc_mp.spec_index(pcid_allocator_ptr).view(), child_ptr, pcid),
        old(krnl).pt_mp.dom() == old(steps).snapshot_k().pt_mp.dom().insert(target_pagetable_ptr),
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)] old(steps).snapshot_k().pt_mp.dom().contains(p)
            ==> old(krnl).pt_mp.spec_index(p) == old(steps).snapshot_k().pt_mp.spec_index(p) && old(krnl).pt_lower.view().spec_index(p) == old(steps).snapshot_k().pt_lower.view().spec_index(p),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable_ptr, TypedLockMode::Write),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr).is_empty(),
        old(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable_ptr, TypedLockMode::Read),
        iommu_table is None ==> old(krnl).it_mp == old(steps).snapshot_k().it_mp,
        iommu_table matches Some(t) ==> {
            &&& old(krnl).it_mp.dom() == old(steps).snapshot_k().it_mp.dom().insert(t)
            &&& forall|p: RwLockPageTableRoot| #![trigger old(krnl).it_mp.spec_index(p)] old(steps).snapshot_k().it_mp.dom().contains(p) ==> old(krnl).it_mp.spec_index(p) == old(steps).snapshot_k().it_mp.spec_index(p)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), t, TypedLockMode::Write)
            &&& old(krnl).it_mp.spec_index(t).view().is_empty()
        },
    ensures
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        final(steps).view() == old(steps).view().push(final(steps).view().last()),
        new_process_publish_step_pre(final(steps).view().last().old_u, cpu_id),
        new_process_publish_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        forall|c: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(c)] old(lctx).cpu_lock_map().dom().contains(c) ==> final(krnl).cpu_arr.spec_index(c).view() == old(krnl).cpu_arr.spec_index(c).view(),
        containers_rodata_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        final(krnl).prc_mp.dom().contains(child_ptr),
        final(krnl).prc_mp.spec_index(child_ptr) == old(krnl).prc_mp.spec_index(child_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view() == (Thread {
            syscall_progress: Ghost(Some(SyscallProgress::Share4k {
                source_range: *source_range, target_range: *source_range, shared: 0,
                origin: Share4kOrigin::NewProcess(NewProcessProgress { range: *source_range, regs, endpoint_index, with_iommu: iommu_table is Some, child: Some(child_ptr) }),
            })),
            ..old(krnl).thr_mp.spec_index(current_thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(current_thread_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).pt_mp.dom().contains(source_pagetable_ptr),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        final(krnl).pt_mp.dom().contains(target_pagetable_ptr),
        final(krnl).pt_mp.spec_index(target_pagetable_ptr) == old(krnl).pt_mp.spec_index(target_pagetable_ptr),
        held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable_ptr) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable_ptr),
        iommu_table matches Some(t) ==> final(krnl).it_mp.dom().contains(t) && final(krnl).it_mp.spec_index(t) == old(krnl).it_mp.spec_index(t),
{
    let ghost sharing = Some(SyscallProgress::Share4k {
        source_range: *source_range, target_range: *source_range, shared: 0,
        origin: Share4kOrigin::NewProcess(NewProcessProgress { range: *source_range, regs, endpoint_index, with_iommu: iommu_table is Some, child: Some(child_ptr) }),
    });
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(sharing), Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        let ghost published_k = *krnl;
        let ghost published_lctx = *lctx;
        assert(kernel_process_added(&steps.snapshot_k(), &*krnl, child_ptr)) by { reveal(kernel_process_added); };
        krnl.kernel_step_boundary_process_added(&mut *lctx, &mut *steps, child_ptr, current_thread_ptr);
        assert(new_process_publish_step_pre(steps.view().last().old_u, cpu_id) && new_process_publish_step(steps.view().last().old_u, steps.view().last().new_u, cpu_id)) by {
            reveal(kernel_thread_quota_4k_changed);
            kernel_process_published_and_parent_unlocked_implies_u_step(&old(steps).snapshot_k(), &published_k, &published_lctx, parent_ptr, child_ptr, current_thread_ptr,
                container_ptr, target_pagetable_ptr, iommu_table, pcid_allocator_ptr, pcid, sharing);
            new_process_publish_step_from_u(kernel_k_to_kernel_u(old(steps).snapshot_k()), kernel_k_to_kernel_u(published_k), cpu_id, parent_ptr, child_ptr, current_thread_ptr,
                container_ptr, *source_range, regs, endpoint_index, iommu_table is Some);
        };
    }
}
} // verus!
