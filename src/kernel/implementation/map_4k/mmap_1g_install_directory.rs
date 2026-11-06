use vstd::prelude::*;
use crate::*;
use super::mmap_4k_build_structure::MissingPageTableLevel;
use super::mmap_4k_build_structure_spec::*;
#[cfg(verus_keep_ghost)]
use super::mmap_4k_create_entry_install_eof::*;
#[cfg(verus_keep_ghost)]
use super::mmap_1g_install_directory_trace::mmap_1g_directory_step_from_k;

verus! {
/// Installing the L3 directory page for the next 1G page records it in mmap progress and leaves other progress unchanged.
pub open spec fn mmap_1g_progress_after_directory(progress: Option<SyscallProgress>) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::Mmap1g { range, mapped, directory: _, hidden, flushed }) => Some(SyscallProgress::Mmap1g { range, mapped, directory: true, hidden, flushed }),
        _ => progress,
    }
}

/// A directory step starts under the three mmap locks, before the recorded range is fully mapped and before the L3 page of the next 1G page is installed, with quota for one directory page.
#[verifier::opaque]
pub open spec fn mmap_1g_directory_step_pre(old_u: KernelU, cpu_id: CpuId) -> bool {
    let thread = old_u.thread_map.spec_index(old_u.cpu_array[cpu_id as int].current_thread->Some_0);
    let progress = thread.syscall_progress->Some_0;
    &&& thread_pagetable_op_in_progress(old_u, cpu_id)
    &&& progress is Mmap1g
    &&& progress->Mmap1g_mapped < progress->Mmap1g_range.len
    &&& !progress->Mmap1g_directory
    &&& thread.quota_4k >= 1
}

/// An L3 directory page consumes one 4K quota of the running thread and records the installed directory in its progress; it creates no window and changes no mapping.
#[verifier::opaque]
pub open spec fn mmap_1g_directory_step(old_u: KernelU, new_u: KernelU, cpu_id: CpuId) -> bool {
    let thrd_ptr = old_u.cpu_array[cpu_id as int].current_thread->Some_0;
    let thread = old_u.thread_map.spec_index(thrd_ptr);
    new_u == (KernelU {
        thread_map: old_u.thread_map.insert(thrd_ptr, ThreadU { quota_4k: (thread.quota_4k - 1) as usize, syscall_progress: mmap_1g_progress_after_directory(thread.syscall_progress), ..thread }),
        ..old_u
    })
}

    /// Allocate one page and install it as the L3 directory page under the missing user root entry `l4i` of the running thread's table, under the table's big write lock, then end the krnl section. Every L3 entry of the new page is empty; the quota deduction and the progress record are
    /// visible through `ThreadU` at this boundary.
    pub fn install_one_mmap_1g_directory_page(
        krnl: &mut KernelK, alloc_ptr_4k: RwLockPageAllocatorPtr, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(steps).snapshot_k() == *old(krnl),
            index_valid(NUM_CPUS, cpu_id),
            old(lctx).cpu_id() == cpu_id,
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr),
            old(krnl).ctn_mp.dom().contains(ctn_ptr),
            old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
            old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
            !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost().exited,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr && old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is Some && old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0 is Mmap1g,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap1g_mapped < old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap1g_range.len,
            !old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0->Mmap1g_directory,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            KERNEL_MEM_END_L4INDEX <= l4i,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thrd_mp.spec_index(thrd_ptr)) >= 1,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i) is None,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i) is None,
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == old(steps).view().push(final(steps).view().last()),
            mmap_1g_directory_step_pre(final(steps).view().last().old_u, cpu_id),
            mmap_1g_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
            held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            final(krnl).ctn_mp.dom().contains(ctn_ptr),
            final(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(ctn_ptr).view_rodata(),
            final(krnl).prc_mp.dom().contains(prc_ptr),
            final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
            final(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
            !(final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(final(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie),
            final(krnl).thrd_mp.dom().contains(thrd_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == false,
            !thread_is_dangling(final(krnl).thrd_mp.spec_index(thrd_ptr)),
            thread_lock_perm.thread_id() == final(lctx).thread_id(),
            thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(steps).snapshot_k() == *final(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
            held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_threads_unchanged_except(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx), set![thrd_ptr]),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![pagetable_ptr]),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_clean(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k - 1,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().caller == old(krnl).thrd_mp.spec_index(thrd_ptr).view().caller,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().callee == old(krnl).thrd_mp.spec_index(thrd_ptr).view().callee,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_1g,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().endpoint_descriptors.view(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().state == old(krnl).thrd_mp.spec_index(thrd_ptr).view().state,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == mmap_1g_progress_after_directory(old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().blocking_endpoint_ptr == old(krnl).thrd_mp.spec_index(thrd_ptr).view().blocking_endpoint_ptr,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().ipc_payload == old(krnl).thrd_mp.spec_index(thrd_ptr).view().ipc_payload,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().error_code == old(krnl).thrd_mp.spec_index(thrd_ptr).view().error_code,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().trap_frame == old(krnl).thrd_mp.spec_index(thrd_ptr).view().trap_frame,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().upper_container_seq == old(krnl).thrd_mp.spec_index(thrd_ptr).view().upper_container_seq,
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                quota_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
                syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().cr3 == old(krnl).pt_mp.spec_index(pagetable_ptr).view().cr3,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().pcid == old(krnl).pt_mp.spec_index(pagetable_ptr).view().pcid,
            final(krnl).pt_mp.spec_index(pagetable_ptr).inv(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus == old(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i) is Some,
            forall|l4j: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4j)]
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4j)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4j && pei_valid(l4j) && l4j != l4i ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4j)
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4j)
                },
            forall|l4j: L4Index, l3j: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4j, l3j)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4j, l3j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4j, l3j),
            forall|l4j: L4Index, l3j: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4j, l3j)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4j, l3j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4j, l3j),
            forall|l4j: L4Index, l3j: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4j, l3j)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4j, l3j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4j, l3j),
            forall|l3j: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3j)]
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(l4i, l3j)]
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3j)]
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4i, l3j)]
                pei_valid(l3j) ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3j) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(l4i, l3j) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3j) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4i, l3j) is None
                },
    {
        let ghost entry_lctx = *lctx;
        proof { kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl); }
        let (pg_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, thrd_ptr, ctn_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(thread_lock_perm));
        proof {
            assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr)) by {
                old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
                pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            };
            assert(krnl.prc_mp.dom().contains(prc_ptr) && krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr
                && krnl.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr) by {
                process_thread_wf_thread_at(old(krnl).prc_mp, old(krnl).thrd_mp, thrd_ptr); process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr);
                process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
            };
            assert(!(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is Zombie)) by {
                process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
            };
        }
        install_one_mmap_1g_directory_page_link(krnl, Tracked(&mut *lctx), pg_ptr, thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr, l4i, Ghost(entry_lctx), Tracked(page_lock_perm),
            Tracked(thread_lock_perm), Tracked(pagetable_lock_perm));
        install_one_mmap_1g_directory_page_end_step(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), cpu_id, thrd_ptr, prc_ptr, pagetable_ptr, Tracked(thread_lock_perm));
        proof {
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k) && krnl.ctn_mp.dom().contains(ctn_ptr)) by {
                container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, ctn_ptr); container_thread_wf_thread_at(krnl.ctn_mp, krnl.thrd_mp, thrd_ptr);
            };
            assert(!(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(krnl.prc_mp.spec_index(prc_ptr).view().state.view() is Zombie)) by {
                process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr); process_emptied_threads_wf_at(krnl.prc_mp, krnl.thrd_mp, prc_ptr, thrd_ptr);
            };
            assert(krnl.pt_mp.spec_index(pagetable_ptr).inv() && whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()) by {
                pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            };
        }
    }

    /// Retype the staged page `pg_ptr` into an empty L3 page, link it under the missing user root entry `l4i` of `pagetable_ptr`, charge it to `thrd_ptr`, and release its page lock, ending the krnl section's mutations in Release. `entry_lctx` is the lock context before the page was
    /// staged.
    fn install_one_mmap_1g_directory_page_link(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pg_ptr: PagePtr, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr,
        pagetable_ptr: RwLockPageTableRoot, l4i: L4Index, Ghost(entry_lctx): Ghost<LocalContext>, Tracked(page_lock_perm): Tracked<LockPerm>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            page_ptr_valid(pg_ptr),
            typed_lock_maps_inserted(&entry_lctx, old(lctx), KernelObjId::Page(page_ptr2page_index(pg_ptr)), TypedHeldLock {
                lock_id: old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pg_ptr)), mode: TypedLockMode::Write }),
            !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(pg_ptr)),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() is Some && old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view()->Some_0 is Mmap1g,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k >= 1,
            old(krnl).prc_mp.dom().contains(prc_ptr),
            old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container == ctn_ptr,
            old(krnl).prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr,
            !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is TablesEmptied) && !(old(krnl).prc_mp.spec_index(prc_ptr).view().state.view() is Zombie),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: thrd_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().owning_container == ctn_ptr,
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pg_ptr), TypedLockMode::Write),
            page_lock_perm.state() is WriteLock,
            page_lock_perm.thread_id() == old(lctx).thread_id(),
            page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i) is None,
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4i) is None,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            nonwindow_typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
            final(lctx).pagetable_window_lock_map() == entry_lctx.pagetable_window_lock_map(),
            thread_lock_perm.lock_id() == final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            kernel_thread_quota_4k_changed(old(krnl), final(krnl), thrd_ptr, -1),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                quota_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
                syscall_progress: final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().remove(pg_ptr),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k - 1,
            final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().cr3 == old(krnl).pt_mp.spec_index(pagetable_ptr).view().cr3,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().pcid == old(krnl).pt_mp.spec_index(pagetable_ptr).view().pcid,
            final(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed(),
            final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
            final(krnl).pt_lower == old(krnl).pt_lower,
            final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable_ptr, final(krnl).pt_lower.view().spec_index(pagetable_ptr)),
            final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread(),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(pg_ptr)),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thrd_mp: final(krnl).thrd_mp, ..*old(krnl) }),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus == old(krnl).pt_mp.spec_index(pagetable_ptr).view().table_stale_cpus,
            whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4i) is Some,
            forall|l4j: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4j)]
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4j)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4j && pei_valid(l4j) && l4j != l4i ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l4(l4j)
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(l4j)
                },
            forall|l4j: L4Index, l3j: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4j, l3j)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4j, l3j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4j, l3j),
            forall|l4j: L4Index, l3j: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4j, l3j)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4j, l3j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4j, l3j),
            forall|l4j: L4Index, l3j: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4j, l3j)]
                whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4j && pei_valid(l4j) && pei_valid(l3j)
                    ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4j, l3j) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4j, l3j),
            forall|l3j: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3j)]
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(l4i, l3j)]
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3j)]
                #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4i, l3j)]
                pei_valid(l3j) ==> {
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3j) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(l4i, l3j) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_l3(l4i, l3j) is None
                    &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_held_1g_l3(l4i, l3j) is None
                },
    {
        let pg_idx = page_ptr2page_index(pg_ptr);
        let ghost staged_k = *krnl;
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.thrd_mp.perms_wf() && krnl.thrd_mp.spec_index(thrd_ptr).inv()) by {
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); thread_perms_wf_map(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr);
        };
        assert(index_valid(NUM_PAGES, pg_idx) && krnl.pg_arr.inv() && krnl.pg_arr.spec_index(pg_idx).view().is_init() && krnl.pg_arr.spec_index(pg_idx).view().inv()
            && krnl.pg_arr.spec_index(pg_idx).view().view().inv() && krnl.pg_arr.spec_index(pg_idx).view().view().addr == pg_ptr) by {
            page_ptr_valid_imply_page_index_valid(); page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, pg_idx);
        };
        assert(!whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).page_closure().contains(pg_ptr)) by {
            if whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).page_closure().contains(pg_ptr) {
                pagetable_pages_wf_closure_page_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable_ptr, pg_ptr);
            }
        };
        proof {
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
            pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        }
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
        let Tracked(page_perm) = {
            let page = krnl.pg_arr.borrow_mut_typed(pg_idx, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_lock_perm));
            let tracked_perm = take_perm_4k(page);
            page.state = PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_ptr, table_type: PT_TYPE } };
            tracked_perm
        };
        {
            let thread = krnl.thrd_mp.borrow_mut_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
            thread.temp_alloc_cache_4k = Ghost(thread.temp_alloc_cache_4k.view().remove(pg_ptr));
            thread.quota_4k = thread.quota_4k - 1;
        }
        let (page_map_ptr, Tracked(page_map_perm)) = page_perm_to_page_map(pg_ptr, Tracked(page_perm));
        pagetable_map_create_entry_l4(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow()), pagetable_ptr, (l4i, 0usize, 0usize, 0usize), page_map_ptr, Tracked(page_map_perm),
            Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
        proof {
            lctx.update_lock_id(KernelObjId::Page(pg_idx), staged_page_lock_id, krnl.pg_arr.lock_id_by_index(pg_idx));
            assert(krnl.pt_lower.view() =~= staged_k.pt_lower.view().insert(pagetable_ptr, krnl.pt_lower.view().spec_index(pagetable_ptr)));
            assert(install_staged_4k_page_table_page_eof_transition_framing(staged_k, *krnl, MissingPageTableLevel::L4, pg_ptr, thrd_ptr, pagetable_ptr)) by {
                reveal(install_staged_4k_page_table_page_eof_transition_framing);
            };
            install_staged_4k_page_table_page_eof(staged_k, *krnl, MissingPageTableLevel::L4, pg_ptr, thrd_ptr, prc_ptr, ctn_ptr, pagetable_ptr);
        }
        let ghost installed_page_lock_id = krnl.pg_arr.lock_id_by_index(pg_idx);
        krnl.wunlock_page(pg_idx, Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(nonwindow_typed_lock_maps_unchanged(&entry_lctx, lctx)) by {
                map_insert_overwrite_lemma(entry_lctx.page_lock_map(), pg_idx, TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write },
                    TypedHeldLock { lock_id: installed_page_lock_id, mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(entry_lctx.page_lock_map(), pg_idx, TypedHeldLock { lock_id: installed_page_lock_id, mode: TypedLockMode::Write });
            };
            assert(kernel_thread_quota_4k_changed(old(krnl), krnl, thrd_ptr, -1)) by { reveal(kernel_thread_quota_4k_changed); };
        }
    }

    /// Record the installed L3 page in the running thread's 1G mmap progress, then end the krnl section of one directory install at the step boundary and derive the 1G mmap directory step from the section's start snapshot.
    fn install_one_mmap_1g_directory_page_end_step(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr,
        prc_ptr: RwLockProcessPtr, pagetable_ptr: RwLockPageTableRoot, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == old(lctx).thread_id(),
            thread_lock_perm.lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
            old(lctx).kernel_view_locking_state() is Release,
            kernel_thread_quota_4k_changed(&old(steps).snapshot_k(), old(krnl), thrd_ptr, -1),
            index_valid(NUM_CPUS, cpu_id),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            {
                let pre = old(steps).snapshot_k();
                let progress = pre.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view();
                &&& pre.inv()
                &&& pre.thrd_mp.typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id())
                &&& pre.pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                &&& *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, pg_arr: old(krnl).pg_arr, thrd_mp: old(krnl).thrd_mp, ..pre })
                &&& old(krnl).thrd_mp.unchanged_except(&pre.thrd_mp, thrd_ptr)
                &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                    quota_4k: old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_4k, temp_alloc_cache_4k: old(krnl).thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k,
                    syscall_progress: old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress, ..pre.thrd_mp.spec_index(thrd_ptr).view()
                })
                &&& old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == pre.thrd_mp.spec_index(thrd_ptr).being_killed()
                &&& pre.prc_mp.dom().contains(prc_ptr) && pre.prc_mp.spec_index(prc_ptr).view_rodata().view().pagetable == pagetable_ptr
                &&& old(krnl).pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
                &&& old(krnl).pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr))
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k()
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m()
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g()
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr)
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(prc_ptr)
                &&& pre.thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr
                &&& progress is Some && progress->Some_0 is Mmap1g && progress->Some_0->Mmap1g_mapped < progress->Some_0->Mmap1g_range.len
                &&& !progress->Some_0->Mmap1g_directory
                &&& old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == progress
            },
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == old(steps).view().push(final(steps).view().last()),
            mmap_1g_directory_step_pre(final(steps).view().last().old_u, cpu_id),
            mmap_1g_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
            final(steps).snapshot_k() == *final(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            forall|cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)] old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            forall|ctn_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(ctn_ptr)]
                old(lctx).container_lock_map().dom().contains(ctn_ptr) ==> {
                    &&& final(krnl).ctn_mp.dom().contains(ctn_ptr)
                    &&& final(krnl).ctn_mp.lock_id_by_key(ctn_ptr) == old(krnl).ctn_mp.lock_id_by_key(ctn_ptr)
                    &&& final(krnl).ctn_mp.spec_index(ctn_ptr) == old(krnl).ctn_mp.spec_index(ctn_ptr)
                },
            forall|prc_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(prc_ptr)]
                old(lctx).process_lock_map().dom().contains(prc_ptr) ==> {
                    &&& final(krnl).prc_mp.dom().contains(prc_ptr)
                    &&& final(krnl).prc_mp.lock_id_by_key(prc_ptr) == old(krnl).prc_mp.lock_id_by_key(prc_ptr)
                    &&& final(krnl).prc_mp.spec_index(prc_ptr) == old(krnl).prc_mp.spec_index(prc_ptr)
                },
            forall|t: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(t)]
                old(lctx).thread_lock_map().dom().contains(t) ==> {
                    &&& final(krnl).thrd_mp.dom().contains(t)
                    &&& t != thrd_ptr ==> final(krnl).thrd_mp.spec_index(t) == old(krnl).thrd_mp.spec_index(t)
                },
            final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread {
                syscall_progress: Ghost(mmap_1g_progress_after_directory(old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view())), ..old(krnl).thrd_mp.spec_index(thrd_ptr).view()
            }),
            final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
            final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(krnl).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(krnl).pt_mp.lock_id_by_key(pagetable_ptr) == old(krnl).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr) == old(krnl).pt_mp.spec_index(pagetable_ptr)
                        &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
            {
                let thread = old(krnl).thrd_mp.spec_index(thrd_ptr).view();
                &&& final(krnl).ctn_mp.dom().contains(thread.owning_container)
                &&& final(krnl).ctn_mp.spec_index(thread.owning_container).view_rodata() == old(krnl).ctn_mp.spec_index(thread.owning_container).view_rodata()
                &&& !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)) ==> final(krnl).prc_mp.dom().contains(thread.owning_proc)
                &&& !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)) ==> final(krnl).prc_mp.spec_index(thread.owning_proc).view_rodata() == old(krnl).prc_mp.spec_index(thread.owning_proc).view_rodata()
            },
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
    {
        let ghost mid = *krnl;
        krnl.set_thread_syscall_progress(thrd_ptr, Ghost(mmap_1g_progress_after_directory(krnl.thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view())), Tracked(&*lctx),
            Tracked(thread_lock_perm));
        proof {
            let pre = steps.snapshot_k();
            let before = *krnl;
            let before_lctx = *lctx;
            assert(kernel_thread_quota_4k_changed(&pre, &before, thrd_ptr, -1)) by { reveal(kernel_thread_quota_4k_changed); };
            mid.thrd_mp.typed_lock_map_aligned_held_in_dom(before_lctx.thread_lock_map(), before_lctx.thread_id());
            krnl.kernel_step_boundary_thread_quota_4k_changed(&mut *lctx, &mut *steps, thrd_ptr, -1);
            mmap_1g_directory_step_from_k(&pre, &before, &before_lctx, cpu_id, thrd_ptr, prc_ptr, pagetable_ptr);
        }
    }
} // verus!
