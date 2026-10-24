use vstd::prelude::*;
use crate::*;
use super::mmap_4k_create_entry_install::install_staged_4k_page_table_page;
use super::mmap_4k_build_structure_spec::*;
#[cfg(verus_keep_ghost)]
use super::mmap_4k_build_structure_trace::mmap_4k_directory_step_from_k;
#[cfg(verus_keep_ghost)]
use super::share_mapping_4k_trace::share_4k_directory_step_from_k;

verus! {
    /// Allocate and install one missing directory page, then end the krnl
    /// section. Directory topology is absent from `PageTableU`, while the
    /// quota deduction is visible through `ThreadU` at this boundary.
    ///
    /// L4 and L3 need the table's big write lock (`write_held`); an L2 page is installed under either big-lock mode in a 2M window
    /// this thread already holds. A new L2 page starts with its windows `lo..=hi` held by this thread and returns their lock perms.
    pub fn install_one_mmap_4k_directory_page(
        krnl: &mut KernelK, level: MissingPageTableLevel, alloc_ptr_4k: RwLockPageAllocatorPtr, quota_thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), lo: L2Index,
        hi: L2Index, write_held: bool, transfer_source: Option<RwLockContainerPtr>, Ghost(progress_thread): Ghost<RwLockThreadPtr>, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>,
        Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
    ) -> (ret: Tracked<Map<L2Index, LockPerm>>)
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            index_valid(NUM_CPUS, cpu_id),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            old(krnl).ctn_mp.dom().contains(container_ptr),
            old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).thr_mp.dom().contains(quota_thread_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            !thread_is_dangling(old(krnl).thr_mp.spec_index(quota_thread_ptr)),
            transfer_source is None ==> old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == container_ptr,
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& source == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container
                &&& source != container_ptr
                &&& old(krnl).ctn_mp.dom().contains(source)
                &&& old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(source)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), source, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write)
                &&& !old(krnl).ctn_mp.spec_index(source).being_killed()
                &&& !old(krnl).ctn_mp.spec_index(container_ptr).being_killed()
                &&& transfer_source_lock_perm is Some
                &&& transfer_source_lock_perm->Some_0.state() is WriteLock
                &&& transfer_source_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_source_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(source).locking_thread()->Write_lock_id
                &&& transfer_target_lock_perm is Some
                &&& transfer_target_lock_perm->Some_0.state() is WriteLock
                &&& transfer_target_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_target_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id
            },
            ((old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr)
                || (typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write) && !old(krnl).prc_mp.spec_index(process_ptr).view().zombie)),
            quota_thread_lock_perm.state() is WriteLock,
            quota_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            write_held ==> pagetable_lock_perm.state() is WriteLock,
            write_held ==> pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            !write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            !write_held ==> pagetable_lock_perm.state() is ReadLock,
            !write_held ==> old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            !write_held ==> transfer_source is None,
            !(level is L2) ==> write_held,
            KERNEL_MEM_END_L4INDEX <= indices.0,
            pei_valid(lo) && pei_valid(hi) && lo <= hi,
            level is L2 ==> old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(quota_thread_ptr)) >= 1,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            match level {
                MissingPageTableLevel::L4 => pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((indices.0, indices.1, indices.2, 0))),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            old(steps).snapshot_k() == *old(krnl) && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread)
                && typed_lock_map_contains_mode(old(lctx).thread_lock_map(), progress_thread, TypedLockMode::Write)
                && old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() is Some
                && old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0 is Share4k
                && old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_shared < old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_source_range.len
                && share_4k_objects_k(*old(krnl), cpu_id).target == process_ptr && old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == process_ptr
                && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == quota_thread_ptr && share_4k_objects_k(*old(krnl), cpu_id).target_container == container_ptr
                && share_4k_objects_k(*old(krnl), cpu_id).transfer_source == transfer_source
                && typed_lock_map_contains_mode(old(lctx).thread_lock_map(), share_4k_objects_k(*old(krnl), cpu_id).source_thread, TypedLockMode::Write)
                && (old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> old(krnl).thr_mp.spec_index(peer).view().state is IPC_TRANSIT && old(krnl).thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread)
                && (progress_thread == quota_thread_ptr || old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is None) ==> {
                &&& final(steps).view() == old(steps).view().push(final(steps).view().last())
                &&& share_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id)
                &&& share_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id)
                &&& share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id)
                &&& final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() == old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()
                &&& final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> final(krnl).thr_mp.spec_index(peer).view().state is IPC_TRANSIT && final(krnl).thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread
                &&& progress_thread == quota_thread_ptr || final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is None
            },
            held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
            final(krnl).prc_mp.dom().contains(process_ptr),
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            final(krnl).thr_mp.dom().contains(quota_thread_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            !thread_is_dangling(final(krnl).thr_mp.spec_index(quota_thread_ptr)),
            mmap_4k_quota_thread_container_compatible(final(krnl), final(lctx), quota_thread_ptr, container_ptr),
            ((final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr)
                || (typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write) && !final(krnl).prc_mp.spec_index(process_ptr).view().zombie)),
            quota_thread_lock_perm.thread_id() == final(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
            write_held ==> pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            !write_held ==> final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(final(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
            !(level is L3) ==> final(lctx).pagetable_window_lock_map() == old(lctx).pagetable_window_lock_map(),
            !(level is L3) ==> ret.view() == Map::<L2Index, LockPerm>::empty(),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    || (level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    && !(level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
                level is L3 && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, w), mode: TypedLockMode::Write }),
            forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (level is L3 && lo <= i <= hi),
            forall|i: L2Index| #![trigger ret.view().index(i)] level is L3 && lo <= i <= hi ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1)).lock_perm_match(i, &ret.view().index(i))
                &&& ret.view().index(i).state() is WriteLock
                &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
            },
            held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
            transfer_source is None ==> held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                let old_source_pages = old(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
                let new_source_pages = final(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
                &&& final(krnl).ctn_mp.dom().contains(source)
                &&& final(krnl).ctn_mp.spec_index(source).is_init() == old(krnl).ctn_mp.spec_index(source).is_init()
                &&& final(krnl).ctn_mp.spec_index(source).view_rodata() == old(krnl).ctn_mp.spec_index(source).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(source).view_ghost() == old(krnl).ctn_mp.spec_index(source).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(source).locking_thread() == old(krnl).ctn_mp.spec_index(source).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(source).being_killed() == old(krnl).ctn_mp.spec_index(source).being_killed()
                &&& final(krnl).ctn_mp.spec_index(source).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(source).view().owned_pages, ..old(krnl).ctn_mp.spec_index(source).view() })
                &&& final(krnl).ctn_mp.dom().contains(container_ptr)
                &&& final(krnl).ctn_mp.spec_index(container_ptr).is_init() == old(krnl).ctn_mp.spec_index(container_ptr).is_init()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(container_ptr).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(container_ptr).being_killed()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(container_ptr).view() })
                &&& new_source_pages.subset_of(old_source_pages)
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages.view().union(old_source_pages.difference(new_source_pages))
            },
            held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
            held_threads_unchanged_except(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx), set![quota_thread_ptr]),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![pagetable_ptr]),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().caller == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().caller,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().callee == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().callee,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().endpoint_descriptors.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().state == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().state,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view(), level),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            final(krnl).pt_mp.spec_index(pagetable_ptr).inv(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked),
            write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            !write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(level is L3 && l4i == indices.0 && l3i == indices.1)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                write_held && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i)
                    && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))]
                write_held && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))
                        == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i)),
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))]
                !write_held && old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) ==> {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).l2_page == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).l2_page
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).lock_state == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).lock_state
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().dom().contains(w.va)
                        ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m().spec_index(w.va)
                },
            forall|w: WindowVa, v: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)]
                !write_held && old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va)
                    && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(v)
                        ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(v)
                },
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().dom().contains((p, w)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && final(lctx).pagetable_window_lock_map().dom().contains((p, w)) && old(lctx).pagetable_lock_map().dom().contains(p) && p != pagetable_ptr ==> {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).window_view(w) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).window_view(w)
                    &&& forall|v: VAddr|
                        #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)]
                        #![trigger pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)]
                        spec_v2l4index(v) == spec_v2l4index(w.va) && spec_v2l3index(v) == spec_v2l3index(w.va) && spec_v2l2index(v) == spec_v2l2index(w.va) ==> {
                            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)
                            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().dom().contains(v)
                                ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_4k().spec_index(v) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_4k().spec_index(v)
                        }
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().dom().contains(w.va)
                        ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p).mapping_2m().spec_index(w.va) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p).mapping_2m().spec_index(w.va)
                },
            match level {
                MissingPageTableLevel::L4 => {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 => pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
            old(steps).snapshot_k() == *old(krnl) && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some
                && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k
                && (old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill ==> level is L4 || level is L3)
                && (!(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill)
                    ==> mmap_4k_directory_rank(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level)))
                && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr)
                && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(quota_thread_ptr)
                && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped < old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range.len
                && transfer_source is None ==> {
                    &&& final(steps).view() == old(steps).view().push(final(steps).view().last())
                    &&& mmap_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id)
                    &&& mmap_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id)
                },
    {
        let ghost share_guard = old(steps).snapshot_k() == *old(krnl) && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread)
            && typed_lock_map_contains_mode(old(lctx).thread_lock_map(), progress_thread, TypedLockMode::Write)
            && old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view() is Some
            && old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0 is Share4k
            && old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_shared < old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_source_range.len
            && share_4k_objects_k(*old(krnl), cpu_id).target == process_ptr && old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == process_ptr
            && share_4k_objects_k(*old(krnl), cpu_id).quota_thread == quota_thread_ptr && share_4k_objects_k(*old(krnl), cpu_id).target_container == container_ptr
            && share_4k_objects_k(*old(krnl), cpu_id).transfer_source == transfer_source
            && typed_lock_map_contains_mode(old(lctx).thread_lock_map(), share_4k_objects_k(*old(krnl), cpu_id).source_thread, TypedLockMode::Write)
            && (old(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                ==> old(krnl).thr_mp.spec_index(peer).view().state is IPC_TRANSIT && old(krnl).thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread)
            && (progress_thread == quota_thread_ptr || old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is None);
        let ghost mmap_guard = old(steps).snapshot_k() == *old(krnl) && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some
            && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k
            && (old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill ==> level is L4 || level is L3)
            && (!(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_phase is Fill)
                ==> mmap_4k_directory_rank(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level)))
            && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr)
            && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(quota_thread_ptr)
            && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_mapped < old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_range.len
            && transfer_source is None;
        let ghost window_va = WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) };
        let ghost entry_lctx = *lctx;
        let alloc_container_ptr = match transfer_source { Some(source) => source, None => container_ptr };
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, quota_thread_ptr, alloc_container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm));
        let ghost share_lctx = *lctx;
        proof {
            if share_guard {
                assert(share_4k_objects_k(*krnl, cpu_id) == share_4k_objects_k(*old(krnl), cpu_id) && krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(share_4k_objects_k); };
                assert(krnl.thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> krnl.thr_mp.spec_index(peer).view().state is IPC_TRANSIT && krnl.thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread) by { reveal(share_4k_objects_k); };
                assert(!krnl.prc_mp.spec_index(process_ptr).view().zombie && krnl.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr) by {
                    process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, quota_thread_ptr); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr);
                };
            }
        }
        proof {
            assert(write_held ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr)) by {
                if write_held {
                    old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable_ptr);
                    pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                }
            };
            assert(krnl.prc_mp.dom().contains(process_ptr) && krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
                && krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr) by {
                if !typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) {
                    process_thread_wf_at(old(krnl).prc_mp, old(krnl).thr_mp, quota_thread_ptr); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, quota_thread_ptr);
                }
                process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, process_ptr);
            };
            if !write_held {
                spec_va_4k_index_roundtrip_at(window_va.va, indices.0, indices.1, indices.2, 0usize);
                assert(old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_va)));
                assert(old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr));
            }
        }
        let windows = install_one_mmap_4k_directory_page_link(krnl, Tracked(&mut *lctx), level, page_ptr, quota_thread_ptr, process_ptr, container_ptr, pagetable_ptr, indices, lo, hi,
            write_held, transfer_source, Ghost(entry_lctx), Tracked(page_lock_perm), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(transfer_source_lock_perm),
            Tracked(transfer_target_lock_perm));
        let ghost directory_lctx = *lctx;
        install_one_mmap_4k_directory_page_end_step(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), level, cpu_id, quota_thread_ptr, process_ptr, container_ptr, pagetable_ptr,
            write_held, transfer_source, page_ptr, Ghost(progress_thread), Ghost(share_lctx), Ghost(mmap_guard), Ghost(share_guard));
        proof {
            assert(krnl.ctn_mp.dom().contains(container_ptr)) by { if transfer_source is None { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, quota_thread_ptr); } };
            assert(krnl.prc_mp.dom().contains(process_ptr) && ((krnl.thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && krnl.thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr)
                || (typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write) && !krnl.prc_mp.spec_index(process_ptr).view().zombie))) by { process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, quota_thread_ptr); };
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, container_ptr); };
            if !write_held {
                spec_va_4k_index_roundtrip_at(window_va.va, indices.0, indices.1, indices.2, 0usize);
                assert(directory_lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, window_va)));
                assert(directory_lctx.pagetable_lock_map().dom().contains(pagetable_ptr));
            }
            assert(krnl.pt_mp.spec_index(pagetable_ptr).inv() && pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).wf()) by {
                pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            };
        }
        windows
    }

    /// Move the staged page to `container_ptr`, publish it as the missing directory page, and release its page lock, ending the
    /// krnl section's mutations in Release.
    fn install_one_mmap_4k_directory_page_link(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, level: MissingPageTableLevel, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), lo: L2Index, hi: L2Index, write_held: bool,
        transfer_source: Option<RwLockContainerPtr>, Ghost(entry_lctx): Ghost<LocalContext>, Tracked(page_lock_perm): Tracked<LockPerm>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>, Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
    ) -> (ret: Tracked<Map<L2Index, LockPerm>>)
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_inserted(&entry_lctx, old(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)), TypedHeldLock {
                lock_id: old(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
            !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(page_ptr)),
            page_ptr_valid(page_ptr),
            old(krnl).thr_mp.dom().contains(quota_thread_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= 1,
            mmap_4k_quota_thread_container_compatible(old(krnl), old(lctx), quota_thread_ptr, container_ptr),
            old(krnl).prc_mp.dom().contains(process_ptr),
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            old(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= indices.0,
            pei_valid(indices.0) && pei_valid(indices.1) && pei_valid(indices.2),
            KERNEL_MEM_END_L4INDEX <= indices.0,
            pei_valid(lo) && pei_valid(hi) && lo <= hi,
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((indices.0, indices.1, indices.2, 0))),
            !(level is L2) ==> write_held,
            level is L2 ==> old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            old(lctx).pcid_needflush_lock_map().dom().is_empty(),
            old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
            old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
            old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
            forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thread_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == (match transfer_source { Some(source) => source, None => container_ptr }),
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
            page_lock_perm.state() is WriteLock,
            page_lock_perm.thread_id() == old(lctx).thread_id(),
            page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            quota_thread_lock_perm.state() is WriteLock,
            quota_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            write_held ==> pagetable_lock_perm.state() is WriteLock,
            write_held ==> pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            !write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            !write_held ==> pagetable_lock_perm.state() is ReadLock,
            !write_held ==> old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& source != container_ptr
                &&& old(krnl).ctn_mp.dom().contains(source) && old(krnl).ctn_mp.dom().contains(container_ptr)
                &&& old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(source)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), source, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write)
                &&& !old(krnl).ctn_mp.spec_index(source).being_killed() && !old(krnl).ctn_mp.spec_index(container_ptr).being_killed()
                &&& transfer_source_lock_perm is Some && transfer_source_lock_perm->Some_0.state() is WriteLock
                &&& transfer_source_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_source_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(source).locking_thread()->Write_lock_id
                &&& transfer_target_lock_perm is Some && transfer_target_lock_perm->Some_0.state() is WriteLock
                &&& transfer_target_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_target_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id
            },
            match level {
                MissingPageTableLevel::L4 => pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(krnl).inv(),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            nonwindow_typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
            !(level is L3) ==> final(lctx).pagetable_window_lock_map() == entry_lctx.pagetable_window_lock_map(),
            !(level is L3) ==> ret.view() == Map::<L2Index, LockPerm>::empty(),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (entry_lctx.pagetable_window_lock_map().dom().contains((p, w))
                    || (level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                entry_lctx.pagetable_window_lock_map().dom().contains((p, w))
                    && !(level is L3 && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == entry_lctx.pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
                level is L3 && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, w), mode: TypedLockMode::Write }),
            forall|i: L2Index| #![trigger ret.view().dom().contains(i)] ret.view().dom().contains(i) == (level is L3 && lo <= i <= hi),
            forall|i: L2Index| #![trigger ret.view().index(i)] level is L3 && lo <= i <= hi ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(indices.0, indices.1))
                    .lock_perm_match(i, &ret.view().index(i))
                &&& ret.view().index(i).state() is WriteLock
                &&& ret.view().index(i).thread_id() == final(lctx).thread_id()
            },
            quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed(),
            kernel_thread_quota_4k_changed(old(krnl), final(krnl), quota_thread_ptr, -1),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view() == (Thread {
                quota_4k: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k, temp_alloc_cache_4k: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k,
                syscall_progress: final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress, ..old(krnl).thr_mp.spec_index(quota_thread_ptr).view()
            }),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view(), level),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().remove(page_ptr),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 1,
            final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, quota_thread_ptr),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
            final(krnl).pt_lower.view() == old(krnl).pt_lower.view().insert(pagetable_ptr, final(krnl).pt_lower.view().spec_index(pagetable_ptr)),
            final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread(),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
            *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, pg_arr: final(krnl).pg_arr, thr_mp: final(krnl).thr_mp, ctn_mp: final(krnl).ctn_mp, ..*old(krnl) }),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            level is L2 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).higher,
            level is L2 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(level is L3 && l4i == indices.0 && l3i == indices.1)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            forall|l4i: L4Index, l3i: L3Index|
                #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))
                        == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i)),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 => pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
            transfer_source is None ==> final(krnl).ctn_mp == old(krnl).ctn_mp,
            transfer_source matches Some(source) ==> {
                &&& old(krnl).ctn_mp.spec_index(source).view().owned_pages.view().contains(page_ptr)
                &&& final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom()
                &&& final(krnl).ctn_mp.spec_index(source).is_init() == old(krnl).ctn_mp.spec_index(source).is_init()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).is_init() == old(krnl).ctn_mp.spec_index(container_ptr).is_init()
                &&& final(krnl).ctn_mp.spec_index(source).view().owned_pages.view().subset_of(old(krnl).ctn_mp.spec_index(source).view().owned_pages.view())
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages.view()
                    .union(old(krnl).ctn_mp.spec_index(source).view().owned_pages.view().difference(final(krnl).ctn_mp.spec_index(source).view().owned_pages.view()))
                &&& forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)] old(krnl).ctn_mp.dom().contains(c) ==> {
                    &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                    &&& final(krnl).ctn_mp.spec_index(c).view_ghost() == old(krnl).ctn_mp.spec_index(c).view_ghost()
                    &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                    &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
                    &&& final(krnl).ctn_mp.spec_index(c).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(c).view().owned_pages, ..old(krnl).ctn_mp.spec_index(c).view() })
                    &&& final(krnl).ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { old(krnl).ctn_mp.spec_index(c).view().owned_pages.view().remove(page_ptr) }
                        else if c == container_ptr { old(krnl).ctn_mp.spec_index(c).view().owned_pages.view().insert(page_ptr) } else { old(krnl).ctn_mp.spec_index(c).view().owned_pages.view() }
                }
            },
    {
        install_one_mmap_4k_directory_page_transfer_if_source(krnl, Tracked(&mut *lctx), page_ptr, quota_thread_ptr, container_ptr, transfer_source, Tracked(&page_lock_perm),
            Tracked(transfer_source_lock_perm), Tracked(transfer_target_lock_perm));
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr));
        let windows = install_staged_4k_page_table_page(krnl, level, page_ptr, quota_thread_ptr, process_ptr, container_ptr, pagetable_ptr, indices, lo, hi, write_held, Tracked(&mut *lctx),
            Tracked(&page_lock_perm), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm));
        let ghost installed_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr));
        krnl.wunlock_page(page_ptr2page_index(page_ptr), Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(nonwindow_typed_lock_maps_unchanged(&entry_lctx, lctx)) by {
                map_insert_overwrite_lemma(entry_lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedHeldLock { lock_id: staged_page_lock_id, mode: TypedLockMode::Write },
                    TypedHeldLock { lock_id: installed_page_lock_id, mode: TypedLockMode::Write });
                map_insert_remove_absent_lemma(entry_lctx.page_lock_map(), page_ptr2page_index(page_ptr), TypedHeldLock { lock_id: installed_page_lock_id, mode: TypedLockMode::Write });
            };
            assert(kernel_thread_quota_4k_changed(old(krnl), krnl, quota_thread_ptr, -1)) by { reveal(kernel_thread_quota_4k_changed); };
        }
        windows
    }

    /// End the krnl section of one directory install at the step boundary and derive the running syscall's directory step
    /// from the section's start snapshot.
    fn install_one_mmap_4k_directory_page_end_step(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, level: MissingPageTableLevel, cpu_id: CpuId,
        quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot, write_held: bool,
        transfer_source: Option<RwLockContainerPtr>, page_ptr: PagePtr, Ghost(progress_thread): Ghost<RwLockThreadPtr>, Ghost(share_lctx): Ghost<LocalContext>,
        Ghost(mmap_guard): Ghost<bool>, Ghost(share_guard): Ghost<bool>,
    )
        requires
            old(krnl).inv(),
            old(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            kernel_thread_quota_4k_changed(&old(steps).snapshot_k(), old(krnl), quota_thread_ptr, -1),
            index_valid(NUM_CPUS, cpu_id),
            write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            mmap_guard || share_guard ==> {
                let pre = old(steps).snapshot_k();
                &&& pre.inv()
                &&& pre.thr_mp.typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id())
                &&& pre.pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                &&& typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write)
                &&& !write_held ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read)
                &&& transfer_source is None ==> {
                    &&& *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, pg_arr: old(krnl).pg_arr, thr_mp: old(krnl).thr_mp, ..pre })
                    &&& old(krnl).thr_mp.unchanged_except(&pre.thr_mp, quota_thread_ptr)
                    &&& old(krnl).thr_mp.spec_index(quota_thread_ptr).view() == (Thread {
                        quota_4k: old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k, temp_alloc_cache_4k: old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k,
                        syscall_progress: old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress, ..pre.thr_mp.spec_index(quota_thread_ptr).view()
                    })
                    &&& old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == pre.thr_mp.spec_index(quota_thread_ptr).being_killed()
                    &&& pre.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr
                    &&& old(krnl).pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
                    &&& old(krnl).pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr))
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k()
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m()
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g()
                }
            },
            mmap_guard ==> {
                let pre = old(steps).snapshot_k();
                let progress = pre.thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view();
                &&& transfer_source is None
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(quota_thread_ptr)
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr)
                &&& pre.thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr
                &&& progress is Some && progress->Some_0 is Mmap4k && progress->Some_0->Mmap4k_mapped < progress->Some_0->Mmap4k_range.len
                &&& progress->Some_0->Mmap4k_phase is Fill ==> level is L4 || level is L3
                &&& !(progress->Some_0->Mmap4k_phase is Fill) ==> mmap_4k_directory_rank(progress->Some_0->Mmap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level))
                &&& old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == mmap_4k_progress_after_directory(progress, level)
            },
            share_guard ==> {
                let pre = old(steps).snapshot_k();
                let objects = share_4k_objects_k(pre, cpu_id);
                let progress = pre.thr_mp.spec_index(progress_thread).view().syscall_progress.view();
                &&& typed_lock_maps_aligned(&pre, &share_lctx)
                &&& typed_lock_map_contains_mode(share_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write)
                &&& pre.cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(progress_thread)
                &&& pre.prc_mp.dom().contains(process_ptr) && pre.thr_mp.dom().contains(progress_thread)
                &&& typed_lock_map_contains_mode(share_lctx.thread_lock_map(), progress_thread, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), progress_thread, TypedLockMode::Write)
                &&& progress is Some && progress->Some_0 is Share4k && progress->Some_0->Share4k_shared < progress->Some_0->Share4k_source_range.len
                &&& progress->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> pre.thr_mp.spec_index(peer).view().state is IPC_TRANSIT && pre.thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread
                &&& objects.target == process_ptr && objects.quota_thread == quota_thread_ptr
                &&& objects.target_container == container_ptr && objects.transfer_source == transfer_source
                &&& pre.thr_mp.dom().contains(objects.source_thread)
                &&& typed_lock_map_contains_mode(share_lctx.thread_lock_map(), objects.source_thread, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).thread_lock_map(), objects.source_thread, TypedLockMode::Write)
                &&& pre.thr_mp.dom().contains(quota_thread_ptr)
                &&& typed_lock_map_contains_mode(share_lctx.thread_lock_map(), quota_thread_ptr, TypedLockMode::Write)
                &&& pre.ctn_mp.dom().contains(container_ptr)
                &&& pre.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr
                &&& !pre.prc_mp.spec_index(process_ptr).view().zombie && pre.prc_mp.spec_index(process_ptr).view().pagetable == pagetable_ptr
                &&& typed_lock_map_contains_mode(share_lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read)
                    || typed_lock_map_contains_mode(share_lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write)
                &&& old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress == pre.thr_mp.spec_index(quota_thread_ptr).view().syscall_progress
                &&& transfer_source matches Some(source) ==> {
                    &&& pre.ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(source)
                    &&& typed_lock_map_contains_mode(share_lctx.container_lock_map(), source, TypedLockMode::Write)
                    &&& typed_lock_map_contains_mode(share_lctx.container_lock_map(), container_ptr, TypedLockMode::Write)
                    &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write)
                    &&& old(krnl).thr_mp.typed_lock_map_aligned(old(lctx).thread_lock_map(), old(lctx).thread_id())
                    &&& *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, ctn_mp: old(krnl).ctn_mp, thr_mp: old(krnl).thr_mp, pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..pre })
                    &&& source != container_ptr
                    &&& pre.ctn_mp.dom().contains(source)
                    &&& pre.ctn_mp.spec_index(source).view().owned_pages.view().contains(page_ptr)
                    &&& old(krnl).ctn_mp.dom() == pre.ctn_mp.dom()
                    &&& forall|c: RwLockContainerPtr| #![trigger old(krnl).ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) ==> {
                        &&& old(krnl).ctn_mp.spec_index(c).view_rodata() == pre.ctn_mp.spec_index(c).view_rodata()
                        &&& old(krnl).ctn_mp.spec_index(c).view_ghost() == pre.ctn_mp.spec_index(c).view_ghost()
                        &&& old(krnl).ctn_mp.spec_index(c).locking_thread() == pre.ctn_mp.spec_index(c).locking_thread()
                        &&& old(krnl).ctn_mp.spec_index(c).being_killed() == pre.ctn_mp.spec_index(c).being_killed()
                        &&& old(krnl).ctn_mp.spec_index(c).view() == (Container { owned_pages: old(krnl).ctn_mp.spec_index(c).view().owned_pages, ..pre.ctn_mp.spec_index(c).view() })
                        &&& old(krnl).ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { pre.ctn_mp.spec_index(c).view().owned_pages.view().remove(page_ptr) }
                            else if c == container_ptr { pre.ctn_mp.spec_index(c).view().owned_pages.view().insert(page_ptr) } else { pre.ctn_mp.spec_index(c).view().owned_pages.view() }
                    }
                    &&& old(krnl).thr_mp.unchanged_except(&pre.thr_mp, quota_thread_ptr)
                    &&& old(krnl).pt_mp.unchanged_except(&pre.pt_mp, pagetable_ptr)
                    &&& old(krnl).pt_lower.view() == pre.pt_lower.view().insert(pagetable_ptr, old(krnl).pt_lower.view().spec_index(pagetable_ptr))
                    &&& pre.pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                    &&& old(krnl).pt_mp.typed_lock_map_aligned(old(lctx).pagetable_lock_map(), old(lctx).thread_id())
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write)
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_4k()
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_2m()
                    &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(pre.pt_mp, pre.pt_lower.view(), pagetable_ptr).mapping_1g()
                }
            },
        ensures
            forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
            final(steps).view() == old(steps).view().push(final(steps).view().last()),
            mmap_guard ==> mmap_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id) && mmap_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id),
            share_guard ==> {
                let progress = final(krnl).thr_mp.spec_index(progress_thread).view().syscall_progress.view();
                &&& share_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id)
                &&& share_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, cpu_id)
                &&& share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(old(steps).snapshot_k(), cpu_id)
                &&& progress == old(steps).snapshot_k().thr_mp.spec_index(progress_thread).view().syscall_progress.view()
                &&& final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == old(steps).snapshot_k().thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()
                &&& progress->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> final(krnl).thr_mp.spec_index(peer).view().state is IPC_TRANSIT && final(krnl).thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread
            },
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            final(lctx).thread_id() == old(lctx).thread_id(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            forall|cpu_id: CpuId|
                #![trigger old(lctx).cpu_lock_map().dom().contains(cpu_id)]
                old(lctx).cpu_lock_map().dom().contains(cpu_id) ==> final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
            forall|container_ptr: RwLockContainerPtr|
                #![trigger old(lctx).container_lock_map().dom().contains(container_ptr)]
                old(lctx).container_lock_map().dom().contains(container_ptr) ==> {
                    &&& final(krnl).ctn_mp.dom().contains(container_ptr)
                    &&& final(krnl).ctn_mp.lock_id_by_key(container_ptr) == old(krnl).ctn_mp.lock_id_by_key(container_ptr)
                    &&& final(krnl).ctn_mp.spec_index(container_ptr) == old(krnl).ctn_mp.spec_index(container_ptr)
                },
            forall|process_ptr: RwLockProcessPtr|
                #![trigger old(lctx).process_lock_map().dom().contains(process_ptr)]
                old(lctx).process_lock_map().dom().contains(process_ptr) ==> {
                    &&& final(krnl).prc_mp.dom().contains(process_ptr)
                    &&& final(krnl).prc_mp.lock_id_by_key(process_ptr) == old(krnl).prc_mp.lock_id_by_key(process_ptr)
                    &&& final(krnl).prc_mp.spec_index(process_ptr) == old(krnl).prc_mp.spec_index(process_ptr)
                },
            forall|thread_ptr: RwLockThreadPtr|
                #![trigger old(lctx).thread_lock_map().dom().contains(thread_ptr)]
                old(lctx).thread_lock_map().dom().contains(thread_ptr) ==> {
                    &&& final(krnl).thr_mp.dom().contains(thread_ptr)
                    &&& final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr)
                    &&& final(krnl).thr_mp.spec_index(thread_ptr) == old(krnl).thr_mp.spec_index(thread_ptr)
                },
            forall|pagetable_ptr: RwLockPageTableRoot|
                #![trigger old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr)]
                old(lctx).pagetable_lock_map().dom().contains(pagetable_ptr) ==> {
                    &&& final(krnl).pt_mp.dom().contains(pagetable_ptr)
                    &&& final(krnl).pt_mp.lock_id_by_key(pagetable_ptr) == old(krnl).pt_mp.lock_id_by_key(pagetable_ptr)
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write) ==> {
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr) == old(krnl).pt_mp.spec_index(pagetable_ptr)
                        &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr)
                    }
                    &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read) ==> {
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view()
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).rlocked_by_thread(old(lctx).thread_id())
                        &&& final(krnl).pt_mp.spec_index(pagetable_ptr).being_killed() == old(krnl).pt_mp.spec_index(pagetable_ptr).being_killed()
                    }
                },
            held_pagetable_windows_unchanged(old(krnl).pt_mp, old(krnl).pt_lower.view(), final(krnl).pt_mp, final(krnl).pt_lower.view(), old(lctx)),
            containers_rodata_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp),
            processes_rodata_unchanged(old(krnl).prc_mp, final(krnl).prc_mp),
            held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
            held_schedulers_unchanged(old(krnl).sched_mp, final(krnl).sched_mp, old(lctx)),
            held_pcid_allocators_unchanged(old(krnl).pcid_allc_mp, final(krnl).pcid_allc_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
            write_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr),
    {
        proof {
            let pre = steps.snapshot_k();
            let before = *krnl;
            let before_lctx = *lctx;
            krnl.kernel_step_boundary_thread_quota_4k_changed(&mut *lctx, &mut *steps, quota_thread_ptr, -1);
            assert(write_held ==> pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr) == pagetable_c(before.pt_mp, before.pt_lower.view(), pagetable_ptr)) by {
                if write_held { assert(before_lctx.pagetable_lock_map().dom().contains(pagetable_ptr)); }
            };
            if mmap_guard { mmap_4k_directory_step_from_k(&pre, &before, &before_lctx, cpu_id, quota_thread_ptr, process_ptr, pagetable_ptr, level, write_held); }
            if share_guard {
                share_4k_directory_step_from_k(&pre, &before, &share_lctx, &before_lctx, cpu_id, progress_thread, quota_thread_ptr, process_ptr, container_ptr, pagetable_ptr,
                    transfer_source, page_ptr);
                assert(share_4k_objects_k(*krnl, cpu_id) == share_4k_objects_k(before, cpu_id)) by { reveal(share_4k_objects_k); };
                assert(krnl.thr_mp.spec_index(progress_thread).view().syscall_progress.view()->Some_0->Share4k_origin matches Share4kOrigin::IpcPages { peer }
                    ==> krnl.thr_mp.spec_index(peer).view().state is IPC_TRANSIT && krnl.thr_mp.spec_index(peer).view().state->IPC_TRANSIT_partner == progress_thread) by { reveal(share_4k_objects_k); };
            }
        }
    }

    /// Move the staged page from `transfer_source` into `container_ptr` when the quota thread allocated it from the parent container.
    fn install_one_mmap_4k_directory_page_transfer_if_source(
        krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, page_ptr: PagePtr, quota_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
        transfer_source: Option<RwLockContainerPtr>, Tracked(page_lock_perm): Tracked<&LockPerm>, Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>,
        Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
    )
        requires
            old(krnl).inv(),
            typed_lock_maps_aligned(old(krnl), old(lctx)),
            page_ptr_valid(page_ptr),
            old(krnl).thr_mp.dom().contains(quota_thread_ptr),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view().contains(page_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
            !old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: quota_thread_ptr }),
            old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == (match transfer_source { Some(source) => source, None => container_ptr }),
            page_lock_perm.state() is WriteLock,
            page_lock_perm.thread_id() == old(lctx).thread_id(),
            page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& source != container_ptr
                &&& old(krnl).ctn_mp.dom().contains(source) && old(krnl).ctn_mp.dom().contains(container_ptr)
                &&& old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().parent == Some(source)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), source, TypedLockMode::Write)
                &&& typed_lock_map_contains_mode(old(lctx).container_lock_map(), container_ptr, TypedLockMode::Write)
                &&& !old(krnl).ctn_mp.spec_index(source).being_killed() && !old(krnl).ctn_mp.spec_index(container_ptr).being_killed()
                &&& transfer_source_lock_perm is Some && transfer_source_lock_perm->Some_0.state() is WriteLock
                &&& transfer_source_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_source_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(source).locking_thread()->Write_lock_id
                &&& transfer_target_lock_perm is Some && transfer_target_lock_perm->Some_0.state() is WriteLock
                &&& transfer_target_lock_perm->Some_0.thread_id() == old(lctx).thread_id()
                &&& transfer_target_lock_perm->Some_0.lock_id() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()->Write_lock_id
            },
        ensures
            final(krnl).inv(),
            *final(lctx) == *old(lctx),
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            *final(krnl) == (KernelK { pg_arr: final(krnl).pg_arr, ctn_mp: final(krnl).ctn_mp, ..*old(krnl) }),
            final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state,
            final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == container_ptr,
            !final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().being_killed(),
            page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
            transfer_source is None ==> *final(krnl) == *old(krnl),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                &&& old(krnl).ctn_mp.spec_index(source).view().owned_pages.view().contains(page_ptr)
                &&& final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom()
                &&& forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
                    old(krnl).ctn_mp.dom().contains(c) && c != source && c != container_ptr ==> final(krnl).ctn_mp.spec_index(c) == old(krnl).ctn_mp.spec_index(c)
                &&& final(krnl).ctn_mp.spec_index(source).is_init() == old(krnl).ctn_mp.spec_index(source).is_init()
                &&& final(krnl).ctn_mp.spec_index(source).view_rodata() == old(krnl).ctn_mp.spec_index(source).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(source).view_ghost() == old(krnl).ctn_mp.spec_index(source).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(source).locking_thread() == old(krnl).ctn_mp.spec_index(source).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(source).being_killed() == old(krnl).ctn_mp.spec_index(source).being_killed()
                &&& final(krnl).ctn_mp.spec_index(source).killer_info() == old(krnl).ctn_mp.spec_index(source).killer_info()
                &&& final(krnl).ctn_mp.spec_index(source).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(source).view().owned_pages, ..old(krnl).ctn_mp.spec_index(source).view() })
                &&& final(krnl).ctn_mp.spec_index(container_ptr).is_init() == old(krnl).ctn_mp.spec_index(container_ptr).is_init()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view_ghost() == old(krnl).ctn_mp.spec_index(container_ptr).view_ghost()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).locking_thread() == old(krnl).ctn_mp.spec_index(container_ptr).locking_thread()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(container_ptr).being_killed()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).killer_info() == old(krnl).ctn_mp.spec_index(container_ptr).killer_info()
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages, ..old(krnl).ctn_mp.spec_index(container_ptr).view() })
                &&& final(krnl).ctn_mp.spec_index(source).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(source).view().owned_pages.view().remove(page_ptr)
                &&& final(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages.view() =~= old(krnl).ctn_mp.spec_index(container_ptr).view().owned_pages.view().insert(page_ptr)
            },
    {
        if let Some(source) = transfer_source {
            let tracked source_lock_perm = transfer_source_lock_perm.tracked_unwrap();
            let tracked target_lock_perm = transfer_target_lock_perm.tracked_unwrap();
            proof { assert(krnl.ctn_mp.spec_index(source).view().owned_pages.view().contains(page_ptr)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_ptr2page_index(page_ptr)); }; }
            transfer_staged_4k_page_to_child_container(krnl, Tracked(&mut *lctx), page_ptr, quota_thread_ptr, source, container_ptr, Tracked(page_lock_perm), Tracked(source_lock_perm), Tracked(target_lock_perm));
        }
    }
} // verus!
