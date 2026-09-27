use vstd::prelude::*;
use crate::*;
use super::mmap_4k_create_entry_install::{
    install_staged_4k_page_table_page,
    MissingPageTableLevel,
};
use super::mmap_4k_build_structure_spec::*;

verus! {
    /// Allocate and install one missing directory page, then end the krnl
    /// section. Directory topology is absent from `PageTableU`, while the
    /// quota deduction is visible through `ThreadU` at this boundary.
    pub(super) fn install_one_mmap_4k_directory_page(
        krnl: &mut KernelK, level: MissingPageTableLevel, alloc_ptr_4k: RwLockPageAllocatorPtr, quota_thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot,
        indices: (L4Index, L3Index, L2Index), transfer_source: Option<RwLockContainerPtr>, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>,
        Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
    )
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
            ((old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)),
            quota_thread_lock_perm.state() is WriteLock,
            quota_thread_lock_perm.thread_id() == old(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            old(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            old(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
            old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(quota_thread_ptr)) >= 1,
            old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end <= indices.0 && pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            match level {
                MissingPageTableLevel::L4 =>
                    old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is None,
                MissingPageTableLevel::L3 => {
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is Some
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L2 => {
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& old(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
            },
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_MAJOR),
        ensures
            forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            final(krnl).inv(),
            final(lctx).kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(final(krnl), final(lctx)),
            typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
            final(krnl).ctn_mp.dom().contains(container_ptr),
            final(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k == alloc_ptr_4k,
            final(krnl).prc_mp.dom().contains(process_ptr),
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr,
            final(krnl).prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr,
            final(krnl).thr_mp.dom().contains(quota_thread_ptr),
            typed_lock_map_contains_mode(final(lctx).thread_lock_map(), quota_thread_ptr, TypedLockMode::Write),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == false,
            mmap_4k_quota_thread_container_compatible(final(krnl), final(lctx), quota_thread_ptr, container_ptr),
            ((final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_ptr, TypedLockMode::Write)),
            quota_thread_lock_perm.thread_id() == final(lctx).thread_id(),
            quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.thread_id() == final(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            final(steps).snapshot_k() == *final(krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
            transfer_source is None ==> held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
            transfer_source is Some ==> {
                let source = transfer_source->Some_0;
                let old_source_pages = old(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
                let new_source_pages = final(krnl).ctn_mp.spec_index(source).view().owned_pages.view();
                &&& forall|c: RwLockContainerPtr| #![trigger final(krnl).ctn_mp.spec_index(c)]
                    c == source || c == container_ptr ==> {
                        &&& final(krnl).ctn_mp.dom().contains(c)
                        &&& final(krnl).ctn_mp.spec_index(c).is_init() == old(krnl).ctn_mp.spec_index(c).is_init()
                        &&& final(krnl).ctn_mp.spec_index(c).view_rodata() == old(krnl).ctn_mp.spec_index(c).view_rodata()
                        &&& final(krnl).ctn_mp.spec_index(c).view_ghost() == old(krnl).ctn_mp.spec_index(c).view_ghost()
                        &&& final(krnl).ctn_mp.spec_index(c).locking_thread() == old(krnl).ctn_mp.spec_index(c).locking_thread()
                        &&& final(krnl).ctn_mp.spec_index(c).being_killed() == old(krnl).ctn_mp.spec_index(c).being_killed()
                        &&& final(krnl).ctn_mp.spec_index(c).view() == (Container { owned_pages: final(krnl).ctn_mp.spec_index(c).view().owned_pages, ..old(krnl).ctn_mp.spec_index(c).view() })
                    }
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
            final(steps).nonlock_view().last().new_u.thread_map.spec_index(quota_thread_ptr) == (ThreadU {
                quota_4k: (final(steps).nonlock_view().last().old_u.thread_map.spec_index(quota_thread_ptr).quota_4k as int - 1) as usize,
                syscall_progress: final(steps).nonlock_view().last().new_u.thread_map.spec_index(quota_thread_ptr).syscall_progress,
                ..final(steps).nonlock_view().last().old_u.thread_map.spec_index(quota_thread_ptr)
            }),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed()
                == old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed(),
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
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            final(krnl).pt_mp.spec_index(pagetable_ptr).inv(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().wf(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().user_view(LockStateU::Unlocked) == old(krnl).pt_mp.spec_index(pagetable_ptr).view().user_view(LockStateU::Unlocked),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_4k(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_2m(),
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g() == old(krnl).pt_mp.spec_index(pagetable_ptr).view().mapping_1g(),
            match level {
                MissingPageTableLevel::L4 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l4(indices.0) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_1g_l3(indices.0, indices.1) is None
                },
                MissingPageTableLevel::L3 => {
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l3(indices.0, indices.1) is Some
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is None
                    &&& final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None
                },
                MissingPageTableLevel::L2 =>
                    final(krnl).pt_mp.spec_index(pagetable_ptr).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            },
            old(steps).snapshot_k() == *old(krnl) && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some
                && mmap_4k_directory_rank(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0->Mmap4k_directory) < mmap_4k_directory_rank(mmap_4k_installed_directory(level))
                && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr)
                && transfer_source is None
                ==> {
                    &&& final(steps).view() == old(steps).view().push(final(steps).view().last())
                    &&& mmap_4k_directory_step_pre(final(steps).view().last().old_u, cpu_id, quota_thread_ptr)
                    &&& mmap_4k_directory_step(final(steps).view().last().old_u, final(steps).view().last().new_u, quota_thread_ptr)
                },
    {

        proof { assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; }; }
        let alloc_container_ptr = match transfer_source { Some(source) => source, None => container_ptr };
        let (page_ptr, Tracked(page_lock_perm)) = allocate_free_4k_page(krnl, quota_thread_ptr, alloc_container_ptr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm));
        if let Some(source) = transfer_source {
            let tracked source_lock_perm = transfer_source_lock_perm.tracked_unwrap();
            let tracked target_lock_perm = transfer_target_lock_perm.tracked_unwrap();
            proof { assert(krnl.ctn_mp.spec_index(source).view().owned_pages.view().contains(page_ptr)) by { reveal(container_page_owner_wf); page_ptr_valid_imply_page_index_valid(); }; }
            transfer_staged_4k_page_to_child_container(krnl, Tracked(&mut *lctx), page_ptr, quota_thread_ptr, source, container_ptr, Tracked(&page_lock_perm), Tracked(source_lock_perm), Tracked(target_lock_perm));
        }
        let ghost staged_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr));
        proof {
            assert(krnl.prc_mp.dom().contains(process_ptr) && krnl.prc_mp.spec_index(process_ptr).view_rodata().view().owning_container == container_ptr && krnl.prc_mp.spec_index(process_ptr).view_rodata().view().pagetable == pagetable_ptr) by { reveal(process_thread_wf); reveal(process_pagetable_match); };
        }
        install_staged_4k_page_table_page(krnl, level, page_ptr, quota_thread_ptr, process_ptr, container_ptr, pagetable_ptr, indices, Tracked(&mut *lctx), Tracked(&page_lock_perm), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm));
        let ghost installed_page_lock_id = krnl.pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr));
        krnl.wunlock_page(page_ptr2page_index(page_ptr), Tracked(&mut *lctx), Tracked(page_lock_perm));
        proof {
            assert(typed_lock_maps_unchanged(old(lctx), lctx)) by {
                map_insert_overwrite_lemma(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedHeldLock {
                    lock_id: staged_page_lock_id, mode: TypedLockMode::Write,
                }, TypedHeldLock {
                    lock_id: installed_page_lock_id, mode: TypedLockMode::Write,
                });
                map_insert_remove_absent_lemma(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedHeldLock {
                    lock_id: installed_page_lock_id, mode: TypedLockMode::Write,
                });
            };

            assert(kernel_thread_quota_4k_changed(
                &steps.snapshot_k(), &*krnl, quota_thread_ptr, -1,
            )) by { reveal(kernel_thread_quota_4k_changed); };
            if transfer_source is None { kernel_thread_quota_4k_and_progress_changed_implies_u_step(&steps.snapshot_k(), &*krnl, &*lctx, cpu_id, quota_thread_ptr, process_ptr, pagetable_ptr); }
            krnl.kernel_step_boundary_thread_quota_4k_changed(
                &mut *lctx, &mut *steps, quota_thread_ptr, -1,
            );
            assert(krnl.ctn_mp.dom().contains(container_ptr)) by { reveal(container_thread_wf); };
            assert(krnl.prc_mp.dom().contains(process_ptr) && ((krnl.thr_mp.spec_index(quota_thread_ptr).view().owning_proc == process_ptr && krnl.thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == pagetable_ptr) || typed_lock_map_contains_mode(lctx.process_lock_map(), process_ptr, TypedLockMode::Write))) by { reveal(process_thread_wf); };
            assert(krnl.allc_4k_mp.dom().contains(alloc_ptr_4k)) by { reveal(container_allocator_wf); };
            assert(krnl.pt_mp.spec_index(pagetable_ptr).inv() && krnl.pt_mp.spec_index(pagetable_ptr).view().wf()) by { reveal(pagetable_perms_wf); };
        }
    }
} // verus!
