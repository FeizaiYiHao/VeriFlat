use vstd::prelude::*;

use crate::*;
use super::mmap_4k_install_one::install_one_mmap_4k_directory_page;
use super::mmap_4k_build_structure_spec::*;

verus! {
    /// Install the missing L4, L3 and L2 directories on the walk to `va` under the table's big write lock. When the L3 entry
    /// already exists this thread holds the 2M window of `va`; when this call creates the L2 page, its windows `lo..=hi` start
    /// held by this thread and their lock perms are returned, keyed by window.
    pub fn mmap_4k_build_one_structure(
        krnl: &mut KernelK, va: VAddr, lo: L2Index, hi: L2Index, alloc_ptr_4k: RwLockPageAllocatorPtr, quota_thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr, cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot,
        transfer_source: Option<RwLockContainerPtr>, Ghost(progress_thread): Ghost<RwLockThreadPtr>, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
        Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>, Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
    ) -> (ret: Tracked<Map<WindowVa, LockPerm>>)
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
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(spec_v2l4index(va), spec_v2l3index(va)) ==> old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va))),
            va_4k_valid(va),
            pei_valid(lo) && pei_valid(hi) && lo <= spec_v2l2index(va) <= hi,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(quota_thread_ptr)) >= 3,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_4k_entry_usable(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va)),
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
                &&& final(steps).snapshot_k() == *final(krnl)
                &&& share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id)
                &&& old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 3
                &&& forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j]
                &&& forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
                    &&& share_4k_directory_step_pre(final(steps).view()[j].old_u, cpu_id)
                    &&& share_4k_directory_step(final(steps).view()[j].old_u, final(steps).view()[j].new_u, cpu_id)
                }
            },
            final(krnl).thr_mp.lock_id_by_key(quota_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(quota_thread_ptr),
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
            quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            old(steps).nonlock_view().len() <= final(steps).nonlock_view().len(),
            final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 3,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            final(krnl).irt.view().owners() == final(steps).snapshot_k().irt.view().owners(),
            final(krnl).irt.view().iommu_roots() == final(steps).snapshot_k().irt.view().iommu_roots(),
            final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
            final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    || (!pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(spec_v2l4index(va), spec_v2l3index(va)) && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == spec_v2l4index(va)
                        && spec_v2l3index(w.va) == spec_v2l3index(va) && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(spec_v2l4index(va), spec_v2l3index(va))
                    || !(p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == spec_v2l4index(va) && spec_v2l3index(w.va) == spec_v2l3index(va) && lo <= spec_v2l2index(w.va) <= hi))
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
                !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(spec_v2l4index(va), spec_v2l3index(va)) && w.wf() && spec_v2l4index(w.va) == spec_v2l4index(va) && spec_v2l3index(w.va) == spec_v2l3index(va) && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, w), mode: TypedLockMode::Write }),
            final(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va))),
            forall|w: WindowVa| #![trigger ret.view().dom().contains(w)]
                ret.view().dom().contains(w) == (!pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(spec_v2l4index(va), spec_v2l3index(va)) && w.wf() && spec_v2l4index(w.va) == spec_v2l4index(va)
                    && spec_v2l3index(w.va) == spec_v2l3index(va) && lo <= spec_v2l2index(w.va) <= hi),
            forall|w: WindowVa| #![trigger ret.view().index(w)] ret.view().dom().contains(w) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr)
                    .window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &ret.view().index(w))
                &&& ret.view().index(w).state() is WriteLock
                &&& ret.view().index(w).thread_id() == final(lctx).thread_id()
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
            held_pagetables_unchanged_except(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx), set![pagetable_ptr]),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && old(lctx).pagetable_lock_map().dom().contains(p) && p != pagetable_ptr ==> {
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
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().caller == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().caller,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().callee == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().callee,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().endpoint_descriptors.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 3,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().state == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().state,
            !(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k)
                ==> final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view(),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some ==> {
                let progress = old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0;
                let final_progress = final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0;
                &&& final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some
                &&& progress is Mmap4k ==> final_progress is Mmap4k
                &&& final_progress->Mmap4k_range == progress->Mmap4k_range
                &&& final_progress->Mmap4k_mapped == progress->Mmap4k_mapped
            },
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(l4i == spec_v2l4index(va) && l3i == spec_v2l3index(va))
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))
                        == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i)),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
    {
        hide(Set::is_empty);
        proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }

        let indices = va2index(va);
        assert({
            &&& pei_valid(spec_v2l4index(va))
            &&& pei_valid(spec_v2l3index(va))
            &&& pei_valid(spec_v2l2index(va))
            &&& pei_valid(spec_v2l1index(va))
        });
        proof {
            assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable_ptr).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); };
            pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            let (l4i, l3i, l2i) = (indices.0, indices.1, indices.2);
            assert(KERNEL_MEM_END_L4INDEX <= l4i && spec_va2index(va) == indices) by { spec_va_4k_index_roundtrip_at(va, indices.0, indices.1, indices.2, indices.3); };
            assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
        }
        let (l4_present, l3_present, l2_present) = {
            let pagetable = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), Tracked(pagetable_lock_perm));
            let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
            match pagetable.get_entry_l4(indices.0) {
                None => (false, false, false),
                Some(l4_entry) => match pagetable.get_entry_l3(indices.0, indices.1, &l4_entry) {
                    None => (true, false, false),
                    Some(l3_entry) => (true, true, pagetable.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3_entry).is_some()),
                },
            }
        };
        let windows = install_missing_mmap_4k_directories(
            krnl, alloc_ptr_4k, quota_thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, (indices.0, indices.1, indices.2), lo, hi, l4_present, l3_present, l2_present,
            transfer_source, Ghost(progress_thread), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm),
            Tracked(transfer_source_lock_perm), Tracked(transfer_target_lock_perm),
        );
        assert(krnl.thr_mp.lock_id_by_key(quota_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(quota_thread_ptr)) by { thread_lock_id_preserved_for_typed_maps_unchanged(old(krnl), krnl, old(lctx), lctx, quota_thread_ptr); };
        windows
    }

    /// Install the missing L4, L3 and L2 directories on the walk to `indices`, in that order.
    fn install_missing_mmap_4k_directories(
        krnl: &mut KernelK, alloc_ptr_4k: RwLockPageAllocatorPtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
        cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), lo: L2Index, hi: L2Index, l4_present: bool, l3_present: bool, l2_present: bool,
        transfer_source: Option<RwLockContainerPtr>, Ghost(progress_thread): Ghost<RwLockThreadPtr>, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
        Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>, Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
    ) -> (ret: Tracked<Map<WindowVa, LockPerm>>)
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
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
            KERNEL_MEM_END_L4INDEX <= indices.0,
            l3_present ==> old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((indices.0, indices.1, indices.2, 0))),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(quota_thread_ptr)) >= 3,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            pei_valid(lo) && pei_valid(hi) && lo <= indices.2 <= hi,
            l4_present == (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some),
            !l4_present ==> !l3_present,
            l3_present == (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some),
            !l3_present ==> !l2_present && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
            l3_present ==> l2_present == (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some),
            l3_present && !l2_present ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
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
                &&& final(steps).snapshot_k() == *final(krnl)
                &&& share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id)
                &&& old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 3
                &&& forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j]
                &&& forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
                    &&& share_4k_directory_step_pre(final(steps).view()[j].old_u, cpu_id)
                    &&& share_4k_directory_step(final(steps).view()[j].old_u, final(steps).view()[j].new_u, cpu_id)
                }
            },
            final(krnl).thr_mp.lock_id_by_key(quota_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(quota_thread_ptr),
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
            quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            old(steps).nonlock_view().len() <= final(steps).nonlock_view().len(),
            final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 3,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            final(krnl).irt.view().owners() == final(steps).snapshot_k().irt.view().owners(),
            final(krnl).irt.view().iommu_roots() == final(steps).snapshot_k().irt.view().iommu_roots(),
            final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
            final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    || (!pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(indices.0, indices.1) && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0
                        && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(indices.0, indices.1)
                    || !(p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi))
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
                !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(indices.0, indices.1) && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, w), mode: TypedLockMode::Write }),
            final(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            forall|w: WindowVa| #![trigger ret.view().dom().contains(w)]
                ret.view().dom().contains(w) == (!pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(indices.0, indices.1) && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1
                    && lo <= spec_v2l2index(w.va) <= hi),
            forall|w: WindowVa| #![trigger ret.view().index(w)] ret.view().dom().contains(w) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr)
                    .window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &ret.view().index(w))
                &&& ret.view().index(w).state() is WriteLock
                &&& ret.view().index(w).thread_id() == final(lctx).thread_id()
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
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && old(lctx).pagetable_lock_map().dom().contains(p) && p != pagetable_ptr ==> {
                    &&& final(lctx).pagetable_window_lock_map().dom().contains((p, w))
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
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().caller == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().caller,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().callee == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().callee,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().endpoint_descriptors.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 3,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().state == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().state,
            !(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k)
                ==> final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view(),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some ==> {
                let progress = old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0;
                let final_progress = final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0;
                &&& final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some
                &&& progress is Mmap4k ==> final_progress is Mmap4k
                &&& final_progress->Mmap4k_range == progress->Mmap4k_range
                &&& final_progress->Mmap4k_mapped == progress->Mmap4k_mapped
            },
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(l4i == indices.0 && l3i == indices.1)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))
                        == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i)),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
    {
        hide(Set::is_empty);
        proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
        if !l4_present {
            let _ = install_one_mmap_4k_directory_page(
                krnl, MissingPageTableLevel::L4, alloc_ptr_4k, quota_thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, indices, indices.2, indices.2, true, transfer_source,
                Ghost(progress_thread), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(transfer_source_lock_perm),
                Tracked(transfer_target_lock_perm),
            );
        }
        let ghost before_lower = *krnl;
        let ghost lctx_lower = *lctx;
        let windows = install_missing_mmap_4k_l3_l2_directories(
            krnl, alloc_ptr_4k, quota_thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, indices, lo, hi, l3_present, l2_present, transfer_source, Ghost(progress_thread),
            Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(transfer_source_lock_perm), Tracked(transfer_target_lock_perm),
        );
        proof {
            if !l4_present {
                if transfer_source is None { held_containers_unchanged_transitive(old(krnl).ctn_mp, before_lower.ctn_mp, krnl.ctn_mp, old(lctx), &lctx_lower); }
                held_processes_unchanged_transitive(old(krnl).prc_mp, before_lower.prc_mp, krnl.prc_mp, old(lctx), &lctx_lower);
                held_endpoints_unchanged_transitive(old(krnl).ep_mp, before_lower.ep_mp, krnl.ep_mp, old(lctx), &lctx_lower);
                held_schedulers_unchanged_transitive(old(krnl).sched_mp, before_lower.sched_mp, krnl.sched_mp, old(lctx), &lctx_lower);
                held_pcid_allocators_unchanged_transitive(old(krnl).pcid_allc_mp, before_lower.pcid_allc_mp, krnl.pcid_allc_mp, old(lctx), &lctx_lower);
                held_iommu_tables_unchanged_transitive(old(krnl).it_mp, before_lower.it_mp, krnl.it_mp, old(lctx), &lctx_lower);
                held_cpus_unchanged_transitive(old(krnl).cpu_arr, before_lower.cpu_arr, krnl.cpu_arr, old(lctx), &lctx_lower);
                held_threads_unchanged_except_transitive(old(krnl).thr_mp, before_lower.thr_mp, krnl.thr_mp, old(lctx), &lctx_lower, set![quota_thread_ptr]);
                held_pagetables_unchanged_except_transitive(old(krnl).pt_mp, before_lower.pt_mp, krnl.pt_mp, old(lctx), &lctx_lower, set![pagetable_ptr]);
            }
        }
        assert(krnl.thr_mp.lock_id_by_key(quota_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(quota_thread_ptr)) by { thread_lock_id_preserved_for_typed_maps_unchanged(old(krnl), krnl, old(lctx), lctx, quota_thread_ptr); };
        windows
    }

    /// Install the missing L3 and L2 directories below a present L4 entry.
    fn install_missing_mmap_4k_l3_l2_directories(
        krnl: &mut KernelK, alloc_ptr_4k: RwLockPageAllocatorPtr, quota_thread_ptr: RwLockThreadPtr, process_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
        cpu_id: CpuId, pagetable_ptr: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index), lo: L2Index, hi: L2Index, l3_present: bool, l2_present: bool,
        transfer_source: Option<RwLockContainerPtr>, Ghost(progress_thread): Ghost<RwLockThreadPtr>, Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>, Tracked(quota_thread_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
        Tracked(transfer_source_lock_perm): Tracked<Option<&LockPerm>>, Tracked(transfer_target_lock_perm): Tracked<Option<&LockPerm>>,
    ) -> (ret: Tracked<Map<WindowVa, LockPerm>>)
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
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
            old(krnl).irt.view().owners() == old(steps).snapshot_k().irt.view().owners(),
            old(krnl).irt.view().iommu_roots() == old(steps).snapshot_k().irt.view().iommu_roots(),
            old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
            old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
            held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
            KERNEL_MEM_END_L4INDEX <= indices.0,
            l3_present ==> old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.spec_index(held_page).view().view().orders_below_table_locks(),
            page_table_key_2m_valid::<PT_TYPE>(spec_index2va((indices.0, indices.1, indices.2, 0))),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            thread_effective_quota_4k(old(krnl).thr_mp.spec_index(quota_thread_ptr)) >= 2,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= indices.0 && pei_valid(indices.0),
            pei_valid(indices.1),
            pei_valid(indices.2),
            pei_valid(lo) && pei_valid(hi) && lo <= indices.2 <= hi,
            pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l4(indices.0) is Some,
            l3_present == (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(indices.0, indices.1) is Some),
            !l3_present ==> !l2_present && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_1g_l3(indices.0, indices.1) is None,
            l3_present ==> l2_present == (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some),
            l3_present && !l2_present ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_2m_l2(indices.0, indices.1, indices.2) is None,
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
                &&& final(steps).snapshot_k() == *final(krnl)
                &&& share_4k_objects_k(*final(krnl), cpu_id) == share_4k_objects_k(*old(krnl), cpu_id)
                &&& old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + 2
                &&& forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j]
                &&& forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
                    &&& share_4k_directory_step_pre(final(steps).view()[j].old_u, cpu_id)
                    &&& share_4k_directory_step(final(steps).view()[j].old_u, final(steps).view()[j].new_u, cpu_id)
                }
            },
            final(krnl).thr_mp.lock_id_by_key(quota_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(quota_thread_ptr),
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
            quota_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(quota_thread_ptr).locking_thread()->Write_lock_id,
            final(krnl).allc_4k_mp.dom().contains(alloc_ptr_4k),
            final(krnl).pt_mp.dom().contains(pagetable_ptr),
            typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Write),
            pagetable_lock_perm.lock_id() == final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Write_lock_id,
            old(steps).nonlock_view().len() <= final(steps).nonlock_view().len(),
            final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + 2,
            final(steps).nonlock_view().subrange(0, old(steps).nonlock_view().len() as int) == old(steps).nonlock_view(),
            final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
            kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
            final(krnl).irt.view().owners() == final(steps).snapshot_k().irt.view().owners(),
            final(krnl).irt.view().iommu_roots() == final(steps).snapshot_k().irt.view().iommu_roots(),
            final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
            final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
            final(lctx).thread_id() == old(lctx).thread_id(),
            nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                    || (!pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(indices.0, indices.1) && p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0
                        && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi)),
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && (pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(indices.0, indices.1)
                    || !(p == pagetable_ptr && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi))
                    ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
            forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w))]
                !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(indices.0, indices.1) && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1 && lo <= spec_v2l2index(w.va) <= hi
                    ==> final(lctx).pagetable_window_lock_map().index((pagetable_ptr, w)) == (TypedHeldLock { lock_id: window_lock_id_at(pagetable_ptr, w), mode: TypedLockMode::Write }),
            final(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) })),
            forall|w: WindowVa| #![trigger ret.view().dom().contains(w)]
                ret.view().dom().contains(w) == (!pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(indices.0, indices.1) && w.wf() && spec_v2l4index(w.va) == indices.0 && spec_v2l3index(w.va) == indices.1
                    && lo <= spec_v2l2index(w.va) <= hi),
            forall|w: WindowVa| #![trigger ret.view().index(w)] ret.view().dom().contains(w) ==> {
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr)
                    .window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va))).lock_perm_match(spec_v2l2index(w.va), &ret.view().index(w))
                &&& ret.view().index(w).state() is WriteLock
                &&& ret.view().index(w).thread_id() == final(lctx).thread_id()
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
            forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
                old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && old(lctx).pagetable_lock_map().dom().contains(p) && p != pagetable_ptr ==> {
                    &&& final(lctx).pagetable_window_lock_map().dom().contains((p, w))
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
            held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().caller == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().caller,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().callee == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().callee,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_container,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_2m,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_1g,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().endpoint_descriptors.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().endpoint_descriptors.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().ipc_payload,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().error_code,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().trap_frame,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(quota_thread_ptr).being_killed(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view_ghost(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_4k.view(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_2m.view().len() == 0,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().temp_alloc_cache_1g.view().len() == 0,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().free_quota_pending_clean(),
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k <= old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k >= old(krnl).thr_mp.spec_index(quota_thread_ptr).view().quota_4k - 2,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().owning_proc,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().proc_pagetable_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().state == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().state,
            !(old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some && old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0 is Mmap4k)
                ==> final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view(),
            old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some ==> {
                let progress = old(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0;
                let final_progress = final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view()->Some_0;
                &&& final(krnl).thr_mp.spec_index(quota_thread_ptr).view().syscall_progress.view() is Some
                &&& progress is Mmap4k ==> final_progress is Mmap4k
                &&& final_progress->Mmap4k_range == progress->Mmap4k_range
                &&& final_progress->Mmap4k_mapped == progress->Mmap4k_mapped
            },
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().blocking_endpoint_ptr,
            final(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq == old(krnl).thr_mp.spec_index(quota_thread_ptr).view().upper_container_seq,
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).wf(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).user_view(LockStateU::Unlocked),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_2m(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_1g(),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.window_stale_cpus,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && !(l4i == indices.0 && l3i == indices.1)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(l4i, l3i),
            forall|l4i: L4Index, l3i: L3Index, l2i: L2Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i)]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            forall|l4i: L4Index, l3i: L3Index| #![trigger pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))]
                pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).kernel_l4_end() <= l4i && pei_valid(l4i) && pei_valid(l3i) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_exists(l4i, l3i)
                    ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i))
                        == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_l2_page(l4i, l3i)),
            pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
            final(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr == old(krnl).pt_mp.spec_index(pagetable_ptr).view().proc_ptr,
            final(krnl).cpu_arr.spec_index(cpu_id).view() == old(krnl).cpu_arr.spec_index(cpu_id).view(),
    {
        hide(Set::is_empty);
        proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
        let ghost window_va = WindowVa { va: spec_index2va((indices.0, indices.1, indices.2, 0usize)) };
        let tracked mut windows: Map<WindowVa, LockPerm> = Map::tracked_empty();
        if !l3_present {
            let Tracked(minted) = install_one_mmap_4k_directory_page(
                krnl, MissingPageTableLevel::L3, alloc_ptr_4k, quota_thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, indices, lo, hi, true, transfer_source,
                Ghost(progress_thread), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(transfer_source_lock_perm),
                Tracked(transfer_target_lock_perm),
            );
            proof {
                broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid, Set::lemma_map_by_contains;
                let key_map = Map::new(minted.dom().map_by(|l2i: L2Index| WindowVa { va: spec_index2va((indices.0, indices.1, l2i, 0usize)) }, |w: WindowVa| spec_v2l2index(w.va)),
                    |w: WindowVa| spec_v2l2index(w.va));
                windows = Map::<L2Index, LockPerm>::tracked_map_keys(minted, key_map);
                spec_va_4k_index_roundtrip_at(window_va.va, indices.0, indices.1, indices.2, 0usize);
                assert(lctx.pagetable_window_lock_map().dom().contains((pagetable_ptr, window_va)));
            }
        }
        let ghost before_l2 = *krnl;
        let ghost lctx_l2 = *lctx;
        if !l2_present {
            let _ = install_one_mmap_4k_directory_page(
                krnl, MissingPageTableLevel::L2, alloc_ptr_4k, quota_thread_ptr, process_ptr, container_ptr, cpu_id, pagetable_ptr, indices, indices.2, indices.2, true, transfer_source,
                Ghost(progress_thread), Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(quota_thread_lock_perm), Tracked(pagetable_lock_perm), Tracked(transfer_source_lock_perm),
                Tracked(transfer_target_lock_perm),
            );
        }
        proof {
            broadcast use spec_va_2m_valid_index_roundtrip, spec_index2va_2m_valid;
            spec_va_4k_index_roundtrip_at(window_va.va, indices.0, indices.1, indices.2, 0usize);
            held_kernel_objects_unchanged_reflexive(old(krnl), old(lctx));
            if !l3_present {
                if transfer_source is None {
                    assert(held_containers_unchanged(before_l2.ctn_mp, krnl.ctn_mp, old(lctx)));
                    held_containers_unchanged_transitive(old(krnl).ctn_mp, before_l2.ctn_mp, krnl.ctn_mp, old(lctx), old(lctx));
                }
                assert(held_processes_unchanged(before_l2.prc_mp, krnl.prc_mp, old(lctx)));
                held_processes_unchanged_transitive(old(krnl).prc_mp, before_l2.prc_mp, krnl.prc_mp, old(lctx), old(lctx));
                assert(held_endpoints_unchanged(before_l2.ep_mp, krnl.ep_mp, old(lctx)));
                held_endpoints_unchanged_transitive(old(krnl).ep_mp, before_l2.ep_mp, krnl.ep_mp, old(lctx), old(lctx));
                assert(held_schedulers_unchanged(before_l2.sched_mp, krnl.sched_mp, old(lctx)));
                held_schedulers_unchanged_transitive(old(krnl).sched_mp, before_l2.sched_mp, krnl.sched_mp, old(lctx), old(lctx));
                assert(held_pcid_allocators_unchanged(before_l2.pcid_allc_mp, krnl.pcid_allc_mp, old(lctx)));
                held_pcid_allocators_unchanged_transitive(old(krnl).pcid_allc_mp, before_l2.pcid_allc_mp, krnl.pcid_allc_mp, old(lctx), old(lctx));
                assert(held_iommu_tables_unchanged(before_l2.it_mp, krnl.it_mp, old(lctx)));
                held_iommu_tables_unchanged_transitive(old(krnl).it_mp, before_l2.it_mp, krnl.it_mp, old(lctx), old(lctx));
                assert(held_cpus_unchanged(before_l2.cpu_arr, krnl.cpu_arr, old(lctx)));
                held_cpus_unchanged_transitive(old(krnl).cpu_arr, before_l2.cpu_arr, krnl.cpu_arr, old(lctx), old(lctx));
                assert(held_threads_unchanged_except(before_l2.thr_mp, krnl.thr_mp, old(lctx), set![quota_thread_ptr]));
                held_threads_unchanged_except_transitive(old(krnl).thr_mp, before_l2.thr_mp, krnl.thr_mp, old(lctx), old(lctx), set![quota_thread_ptr]);
                assert(held_pagetables_unchanged_except(before_l2.pt_mp, krnl.pt_mp, old(lctx), set![pagetable_ptr]));
                held_pagetables_unchanged_except_transitive(old(krnl).pt_mp, before_l2.pt_mp, krnl.pt_mp, old(lctx), old(lctx), set![pagetable_ptr]);
            }
        }
        assert(krnl.thr_mp.lock_id_by_key(quota_thread_ptr) == old(krnl).thr_mp.lock_id_by_key(quota_thread_ptr)) by { thread_lock_id_preserved_for_typed_maps_unchanged(old(krnl), krnl, old(lctx), lctx, quota_thread_ptr); };
        Tracked(windows)
    }
} // verus!
