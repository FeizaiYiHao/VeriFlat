use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_retire_pages::kill_retire_lock_cache;

verus! {
/// Write-lock what retiring the table page `page_ptr` that `scan` names from the write-held table `table` of the zombie
/// `target` (its write-held IOMMU table when `iommu`) takes: the page and, after a step boundary the projection does not
/// show, shard `cpu_id` of the 4K allocator of the page's owner. Returns the page and cache permissions, the owner and its
/// 4K allocator, and the lock maps held after the page lock.
pub(crate) fn kill_retire_lock_table_page(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, target: RwLockProcessPtr, iommu: bool, table: RwLockPageTableRoot,
    scan: StructureScan, page_ptr: PagePtr,
) -> (ret: (Tracked<LockPerm>, Tracked<LockPerm>, RwLockContainerPtr, RwLockPageAllocatorPtr, Ghost<LocalContext>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        held_locks_order_below(old(krnl), old(lctx), PAGE_TABLE_LOCK_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        old(lctx).process_lock_map().dom().contains(target),
        old(krnl).prc_mp.spec_index(target).view().zombie,
        page_ptr_valid(page_ptr),
        scan.spec_table_page() == Some(page_ptr),
        !iommu ==> {
            &&& old(krnl).prc_mp.spec_index(target).view().pagetable == table
            &&& old(krnl).pt_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), table, TypedLockMode::Write)
            &&& old(lctx).pagetable_lock_map().dom() == set![table]
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).spec_structure_scan_wf(scan)
            &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present()
        },
        iommu ==> {
            &&& old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(table)
            &&& old(krnl).it_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), table, TypedLockMode::Write)
            &&& old(krnl).it_mp.spec_index(table).view().spec_structure_scan_wf(scan)
        },
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
        ret.4.view().thread_id() == old(lctx).thread_id(),
        !old(lctx).page_lock_map().dom().contains(page_ptr2page_index(page_ptr)),
        typed_lock_maps_inserted(old(lctx), &ret.4.view(), KernelObjId::Page(page_ptr2page_index(page_ptr)), ret.4.view().page_lock_map()[page_ptr2page_index(page_ptr)]),
        !ret.4.view().allocator_cache_4k_lock_map().dom().contains((ret.3, cpu_id)),
        typed_lock_maps_inserted(&ret.4.view(), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ4k, ret.3, cpu_id), final(lctx).allocator_cache_4k_lock_map()[(ret.3, cpu_id)]),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (ret.3, cpu_id), TypedLockMode::Write),
        ret.0.view().state() is WriteLock,
        ret.0.view().thread_id() == final(lctx).thread_id(),
        ret.0.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).allc_4k_mp.spec_index(ret.3).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view(),
        ret.2 == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container,
        final(krnl).ctn_mp.dom().contains(ret.2),
        final(krnl).ctn_mp.spec_index(ret.2).view_rodata().view().allocator_ptr_4k == ret.3,
        final(krnl).allc_4k_mp.dom().contains(ret.3),
        final(krnl).allc_4k_mp.spec_index(ret.3).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        iommu ==> held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        !iommu ==> {
            &&& final(krnl).pt_mp.dom().contains(table)
            &&& final(krnl).pt_mp.spec_index(table).locking_thread() == old(krnl).pt_mp.spec_index(table).locking_thread()
            &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), table) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table)
        },
{
    let page_index = page_ptr2page_index(page_ptr);
    let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        krnl.prc_mp.typed_lock_map_aligned_held_in_dom(lctx.process_lock_map(), lctx.thread_id());
        kernel_endpoint_nonlock_fields_unchanged_for_equal(steps.snapshot_k().ep_mp, krnl.ep_mp); kernel_lock_states_unchanged_except_tables_of_implies_u_eq(&steps.snapshot_k(), &*krnl, Some(target));
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        page_array_wf_map(krnl.pg_arr);
        page_array_wf_at(krnl.pg_arr, page_index);
    }
    let owner = krnl.pg_arr.borrow_typed(page_index, Ghost(lctx.page_lock_map()), Tracked(&*lctx), Tracked(&page_perm)).owning_container;
    proof {
        assert(krnl.ctn_mp.dom().contains(owner)) by { container_page_owner_backward_at(krnl.ctn_mp, krnl.pg_arr, page_index); };
        container_perms_wf_at(krnl.ctn_mp, owner);
    }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_4k;
    proof { container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); }
    let ghost page_lctx = *lctx;
    let Tracked(cache_perm) = kill_retire_lock_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), allocator_ptr, cpu_id, 1, Ghost(page_index));
    proof {
        assert(old(lctx).page_lock_map() =~= page_lctx.page_lock_map().remove(page_index));
        if !iommu {
            assert(whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), table) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), table)) by {
                old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), table);
                pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), table); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), table);
            };
        }
    }
    (Tracked(page_perm), Tracked(cache_perm), owner, allocator_ptr, Ghost(page_lctx))
}
} // verus!
