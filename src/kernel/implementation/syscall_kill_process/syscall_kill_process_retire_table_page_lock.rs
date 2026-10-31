use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_retire_pages::kill_retire_lock_cache;

verus! {
/// Write-lock what retiring the table page `page_ptr` that `scan` names from the write-held table `table` of the zombie
/// `target` (its write-held IOMMU table when `iommu`) takes: the L1 window above an L1 page, then the page, and, after a
/// step boundary the projection does not show, shard `cpu_id` of the 4K allocator of the page's owner. Returns the
/// window, page, and cache permissions, the owner and its 4K allocator, and the lock maps held after the window lock and
/// after the page lock.
pub(crate) fn kill_retire_lock_table_page(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, target: RwLockProcessPtr, iommu: bool,
    table: RwLockPageTableRoot, scan: StructureScan, page_ptr: PagePtr, Tracked(table_perm): Tracked<&LockPerm>,
) -> (ret: (Tracked<Option<LockPerm>>, Tracked<LockPerm>, Tracked<LockPerm>, RwLockContainerPtr, RwLockPageAllocatorPtr, Ghost<LocalContext>, Ghost<LocalContext>))
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
        table_perm.state() is WriteLock,
        table_perm.thread_id() == old(lctx).thread_id(),
        !iommu ==> {
            &&& old(krnl).prc_mp.spec_index(target).view().pagetable == table
            &&& old(krnl).pt_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), table, TypedLockMode::Write)
            &&& old(lctx).pagetable_lock_map().dom() == set![table]
            &&& table_perm.lock_id() == old(krnl).pt_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).spec_structure_scan_wf(scan)
            &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).leaves_present()
        },
        iommu ==> {
            &&& old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(table)
            &&& old(krnl).it_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).it_mp.spec_index(table).locking_thread()->Write_lock_id
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
        ret.5.view().thread_id() == old(lctx).thread_id(),
        !iommu && scan is L1 ==> typed_lock_maps_inserted(old(lctx), &ret.5.view(), KernelObjId::PageTableWindow(table, WindowVa { va: spec_index2va((scan->L1_l4i, scan->L1_l3i, scan->L1_l2i, 0)) }),
            ret.5.view().pagetable_window_lock_map()[(table, WindowVa { va: spec_index2va((scan->L1_l4i, scan->L1_l3i, scan->L1_l2i, 0)) })]),
        !(!iommu && scan is L1) ==> typed_lock_maps_unchanged(old(lctx), &ret.5.view()),
        !ret.5.view().page_lock_map().dom().contains(page_ptr2page_index(page_ptr)),
        typed_lock_maps_inserted(&ret.5.view(), &ret.6.view(), KernelObjId::Page(page_ptr2page_index(page_ptr)), ret.6.view().page_lock_map()[page_ptr2page_index(page_ptr)]),
        !ret.6.view().allocator_cache_4k_lock_map().dom().contains((ret.4, cpu_id)),
        typed_lock_maps_inserted(&ret.6.view(), final(lctx), KernelObjId::AllocatorCache(PageSize::SZ4k, ret.4, cpu_id), final(lctx).allocator_cache_4k_lock_map()[(ret.4, cpu_id)]),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).allocator_cache_4k_lock_map(), (ret.4, cpu_id), TypedLockMode::Write),
        !iommu && scan is L1 ==> typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (table, WindowVa { va: spec_index2va((scan->L1_l4i, scan->L1_l3i, scan->L1_l2i, 0)) }),
            TypedLockMode::Write),
        !iommu && scan is L2 ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
        ret.1.view().state() is WriteLock,
        ret.1.view().thread_id() == final(lctx).thread_id(),
        ret.1.view().lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        ret.2.view().state() is WriteLock,
        ret.2.view().thread_id() == final(lctx).thread_id(),
        ret.2.view().lock_id() == final(krnl).allc_4k_mp.spec_index(ret.4).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        !iommu && scan is L1 ==> {
            &&& ret.0.view() is Some
            &&& ret.0.view()->Some_0.state() is WriteLock
            &&& ret.0.view()->Some_0.thread_id() == old(lctx).thread_id()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).lower.l2_owner(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).window_l2_page(scan->L1_l4i, scan->L1_l3i), scan->L1_l2i)
                == (SpinLockState::Some { thread_id: ret.0.view()->Some_0.thread_id(), lock_id: ret.0.view()->Some_0.lock_id() })
        },
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view(),
        ret.3 == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container,
        final(krnl).ctn_mp.dom().contains(ret.3),
        final(krnl).ctn_mp.spec_index(ret.3).view_rodata().view().allocator_ptr_4k == ret.4,
        final(krnl).allc_4k_mp.dom().contains(ret.4),
        final(krnl).allc_4k_mp.spec_index(ret.4).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
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
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).spec_structure_scan_wf(scan)
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).leaves_present()
            &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), table).page_closure() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), table).page_closure()
        },
{
    let page_index = page_ptr2page_index(page_ptr);
    let Tracked(window_perm) = if iommu {
        Tracked(None)
    } else {
        match scan {
            StructureScan::L1 { l4i, l3i, l2i, .. } => {
                proof {
                    pagetable_perms_wf_at(krnl.pt_mp, table); krnl.default_pagetable_wf_at(table);
                    assert(spec_va_2m_valid(spec_index2va((l4i, l3i, l2i, 0usize)))) by (bit_vector) requires KERNEL_MEM_END_L4INDEX <= l4i < 512, l3i < 512, l2i < 512;
                }
                let Tracked(perm) = krnl.lock_pagetable_window(table, l4i, l3i, l2i, Tracked(table_perm), Tracked(&mut *lctx));
                Tracked(Some(perm))
            },
            _ => Tracked(None),
        }
    };
    let ghost locked_k = *krnl;
    let ghost locked_lctx = *lctx;
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
            assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), table) == pagetable_c(locked_k.pt_mp, locked_k.pt_lower.view(), table)) by {
                locked_k.pt_mp.typed_lock_map_aligned_write_at(locked_lctx.pagetable_lock_map(), locked_lctx.thread_id(), table);
                pagetable_lower_backup_wf_at(locked_k.pt_mp, locked_k.pt_lower.view(), table); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), table);
            };
        }
    }
    (Tracked(window_perm), Tracked(page_perm), Tracked(cache_perm), owner, allocator_ptr, Ghost(locked_lctx), Ghost(page_lctx))
}
} // verus!
