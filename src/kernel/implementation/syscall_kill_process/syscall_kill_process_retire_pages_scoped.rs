use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::{KillScope, kill_scope_progress};
use super::syscall_kill_process_retire_pages::kill_retire_lock_cache;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_spec::kill_retire_table_page_scoped_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_eof::kill_retire_table_page_scoped_eof;

verus! {
/// Retire the table page `page_ptr` that `scan` names from the write-held table `table` of the zombie `target` (its
/// write-held IOMMU table when `iommu`) to shard `cpu_id` of the 4K allocator of its owner, the target's container, whose
/// quota grows by one in one step that extends the kill's partial trace; the page, cache and quota locks taken for it
/// are released.
pub(crate) fn kill_retire_next_table_page_scoped(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, iommu: bool, table: RwLockPageTableRoot, scan: StructureScan, page_ptr: PagePtr, Tracked(table_perm): Tracked<&LockPerm>,
    Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        held_locks_order_below(old(krnl), old(lctx), PAGETABLE_PAGE_MAJOR),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        index_valid(NUM_CPUS, cpu_id),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), target, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, KillStage::Retire),
        scope matches KillScope::Container { container } ==> old(krnl).ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(old(lctx).container_lock_map(), container, TypedLockMode::Write),
        old(krnl).prc_mp.spec_index(target).view().zombie,
        page_ptr_valid(page_ptr),
        scan.spec_table_page() == Some(page_ptr),
        table_perm.state() is WriteLock,
        table_perm.thread_id() == old(lctx).thread_id(),
        !iommu ==> {
            &&& old(krnl).prc_mp.spec_index(target).view().pagetable == table
            &&& old(krnl).pt_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).pt_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& old(krnl).pt_mp.spec_index(table).view().spec_structure_scan_wf(scan)
        },
        iommu ==> {
            &&& old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(table)
            &&& old(krnl).it_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).it_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& old(krnl).it_mp.spec_index(table).view().spec_structure_scan_wf(scan)
        },
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        !iommu ==> old(krnl).pt_mp.spec_index(table).view().page_closure().contains(page_ptr)
            && final(krnl).pt_mp.spec_index(table).view().page_closure() == old(krnl).pt_mp.spec_index(table).view().page_closure().remove(page_ptr),
        iommu ==> old(krnl).it_mp.spec_index(table).view().page_closure().contains(page_ptr)
            && final(krnl).it_mp.spec_index(table).view().page_closure() == old(krnl).it_mp.spec_index(table).view().page_closure().remove(page_ptr),
        iommu ==> held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        !iommu ==> held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
        !iommu ==> {
            &&& final(krnl).pt_mp.spec_index(table).locking_thread() == old(krnl).pt_mp.spec_index(table).locking_thread()
            &&& old(krnl).pt_mp.spec_index(table).view().leaves_present() ==> final(krnl).pt_mp.spec_index(table).view().leaves_present()
        },
        iommu ==> {
            &&& final(krnl).it_mp.spec_index(table).locking_thread() == old(krnl).it_mp.spec_index(table).locking_thread()
            &&& old(krnl).it_mp.spec_index(table).view().leaves_present() ==> final(krnl).it_mp.spec_index(table).view().leaves_present()
        },
{
    let ghost origin = krnl.prc_mp.spec_index(target).view_rodata().view().owning_container;
    let page_index = page_ptr2page_index(page_ptr);
    let Tracked(page_perm) = krnl.wlock_page(page_index, Tracked(&mut *lctx));
    let ghost held_lctx = *lctx;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_thread_write_held_section_implies_u_eq(&steps.snapshot_k(), &*krnl, old(lctx), &*lctx, thread_ptr);
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
    let ghost cache_lctx = *lctx;
    let Tracked(cache_perm) = kill_retire_lock_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), allocator_ptr, cpu_id, 1, Ghost(page_index));
    let ghost snap = *krnl;
    let ghost snap_lctx = *lctx;
    let ghost before = steps.view();
    proof {
        assert(held_lctx.page_lock_map().dom().contains(page_index) && held_lctx.process_lock_map().dom().contains(target));
        assert(cache_lctx.page_lock_map().dom().contains(page_index) && cache_lctx.process_lock_map().dom().contains(target));
        process_perms_wf_map(krnl.prc_mp); process_perms_wf_at(krnl.prc_mp, target);
        if iommu {
            process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target);
            pagetable_pages_wf_closure_entry_at(krnl.it_mp, krnl.pg_arr, table, page_ptr);
        } else {
            process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target);
            pagetable_pages_wf_closure_entry_at(krnl.pt_mp, krnl.pg_arr, table, page_ptr);
        }
        assert(owner == origin) by { process_kernel_pages_owner_wf_at(krnl.pg_arr, krnl.prc_mp, krnl.pt_mp, krnl.it_mp, page_index); };
    }
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    kill_retire_table_page_scoped_to_cache(krnl, Tracked(&mut *lctx), iommu, table, scan, page_ptr, owner, allocator_ptr, cpu_id, Tracked(table_perm), Tracked(&page_perm),
        Tracked(&cache_perm), Tracked(&quota_perm));
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(lctx.page_lock_map() =~= old(lctx).page_lock_map() && lctx.allocator_cache_4k_lock_map() =~= old(lctx).allocator_cache_4k_lock_map()
            && lctx.allocator_quota_4k_lock_map() =~= old(lctx).allocator_quota_4k_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        kernel_page_freed_to_owner_quota_implies_u_step(&snap, &*krnl, iommu, table, owner, allocator_ptr, origin);
        let post_u = kernel_k_to_kernel_u(*krnl);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
        kill_trace_from_scoped_credit(&*steps, before, start, pre, post_u, &snap, &snap_lctx, cpu_id, ctx, process_ptr, thread_ptr, target, KillStage::Retire, scope);
    }
}

/// Unlink the table page `page_ptr` that `scan` names from the write-held table `table` of a zombie (its IOMMU table when
/// `iommu`) and return it through the write-held cache shard `cpu_id` of the 4K allocator `allocator_ptr` of its owner
/// `owner`, crediting that allocator's write-held quota by one.
pub(crate) fn kill_retire_table_page_scoped_to_cache(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, iommu: bool, table: RwLockPageTableRoot, scan: StructureScan, page_ptr: PagePtr, owner: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr, cpu_id: CpuId, Tracked(table_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<&LockPerm>, Tracked(cache_perm): Tracked<&LockPerm>,
    Tracked(quota_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(page_ptr),
        scan.spec_table_page() == Some(page_ptr),
        table_perm.state() is WriteLock,
        table_perm.thread_id() == old(lctx).thread_id(),
        !iommu ==> {
            &&& old(krnl).pt_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).pt_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& old(krnl).pt_mp.spec_index(table).view().spec_structure_scan_wf(scan)
        },
        iommu ==> {
            &&& old(krnl).it_mp.dom().contains(table)
            &&& typed_lock_map_contains_mode(old(lctx).iommu_table_lock_map(), table, TypedLockMode::Write)
            &&& table_perm.lock_id() == old(krnl).it_mp.spec_index(table).locking_thread()->Write_lock_id
            &&& old(krnl).it_mp.spec_index(table).view().spec_structure_scan_wf(scan)
        },
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().state == (PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: table, table_type: if iommu { IOMMU_TYPE } else { PT_TYPE } } }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        old(krnl).allc_4k_mp.dom().contains(allocator_ptr),
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
        typed_lock_map_contains_mode(old(lctx).allocator_cache_4k_lock_map(), (allocator_ptr, cpu_id), TypedLockMode::Write),
        cache_perm.state() is WriteLock,
        cache_perm.thread_id() == old(lctx).thread_id(),
        cache_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_perm.state() is WriteLock,
        quota_perm.thread_id() == old(lctx).thread_id(),
        quota_perm.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Page(page_ptr2page_index(page_ptr)),
            TypedHeldLock { lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), mode: TypedLockMode::Write }),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, it_mp: final(krnl).it_mp, pg_arr: final(krnl).pg_arr, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        !iommu ==> {
            &&& final(krnl).it_mp == old(krnl).it_mp
            &&& final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, table)
            &&& final(krnl).pt_mp.spec_index(table).locking_thread() == old(krnl).pt_mp.spec_index(table).locking_thread()
            &&& old(krnl).pt_mp.spec_index(table).view().leaves_present() ==> final(krnl).pt_mp.spec_index(table).view().leaves_present()
            &&& pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, table, old(krnl).pt_mp.spec_index(table).view())
                ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, table, final(krnl).pt_mp.spec_index(table).view())
        },
        iommu ==> {
            &&& final(krnl).pt_mp == old(krnl).pt_mp
            &&& final(krnl).it_mp.unchanged_except(&old(krnl).it_mp, table)
            &&& final(krnl).it_mp.spec_index(table).locking_thread() == old(krnl).it_mp.spec_index(table).locking_thread()
            &&& old(krnl).it_mp.spec_index(table).view().leaves_present() ==> final(krnl).it_mp.spec_index(table).view().leaves_present()
        },
        !iommu ==> old(krnl).pt_mp.spec_index(table).view().page_closure().contains(page_ptr)
            && final(krnl).pt_mp.spec_index(table).view().page_closure() == old(krnl).pt_mp.spec_index(table).view().page_closure().remove(page_ptr),
        iommu ==> old(krnl).it_mp.spec_index(table).view().page_closure().contains(page_ptr)
            && final(krnl).it_mp.spec_index(table).view().page_closure() == old(krnl).it_mp.spec_index(table).view().page_closure().remove(page_ptr),
        final(krnl).pg_arr.entries_unchanged_except(&old(krnl).pg_arr, page_ptr2page_index(page_ptr)),
        final(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread(),
        final(krnl).allc_4k_mp.dom() == old(krnl).allc_4k_mp.dom(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().view() + 1,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
{
    let page_index = page_ptr2page_index(page_ptr);
    proof {
        page_array_wf_at(krnl.pg_arr, page_index);
        allocator_perms_wf_map(krnl.allc_4k_mp);
        allocator_perms_wf_at(krnl.allc_4k_mp, allocator_ptr);
        assert(!krnl.allc_4k_mp.spec_index(allocator_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(page_ptr)) by { container_allocator_free_4k_page_wf_cache_at(krnl.allc_4k_mp, krnl.pg_arr, allocator_ptr, cpu_id, page_ptr); };
        lemma_container_allocator_4k_quota_bounded(&*krnl, owner);
    }
    let Tracked(page_map_perm) = if iommu {
        iommu_table_map_remove_table_page(&mut krnl.it_mp, table, scan, Tracked(&mut *lctx), Tracked(table_perm))
    } else {
        pagetable_map_remove_table_page(&mut krnl.pt_mp, table, scan, Tracked(&mut *lctx), Tracked(table_perm))
    };
    let Tracked(page_4k_perm) = page_map_to_page_perm(page_ptr, Tracked(page_map_perm));
    let ghost old_page_lock_id = krnl.pg_arr.lock_id_by_index(page_index);
    let (node_addr, node_perm) = page_array_retire_kernel_object_4k_to_cache(&mut krnl.pg_arr, page_index, Tracked(page_4k_perm), allocator_ptr, cpu_id, Tracked(&*lctx), Tracked(page_perm));
    proof { lctx.update_lock_id(KernelObjId::Page(page_index), old_page_lock_id, krnl.pg_arr.lock_id_by_index(page_index)); }
    krnl.allc_4k_mp.push_cache_page_typed(allocator_ptr, cpu_id, node_addr, node_perm, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
        Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(cache_perm));
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()),
            Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), Tracked(quota_perm));
        quota.value = quota.value + 1;
    }
    proof {
        assert(kill_retire_table_page_scoped_eof_transition_framing(*old(krnl), *krnl, iommu, table, page_ptr, allocator_ptr, cpu_id, node_addr)) by { reveal(kill_retire_table_page_scoped_eof_transition_framing); };
        kill_retire_table_page_scoped_eof(*old(krnl), *krnl, iommu, table, page_ptr, owner, allocator_ptr, cpu_id, node_addr);
    }
}
} // verus!
