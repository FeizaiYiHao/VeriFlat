use vstd::prelude::*;
use crate::*;
use super::syscall_kill_process_spec::*;
use super::syscall_kill_process_trace::*;
use super::syscall_kill_process_walk::KillScope;
use super::syscall_kill_process_retire_pages::kill_retire_lock_cache;
use super::syscall_kill_process_reclaim_scoped::{kill_reclaim_last_4k_mapping_scoped_to_cache, kill_reclaim_last_iommu_4k_mapping_scoped_to_cache};
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk::kill_scope_progress;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_reclaim_scoped_spec::*;

verus! {
/// Free the page `page_ptr` whose last mapping is the hidden 4K leaf at `va` of the write-held page table `pagetable` of
/// the target: return it through the cache shard `cpu_id` of its owner `owner`'s 4K allocator, credit that allocator's
/// quota by one, and release the write-held page, in one step that extends the kill's partial trace. The killer held
/// `entry_lctx` before it write-locked the page.
pub(crate) fn kill_reclaim_last_4k_mapping_scoped(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, pagetable: RwLockPageTableRoot, va: VAddr, page_ptr: PagePtr, owner: RwLockContainerPtr,
    Tracked(pagetable_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<LockPerm>, Tracked(window_perm): Tracked<LockPerm>, Ghost(stage): Ghost<KillStage>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
    Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>, Ghost(entry_lctx): Ghost<LocalContext>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, pg_arr: old(krnl).pg_arr, ..old(steps).snapshot_k() }),
        old(krnl).pt_mp.unchanged_except(&old(steps).snapshot_k().pt_mp, pagetable),
        old(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(steps).snapshot_k().pt_mp.spec_index(pagetable).locking_thread(),
        old(krnl).pt_lower.view() =~= old(steps).snapshot_k().pt_lower.view().insert(pagetable, old(krnl).pt_lower.view().spec_index(pagetable)),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_4k(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), pagetable).mapping_1g(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).pg_arr.unchanged_except(&old(steps).snapshot_k().pg_arr, page_ptr2page_index(page_ptr)),
        !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(page_ptr)),
        lock_ensures(&entry_lctx, old(lctx), old(steps).snapshot_k().pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))),
        entry_lctx.page_lock_map().dom().is_empty(),
        held_locks_order_below(&old(steps).snapshot_k(), &entry_lctx, ALLOCATOR_CACHE_4K_MAJOR),
        entry_lctx.scheduler_lock_map().dom().is_empty(),
        entry_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
        entry_lctx.cpu_set_lock_map().dom().is_empty(),
        entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_4k_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_2m_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_1g_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger entry_lctx.cpu_lock_map().dom().contains(held_cpu_id)]
            entry_lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), target, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().pagetable == pagetable,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, stage),
        scope matches KillScope::Container { container } ==> old(krnl).ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(entry_lctx.container_lock_map(), container, TypedLockMode::Write),
        scope is Subtree ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        scope matches KillScope::Container { container } ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container
            && old(krnl).ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        old(krnl).pt_mp.dom().contains(pagetable),
        va_4k_valid(va),
        old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end <= spec_va2index(va).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().dom().contains(va),
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).present,
        !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus.dom().contains((pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va), spec_v2l3index(va)), spec_v2l2index(va))),
        typed_lock_map_contains_mode(entry_lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.state() is WriteLock,
        pagetable_perm.thread_id() == entry_lctx.thread_id(),
        pagetable_perm.lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(entry_lctx.pagetable_window_lock_map(), (pagetable, WindowVa { va: spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0)) }), TypedLockMode::Write),
        window_perm.state() is WriteLock,
        window_perm.thread_id() == entry_lctx.thread_id(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).window_l2_page(spec_v2l4index(va),
            spec_v2l3index(va))).lock_perm_match(spec_v2l2index(va), &window_perm),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().spec_index(va).addr == page_ptr,
        page_ptr_valid(page_ptr),
        !(old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_removed(&entry_lctx, final(lctx), KernelObjId::PageTableWindow(pagetable, WindowVa { va: spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0)) })),
        final(lctx).cpu_id() == entry_lctx.cpu_id(),
        final(lctx).thread_id() == entry_lctx.thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> final(krnl).cpu_published[entry_lctx.cpu_id() as int].view() == old(krnl).cpu_published[entry_lctx.cpu_id() as int].view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, &entry_lctx),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, &entry_lctx),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, &entry_lctx),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, &entry_lctx),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, &entry_lctx),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_4k().remove(va),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).mapping_1g(),
        final(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end == old(krnl).pt_mp.spec_index(pagetable).view().kernel_l4_end,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.window_stale_cpus,
{
    let page_index = page_ptr2page_index(page_ptr);
    let ghost origin = krnl.prc_mp.spec_index(target).view_rodata().view().owning_container;
    proof {
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target);
        page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index);
    }
    let ghost held_lctx = *lctx;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        assert(held_lctx.page_lock_map().dom().contains(page_index) && krnl.ctn_mp.dom().contains(owner));
        container_perms_wf_at(krnl.ctn_mp, owner); container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner);
    }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_4k;
    let ghost cache_lctx = *lctx;
    let Tracked(cache_perm) = kill_retire_lock_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), allocator_ptr, cpu_id, 1, Ghost(page_index));
    let ghost snap = *krnl;
    let ghost snap_lctx = *lctx;
    proof {
        assert(held_lctx.page_lock_map().dom().contains(page_index) && held_lctx.pagetable_lock_map().dom().contains(pagetable) && held_lctx.process_lock_map().dom().contains(target));
        assert(cache_lctx.page_lock_map().dom().contains(page_index) && cache_lctx.pagetable_lock_map().dom().contains(pagetable) && cache_lctx.process_lock_map().dom().contains(target));
        assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable)) by {
            old(krnl).pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
            pagetable_lower_backup_wf_at(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable); pagetable_lower_backup_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
        };
        mapped_4k_page_pagetable_wf_pagetable_at(krnl.pt_mp, krnl.pt_lower.view(), krnl.pg_arr, pagetable, va);
        assert(krnl.pg_arr.spec_index(page_index).view().view().mappings().contains((pagetable, va)) && krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k);
        pagetable_perms_wf_at(krnl.pt_mp, pagetable); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target);
        container_process_page_pagetable_wf_page_at(krnl.ctn_mp, krnl.prc_mp, krnl.pt_mp, krnl.pg_arr, page_index, pagetable, va);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target);
        assert(krnl.ctn_mp.dom().contains(origin) && krnl.ctn_mp.dom().contains(owner));
        container_subtree_set_exclusive_at(krnl.rt_ctn, krnl.ctn_mp, owner, origin);
    }
    let ghost before = steps.view();
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    kill_reclaim_last_4k_mapping_scoped_to_cache(krnl, Tracked(&mut *lctx), pagetable, va, page_ptr, owner, allocator_ptr, cpu_id, Tracked(pagetable_perm), Tracked(&page_perm),
        Tracked(&cache_perm), Tracked(&quota_perm));
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
    let window = va2index(va);
    krnl.unlock_pagetable_window(pagetable, window.0, window.1, window.2, Tracked(pagetable_perm), Tracked(&mut *lctx), Tracked(window_perm));
    proof {
        assert(lctx.page_lock_map() =~= entry_lctx.page_lock_map() && lctx.allocator_cache_4k_lock_map() =~= entry_lctx.allocator_cache_4k_lock_map()
            && lctx.allocator_quota_4k_lock_map() =~= entry_lctx.allocator_quota_4k_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        kernel_page_freed_to_owner_quota_implies_u_step(&snap, &*krnl, false, pagetable, owner, allocator_ptr, origin);
        let post_u = kernel_k_to_kernel_u(*krnl);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
        kill_trace_from_scoped_credit(&*steps, before, start, pre, post_u, &snap, &snap_lctx, cpu_id, ctx, process_ptr, thread_ptr, target, stage, scope);
    }
}

/// Free the page `page_ptr` whose last mapping is the hidden 4K leaf at `indices` of the write-held IOMMU table
/// `iommu_table` of the target: return it through the cache shard `cpu_id` of its owner `owner`'s 4K allocator, credit
/// that allocator's quota by one, and release the write-held page, in one step that extends the kill's partial trace. The
/// killer held `entry_lctx` before it write-locked the page.
pub(crate) fn kill_reclaim_last_iommu_4k_mapping_scoped(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, cpu_id: CpuId, process_ptr: RwLockProcessPtr,
    thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr, iommu_table: RwLockPageTableRoot, indices: (L4Index, L3Index, L2Index, L1Index), page_ptr: PagePtr,
    l1_ptr: PageMapPtr, owner: RwLockContainerPtr, Tracked(iommu_perm): Tracked<&LockPerm>, Tracked(page_perm): Tracked<LockPerm>, Ghost(stage): Ghost<KillStage>, Ghost(start): Ghost<int>,
    Ghost(pre): Ghost<KernelU>, Ghost(scope): Ghost<KillScope>, Ghost(ctx): Ghost<KillTraceCtx>, Ghost(entry_lctx): Ghost<LocalContext>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        *old(krnl) == (KernelK { pg_arr: old(krnl).pg_arr, ..old(steps).snapshot_k() }),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).pg_arr.unchanged_except(&old(steps).snapshot_k().pg_arr, page_ptr2page_index(page_ptr)),
        !entry_lctx.page_lock_map().dom().contains(page_ptr2page_index(page_ptr)),
        lock_ensures(&entry_lctx, old(lctx), old(steps).snapshot_k().pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)), KernelObjId::Page(page_ptr2page_index(page_ptr))),
        old(steps).snapshot_k().pg_arr.lock_id_by_index(page_ptr2page_index(page_ptr)).major == MAPPED_PAGE_LOCK_MAJOR,
        entry_lctx.page_lock_map().dom().is_empty(),
        held_locks_order_below(&old(steps).snapshot_k(), &entry_lctx, ALLOCATOR_CACHE_4K_MAJOR),
        entry_lctx.scheduler_lock_map().dom().is_empty(),
        entry_lctx.cpu_offline_flag_lock_map().dom().is_empty(),
        entry_lctx.cpu_set_lock_map().dom().is_empty(),
        entry_lctx.pcid_needflush_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_4k_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_2m_lock_map().dom().is_empty(),
        entry_lctx.allocator_quota_1g_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger entry_lctx.cpu_lock_map().dom().contains(held_cpu_id)]
            entry_lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        0 <= start <= old(steps).view().len(),
        kill_partial_trace(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, cpu_id),
        typed_lock_map_contains_mode(entry_lctx.cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), process_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(entry_lctx.process_lock_map(), target, TypedLockMode::Write),
        old(krnl).prc_mp.dom().contains(target),
        old(krnl).prc_mp.spec_index(target).being_killed(),
        old(krnl).prc_mp.spec_index(target).view().iommu_table == Some(iommu_table),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().syscall_progress.view() == kill_scope_progress(scope, target, stage),
        scope matches KillScope::Container { container } ==> old(krnl).ctn_mp.dom().contains(container) && typed_lock_map_contains_mode(entry_lctx.container_lock_map(), container, TypedLockMode::Write),
        scope is Subtree ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container,
        scope matches KillScope::Container { container } ==> old(krnl).prc_mp.spec_index(target).view_rodata().view().owning_container == container
            && old(krnl).ctn_mp.spec_index(container).view_ghost().uppertree_seq.view().contains(old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().owning_container),
        old(krnl).it_mp.dom().contains(iommu_table),
        pei_valid(indices.0),
        pei_valid(indices.1),
        pei_valid(indices.2),
        pei_valid(indices.3),
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().dom().contains(spec_index2va(indices)),
        !old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).present,
        typed_lock_map_contains_mode(entry_lctx.iommu_table_lock_map(), iommu_table, TypedLockMode::Write),
        iommu_perm.state() is WriteLock,
        iommu_perm.thread_id() == entry_lctx.thread_id(),
        iommu_perm.lock_id() == old(krnl).it_mp.spec_index(iommu_table).locking_thread()->Write_lock_id,
        old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().spec_index(spec_index2va(indices)).addr == page_ptr,
        old(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2) is Some,
        old(krnl).it_mp.spec_index(iommu_table).view().spec_resolve_mapping_l2(indices.0, indices.1, indices.2)->0.addr == l1_ptr,
        page_ptr_valid(page_ptr),
        !(old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().ref_count > 1 || old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().is_io_page),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().view().owning_container == owner,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(page_ptr), TypedLockMode::Write),
        page_perm.state() is WriteLock,
        page_perm.thread_id() == old(lctx).thread_id(),
        page_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_table_tlb_entries_present(old(krnl).iommu_tlb, old(krnl).irt.view(), old(krnl).it_mp, iommu_table),
    ensures
        final(krnl).inv(),
        iommu_table_tlb_entries_present(final(krnl).iommu_tlb, final(krnl).irt.view(), final(krnl).it_mp, iommu_table),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(&entry_lctx, final(lctx)),
        final(lctx).cpu_id() == entry_lctx.cpu_id(),
        final(lctx).thread_id() == entry_lctx.thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len(),
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        kill_partial_trace(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, ctx),
        index_valid(NUM_CPUS, entry_lctx.cpu_id()) ==> final(krnl).cpu_published[entry_lctx.cpu_id() as int].view() == old(krnl).cpu_published[entry_lctx.cpu_id() as int].view(),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, &entry_lctx),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, &entry_lctx),
        held_threads_unchanged(old(krnl).thr_mp, final(krnl).thr_mp, &entry_lctx),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, &entry_lctx),
        forall|p: RwLockPageTableRoot| #![trigger entry_lctx.pagetable_lock_map().dom().contains(p)] typed_lock_map_contains_mode(entry_lctx.pagetable_lock_map(), p, TypedLockMode::Write)
            ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), p) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), p),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, &entry_lctx),
        final(krnl).it_mp.dom().contains(iommu_table),
        final(krnl).it_mp.spec_index(iommu_table).locking_thread() == old(krnl).it_mp.spec_index(iommu_table).locking_thread(),
        final(krnl).it_mp.spec_index(iommu_table).being_killed() == old(krnl).it_mp.spec_index(iommu_table).being_killed(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_4k() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_4k().remove(spec_index2va(indices)),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_2m() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_2m(),
        final(krnl).it_mp.spec_index(iommu_table).view().mapping_1g() == old(krnl).it_mp.spec_index(iommu_table).view().mapping_1g(),
        final(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end == old(krnl).it_mp.spec_index(iommu_table).view().kernel_l4_end,
        final(krnl).it_mp.spec_index(iommu_table).view().did == old(krnl).it_mp.spec_index(iommu_table).view().did,
{
    let page_index = page_ptr2page_index(page_ptr);
    let ghost origin = krnl.prc_mp.spec_index(target).view_rodata().view().owning_container;
    let ghost iova = spec_index2va(indices);
    proof {
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target);
        page_array_wf_map(krnl.pg_arr); page_array_wf_at(krnl.pg_arr, page_index);
    }
    let ghost held_lctx = *lctx;
    proof {
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&steps.snapshot_k(), &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        assert(held_lctx.page_lock_map().dom().contains(page_index) && krnl.ctn_mp.dom().contains(owner));
        container_perms_wf_at(krnl.ctn_mp, owner); container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner);
    }
    let allocator_ptr = krnl.ctn_mp.borrow_rodata(owner).borrow().allocator_ptr_4k;
    let ghost cache_lctx = *lctx;
    let Tracked(cache_perm) = kill_retire_lock_cache(krnl, Tracked(&mut *lctx), Tracked(&mut *steps), allocator_ptr, cpu_id, 1, Ghost(page_index));
    let ghost snap = *krnl;
    let ghost snap_lctx = *lctx;
    proof {
        assert(held_lctx.page_lock_map().dom().contains(page_index) && held_lctx.iommu_table_lock_map().dom().contains(iommu_table) && held_lctx.process_lock_map().dom().contains(target));
        assert(cache_lctx.page_lock_map().dom().contains(page_index) && cache_lctx.iommu_table_lock_map().dom().contains(iommu_table) && cache_lctx.process_lock_map().dom().contains(target));
        page_iommu_table_wf_table_at(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr, iommu_table, iova);
        assert(krnl.pg_arr.spec_index(page_index).view().view().iommu_mappings().contains((iommu_table, iova)) && krnl.pg_arr.spec_index(page_index).view().view().state is Mapped4k);
        iommu_table_perms_wf_map(krnl.it_mp); iommu_table_perms_wf_at(krnl.it_mp, iommu_table); process_iommu_table_match_process_at(krnl.prc_mp, krnl.it_mp, target);
        page_iommu_table_wf_page_owner_at(krnl.ctn_mp, krnl.prc_mp, krnl.it_mp, krnl.pg_arr, page_index, iommu_table, iova);
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, target);
        assert(krnl.ctn_mp.dom().contains(origin) && krnl.ctn_mp.dom().contains(owner));
        container_subtree_set_exclusive_at(krnl.rt_ctn, krnl.ctn_mp, owner, origin);
    }
    let ghost before = steps.view();
    let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
    kill_reclaim_last_iommu_4k_mapping_scoped_to_cache(krnl, Tracked(&mut *lctx), iommu_table, indices, page_ptr, l1_ptr, owner, allocator_ptr, cpu_id, Tracked(iommu_perm), Tracked(&page_perm),
        Tracked(&cache_perm), Tracked(&quota_perm));
    krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
    krnl.wunlock_allocator_cache_4k(allocator_ptr, cpu_id, Tracked(&mut *lctx), Tracked(cache_perm));
    krnl.wunlock_page(page_index, Tracked(&mut *lctx), Tracked(page_perm));
    proof {
        assert(lctx.page_lock_map() =~= entry_lctx.page_lock_map() && lctx.allocator_cache_4k_lock_map() =~= entry_lctx.allocator_cache_4k_lock_map()
            && lctx.allocator_quota_4k_lock_map() =~= entry_lctx.allocator_quota_4k_lock_map());
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&snap, &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        kernel_page_freed_to_owner_quota_implies_u_step(&snap, &*krnl, true, iommu_table, owner, allocator_ptr, origin);
        let post_u = kernel_k_to_kernel_u(*krnl);
        krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
        kill_trace_from_scoped_credit(&*steps, before, start, pre, post_u, &snap, &snap_lctx, cpu_id, ctx, process_ptr, thread_ptr, target, stage, scope);
    }
}

} // verus!
