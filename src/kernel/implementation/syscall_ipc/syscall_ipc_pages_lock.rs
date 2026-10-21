use vstd::prelude::*;
use crate::*;
use super::syscall_ipc_spec::*;
use super::syscall_ipc_trace::*;

verus! {
/// With both page tables of a pages rendezvous held, the source read and the target read or written, and both ranges above the kernel
/// L4 entries: locks every existing 2M window of the source range and of the target range, the table with the lower root first.
fn ipc_pages_lock_pair_windows(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: (Tracked<Map<WindowVa, LockPerm>>, Tracked<Map<WindowVa, LockPerm>>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        source_range.wf(),
        source_range.len > 0,
        target_range.wf(),
        target_range.len > 0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
            old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, if (target_pagetable_lock_perm.state() is WriteLock) { TypedLockMode::Write } else { TypedLockMode::Read }),
        (target_pagetable_lock_perm.state() is WriteLock) ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !(target_pagetable_lock_perm.state() is WriteLock) ==> target_pagetable_lock_perm.state() is ReadLock,
        !(target_pagetable_lock_perm.state() is WriteLock) ==> old(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)]
            old(krnl).pt_mp.dom().contains(p) && p != source_pagetable && p != target_pagetable ==> final(krnl).pt_mp.spec_index(p) == old(krnl).pt_mp.spec_index(p),
        final(krnl).pt_lower.view() =~= old(krnl).pt_lower.view().insert(source_pagetable, final(krnl).pt_lower.view().spec_index(source_pagetable))
            .insert(target_pagetable, final(krnl).pt_lower.view().spec_index(target_pagetable)),
        final(krnl).pt_mp.spec_index(source_pagetable).locking_thread() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(source_pagetable).being_killed() == old(krnl).pt_mp.spec_index(source_pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus,
        final(krnl).pt_mp.spec_index(target_pagetable).locking_thread() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).being_killed() == old(krnl).pt_mp.spec_index(target_pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus,
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && ret.0@.dom().contains(w) || p == target_pagetable && ret.1@.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.0@.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.1@.dom().contains(w),
        forall|w: WindowVa| #![trigger ret.0@.dom().contains(w)] ret.0@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& ret.0@.index(w).state() is WriteLock
                &&& ret.0@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.0@.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger ret.1@.dom().contains(w)] ret.1@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& ret.1@.index(w).state() is WriteLock
                &&& ret.1@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.1@.index(w))
                &&& !(target_pagetable_lock_perm.state() is WriteLock) ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !(target_pagetable_lock_perm.state() is WriteLock) ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
{
    if source_pagetable < target_pagetable {
        let Tracked(source_windows) = krnl.lock_pagetable_range_existing_windows(source_pagetable, source_range, Tracked(source_pagetable_lock_perm), Tracked(&mut *lctx));
        let Tracked(target_windows) = krnl.lock_pagetable_range_existing_windows(target_pagetable, target_range, Tracked(target_pagetable_lock_perm), Tracked(&mut *lctx));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        }
        (Tracked(source_windows), Tracked(target_windows))
    } else {
        let Tracked(target_windows) = krnl.lock_pagetable_range_existing_windows(target_pagetable, target_range, Tracked(target_pagetable_lock_perm), Tracked(&mut *lctx));
        let Tracked(source_windows) = krnl.lock_pagetable_range_existing_windows(source_pagetable, source_range, Tracked(source_pagetable_lock_perm), Tracked(&mut *lctx));
        proof {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
            assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
            assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        }
        (Tracked(source_windows), Tracked(target_windows))
    }
}

/// Releases the existing windows of `root` over `range` while this thread keeps holding every window of `other` in `other_windows`.
fn ipc_pages_unlock_windows_keeping(
    krnl: &mut KernelK, root: RwLockPageTableRoot, range: &VaRange4K, Tracked(big): Tracked<&LockPerm>, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(perms): Tracked<Map<WindowVa, LockPerm>>, Ghost(other): Ghost<RwLockPageTableRoot>, Ghost(other_windows): Ghost<Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(krnl).pt_mp.dom().contains(root),
        range.wf(),
        range.len > 0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).kernel_l4_end() <= spec_va2index(range.start).0,
        big.thread_id() == old(lctx).thread_id(),
        big.state() is WriteLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Write),
        big.state() is WriteLock ==> big.lock_id() == old(krnl).pt_mp.spec_index(root).locking_thread()->Write_lock_id,
        big.state() is ReadLock ==> typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), root, TypedLockMode::Read),
        big.state() is ReadLock ==> old(krnl).pt_mp.spec_index(root).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), big.lock_id()),
        forall|w: WindowVa|
            #![trigger va_range_2m_windows(*range).contains(w)]
            va_range_2m_windows(*range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> perms.dom().contains(w),
        forall|w: WindowVa|
            #![trigger perms.dom().contains(w)]
            perms.dom().contains(w) ==> {
                &&& va_range_2m_windows(*range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (root, w), TypedLockMode::Write)
                &&& perms.index(w).state() is WriteLock
                &&& perms.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &perms.index(w))
                &&& !(big.state() is WriteLock) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).window_leaves_present(w)
                &&& !(big.state() is WriteLock) ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        other != root,
        forall|w: WindowVa| #![trigger other_windows.dom().contains(w)] other_windows.dom().contains(w) ==> old(lctx).pagetable_window_lock_map().dom().contains((other, w)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release || final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        final(krnl).inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, root),
        update_ghost_ensures(old(krnl).pt_mp.spec_index(root), final(krnl).pt_mp.spec_index(root),
            if old(krnl).pt_mp.spec_index(root).wlocked() { final(krnl).pt_lower.view().spec_index(root) } else { old(krnl).pt_mp.spec_index(root).view_ghost() }),
        final(krnl).pt_lower.view() =~= old(krnl).pt_lower.view().insert(root, final(krnl).pt_lower.view().spec_index(root)),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).higher == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).higher,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).lower.l2_perms == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).lower.l2_perms,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).lower.l2_ghost == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).lower.l2_ghost,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).lower.l1_tables == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).lower.l1_tables,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).lower.l1_rev_map == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).lower.l1_rev_map,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).lower.window_stale_cpus,
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), root).page_closure() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), root).page_closure(),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        forall|p: RwLockPageTableRoot, w: WindowVa|
            #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && perms.dom().contains(w))),
        forall|p: RwLockPageTableRoot, w: WindowVa|
            #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
        (forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))] old(lctx).pagetable_window_lock_map().dom().contains((p, w)) ==> p == root && perms.dom().contains(w))
            ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
        forall|w: WindowVa| #![trigger other_windows.dom().contains(w)] other_windows.dom().contains(w) ==> final(lctx).pagetable_window_lock_map().dom().contains((other, w)),
{ krnl.unlock_pagetable_range_existing_windows(root, range, Tracked(big), Tracked(&mut *lctx), Tracked(perms)); }

/// Releases the 2M windows of both ranges that `ipc_pages_lock_pair_windows` locked, leaving both page tables held.
pub(super) fn ipc_pages_unlock_pair_windows(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot,
    Tracked(lctx): Tracked<&mut LocalContext>, Tracked(source_pagetable_lock_perm): Tracked<&LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
    Tracked(source_windows): Tracked<Map<WindowVa, LockPerm>>, Tracked(target_windows): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        source_range.wf(),
        source_range.len > 0,
        target_range.wf(),
        target_range.len > 0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, if (target_pagetable_lock_perm.state() is WriteLock) { TypedLockMode::Write } else { TypedLockMode::Read }),
        (target_pagetable_lock_perm.state() is WriteLock) ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !(target_pagetable_lock_perm.state() is WriteLock) ==> target_pagetable_lock_perm.state() is ReadLock,
        !(target_pagetable_lock_perm.state() is WriteLock) ==> old(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger target_windows.dom().contains(w)] target_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& target_windows.index(w).state() is WriteLock
                &&& target_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &target_windows.index(w))
                &&& !(target_pagetable_lock_perm.state() is WriteLock) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !(target_pagetable_lock_perm.state() is WriteLock) ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release || final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)]
            old(krnl).pt_mp.dom().contains(p) && p != source_pagetable && p != target_pagetable ==> final(krnl).pt_mp.spec_index(p) == old(krnl).pt_mp.spec_index(p),
        final(krnl).pt_lower.view() =~= old(krnl).pt_lower.view().insert(source_pagetable, final(krnl).pt_lower.view().spec_index(source_pagetable))
            .insert(target_pagetable, final(krnl).pt_lower.view().spec_index(target_pagetable)),
        final(krnl).pt_mp.spec_index(source_pagetable).locking_thread() == old(krnl).pt_mp.spec_index(source_pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        final(krnl).pt_mp.spec_index(source_pagetable).being_killed() == old(krnl).pt_mp.spec_index(source_pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus,
        final(krnl).pt_mp.spec_index(target_pagetable).locking_thread() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
        final(krnl).pt_mp.spec_index(target_pagetable).being_killed() == old(krnl).pt_mp.spec_index(target_pagetable).being_killed(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus,
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
{
    ipc_pages_unlock_windows_keeping(
        krnl, source_pagetable, source_range, Tracked(source_pagetable_lock_perm), Tracked(&mut *lctx), Tracked(source_windows), Ghost(target_pagetable), Ghost(target_windows),
    );
    proof { assert(pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable) == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable)); }
    krnl.unlock_pagetable_range_existing_windows(target_pagetable, target_range, Tracked(target_pagetable_lock_perm), Tracked(&mut *lctx), Tracked(target_windows));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
    }
}

/// Whether `range` starts above the kernel L4 entries of `pagetable`, which this thread holds.
fn ipc_pages_range_user(krnl: &KernelK, range: &VaRange4K, pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>, Tracked(pagetable_lock_perm): Tracked<&LockPerm>)
    -> (ret: bool)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        range.wf(),
        krnl.pt_mp.dom().contains(pagetable),
        pagetable_lock_perm.thread_id() == lctx.thread_id(),
        pagetable_lock_perm.state() is WriteLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_lock_perm.state() is WriteLock ==> pagetable_lock_perm.lock_id() == krnl.pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        pagetable_lock_perm.state() is ReadLock ==> typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock ==> krnl.pt_mp.spec_index(pagetable).read_lock_perm_match(&pagetable_lock_perm),
    ensures ret == (pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), pagetable).kernel_l4_end() <= spec_va2index(range.start).0),
{
    proof { assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(pagetable).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); }; }
    let pt = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(pagetable_lock_perm));
    pt.kernel_l4_end <= va2index(range.start).0
}

/// Under the target page table's read lock, reports whether every page of the target range already has its L2 directory entry.
fn ipc_pages_target_l2_present(
    krnl: &KernelK, target_range: &VaRange4K, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&LocalContext>,
    Tracked(target_pagetable_lock_perm): Tracked<&LockPerm>,
) -> (ret: bool)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(target_pagetable),
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), target_pagetable, TypedLockMode::Read),
        target_pagetable_lock_perm.state() is ReadLock,
        target_pagetable_lock_perm.thread_id() == lctx.thread_id(),
        krnl.pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        target_range.wf(),
        target_range.len > 0,
        pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
    ensures
        ret ==> forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
{
    proof {
        assert(krnl.pt_mp.perms_wf() && krnl.pt_mp.spec_index(target_pagetable).inv()) by { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, target_pagetable); };
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable);
        target_range.va_range_lemma();
    }
    let pagetable = krnl.pt_mp.borrow_typed(target_pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), Tracked(target_pagetable_lock_perm));
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(target_pagetable);
    let range_len = target_range.len;
    let mut i: usize = 0;
    while i < range_len
        invariant
            target_range.wf(),
            target_range.len == range_len,
            0 < range_len,
            i <= range_len,
            forall|k: usize| 0 <= k < target_range.len ==> #[trigger] target_range.view().spec_index(k as int) == spec_va_add_range(target_range.start, k),
            (PageTableC { higher: *pagetable, lower: *lower }) == pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).wf(),
            pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
            forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < i ==> {
                let va = target_range.view().spec_index(j);
                pagetable_c(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        decreases range_len - i,
    {
        let va = target_range.index(i);
        let indices = va2index(va);
        proof {
            spec_va_4k_valid_index_roundtrip(va); spec_va_4k_valid_index_roundtrip(target_range.start);
            spec_v2l4index_monotonic(target_range.start, va);
        }
        let (entry, _) = pagetable.resolve_mapping_4k_l2(Tracked(lower), indices.0, indices.1, indices.2);
        if entry.is_none() { return false; }
        i = i + 1;
    }
    true
}

/// Locks both page tables of a pages rendezvous, the source for reading and the target for writing when `write_target` and for reading
/// otherwise, and, when both ranges start above the kernel L4 entries, every existing 2M window of both ranges.
fn ipc_pages_lock_tables_and_windows(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot,
    Tracked(lctx): Tracked<&mut LocalContext>, write_target: bool,
) -> (ret: (bool, bool, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<Map<WindowVa, LockPerm>>, Tracked<Map<WindowVa, LockPerm>>))
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        source_range.wf(),
        source_range.len > 0,
        target_range.wf(),
        target_range.len > 0,
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)]
            old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)]
            old(krnl).pt_mp.dom().contains(p) && p != source_pagetable && p != target_pagetable ==> final(krnl).pt_mp.spec_index(p) == old(krnl).pt_mp.spec_index(p),
        final(krnl).pt_lower.view() =~= old(krnl).pt_lower.view().insert(source_pagetable, final(krnl).pt_lower.view().spec_index(source_pagetable))
            .insert(target_pagetable, final(krnl).pt_lower.view().spec_index(target_pagetable)),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == old(krnl).pt_mp.spec_index(source_pagetable).view(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == old(krnl).pt_mp.spec_index(target_pagetable).view(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g(),
        !(old(krnl).pt_mp.spec_index(source_pagetable).locking_thread() is Write),
        write_target ==> old(krnl).pt_mp.spec_index(target_pagetable).locking_thread() is None,
        !write_target ==> !(old(krnl).pt_mp.spec_index(target_pagetable).locking_thread() is Write),
        final(krnl).pt_mp.spec_index(source_pagetable).locking_thread() == (RwLockState::Read { reader_map: (if old(krnl).pt_mp.spec_index(source_pagetable).locking_thread() is Read
            { old(krnl).pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map } else { Map::empty() }).insert(final(lctx).thread_id(), ret.2@.lock_id()) }),
        !write_target ==> final(krnl).pt_mp.spec_index(target_pagetable).locking_thread() == (RwLockState::Read { reader_map: (if old(krnl).pt_mp.spec_index(target_pagetable).locking_thread() is Read
            { old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map } else { Map::empty() }).insert(final(lctx).thread_id(), ret.3@.lock_id()) }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, if write_target { TypedLockMode::Write } else { TypedLockMode::Read }),
        ret.2@.state() is ReadLock,
        ret.2@.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&ret.2@),
        ret.3@.thread_id() == final(lctx).thread_id(),
        (ret.3@.state() is WriteLock) == write_target,
        write_target ==> ret.3@.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        write_target ==> final(krnl).pt_mp.spec_index(target_pagetable).locking_thread() is Write,
        !write_target ==> ret.3@.state() is ReadLock,
        !write_target ==> final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&ret.3@),
        write_target ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        write_target ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        ret.0 == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0),
        ret.1 == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && ret.4@.dom().contains(w) || p == target_pagetable && ret.5@.dom().contains(w)),
        ret.0 && ret.1 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.4@.dom().contains(w),
        ret.0 && ret.1 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.5@.dom().contains(w),
        forall|w: WindowVa| #![trigger ret.4@.dom().contains(w)] ret.4@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& ret.4@.index(w).state() is WriteLock
                &&& ret.4@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.4@.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger ret.5@.dom().contains(w)] ret.5@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& ret.5@.index(w).state() is WriteLock
                &&& ret.5@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.5@.index(w))
                &&& !write_target ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !write_target ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !(ret.0 && ret.1) ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
{
    proof {
        krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable);
        krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable);
        assert(krnl.pt_mp.spec_index(source_pagetable).inv() && krnl.pt_mp.spec_index(target_pagetable).inv()) by {
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, source_pagetable); pagetable_perms_wf_at(krnl.pt_mp, target_pagetable);
        };
    }
    let (Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm)) = if write_target {
        krnl.rlock_wlock_pagetable_pair(source_pagetable, target_pagetable, Tracked(&mut *lctx))
    } else {
        krnl.rlock_pagetable_pair(source_pagetable, target_pagetable, Tracked(&mut *lctx))
    };
    proof {
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable);
        if write_target {
            krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable);
        } else {
            krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable);
        }
        assert(krnl.pt_mp.dom() == old(krnl).pt_mp.dom()) by { reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_pagetable_nonlock_fields_unchanged); };
        pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), source_pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), target_pagetable);
    }
    let source_user = ipc_pages_range_user(&*krnl, source_range, source_pagetable, Tracked(&*lctx), Tracked(&source_pagetable_lock_perm));
    let target_user = ipc_pages_range_user(&*krnl, target_range, target_pagetable, Tracked(&*lctx), Tracked(&target_pagetable_lock_perm));
    if !(source_user && target_user) {
        let tracked source_windows = Map::<WindowVa, LockPerm>::tracked_empty();
        let tracked target_windows = Map::<WindowVa, LockPerm>::tracked_empty();
        return (source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows));
    }
    let (Tracked(source_windows), Tracked(target_windows)) = ipc_pages_lock_pair_windows(
        krnl, source_range, target_range, source_pagetable, target_pagetable, Tracked(&mut *lctx), Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm),
    );
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
    }
    (true, true, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows))
}

/// Releases the 2M windows and both read-locked page tables of a pages rendezvous without a visible change and passes the step boundary,
/// keeping the held CPU, both held threads, and the held endpoint.
fn ipc_pages_unlock_tables_and_windows(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_pagetable: RwLockPageTableRoot, target_pagetable: RwLockPageTableRoot, cpu_id: CpuId,
    current_thread_ptr: RwLockThreadPtr, peer_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(steps): Tracked<&mut KernelSteps>, Tracked(source_pagetable_lock_perm): Tracked<LockPerm>, Tracked(target_pagetable_lock_perm): Tracked<LockPerm>,
    Tracked(source_windows): Tracked<Map<WindowVa, LockPerm>>, Tracked(target_windows): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        source_range.wf(),
        source_range.len > 0,
        target_range.wf(),
        target_range.len > 0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0,
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        source_pagetable_lock_perm.state() is ReadLock,
        source_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&source_pagetable_lock_perm),
        target_pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), target_pagetable, if (target_pagetable_lock_perm.state() is WriteLock) { TypedLockMode::Write } else { TypedLockMode::Read }),
        (target_pagetable_lock_perm.state() is WriteLock) ==> target_pagetable_lock_perm.lock_id() == old(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !(target_pagetable_lock_perm.state() is WriteLock) ==> target_pagetable_lock_perm.state() is ReadLock,
        !(target_pagetable_lock_perm.state() is WriteLock) ==> old(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&target_pagetable_lock_perm),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && source_windows.dom().contains(w) || p == target_pagetable && target_windows.dom().contains(w)),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> target_windows.dom().contains(w),
        forall|w: WindowVa| #![trigger source_windows.dom().contains(w)] source_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& source_windows.index(w).state() is WriteLock
                &&& source_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &source_windows.index(w))
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger target_windows.dom().contains(w)] target_windows.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& target_windows.index(w).state() is WriteLock
                &&& target_windows.index(w).thread_id() == old(lctx).thread_id()
                &&& pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &target_windows.index(w))
                &&& !(target_pagetable_lock_perm.state() is WriteLock) ==> pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !(target_pagetable_lock_perm.state() is WriteLock) ==> !pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        target_pagetable_lock_perm.state() is ReadLock,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        old(steps).snapshot_k().pt_mp.spec_index(source_pagetable).inv(),
        old(steps).snapshot_k().pt_mp.spec_index(target_pagetable).inv(),
        !old(steps).snapshot_k().pt_mp.spec_index(source_pagetable).locked_by_thread(old(lctx).thread_id()),
        !old(steps).snapshot_k().pt_mp.spec_index(target_pagetable).locked_by_thread(old(lctx).thread_id()),
        !(old(steps).snapshot_k().pt_mp.spec_index(source_pagetable).locking_thread() is Write),
        !(old(steps).snapshot_k().pt_mp.spec_index(target_pagetable).locking_thread() is Write),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        *old(krnl) == (KernelK { pt_mp: old(krnl).pt_mp, pt_lower: old(krnl).pt_lower, ..old(steps).snapshot_k() }),
        old(krnl).pt_mp.dom() == old(steps).snapshot_k().pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger old(krnl).pt_mp.spec_index(p)]
            old(steps).snapshot_k().pt_mp.dom().contains(p) && p != source_pagetable && p != target_pagetable ==> old(krnl).pt_mp.spec_index(p) == old(steps).snapshot_k().pt_mp.spec_index(p),
        old(krnl).pt_lower.view() =~= old(steps).snapshot_k().pt_lower.view().insert(source_pagetable, old(krnl).pt_lower.view().spec_index(source_pagetable))
            .insert(target_pagetable, old(krnl).pt_lower.view().spec_index(target_pagetable)),
        old(krnl).pt_mp.spec_index(source_pagetable).view() == old(steps).snapshot_k().pt_mp.spec_index(source_pagetable).view(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_4k() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), source_pagetable).mapping_4k(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_2m() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), source_pagetable).mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), source_pagetable).mapping_1g() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), source_pagetable).mapping_1g(),
        old(krnl).pt_mp.spec_index(target_pagetable).view() == old(steps).snapshot_k().pt_mp.spec_index(target_pagetable).view(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_4k() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), target_pagetable).mapping_4k(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), target_pagetable).mapping_2m(),
        pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(old(steps).snapshot_k().pt_mp, old(steps).snapshot_k().pt_lower.view(), target_pagetable).mapping_1g(),
        old(krnl).pt_mp.spec_index(source_pagetable).locking_thread() == (RwLockState::Read { reader_map: (if old(steps).snapshot_k().pt_mp.spec_index(source_pagetable).locking_thread() is Read
            { old(steps).snapshot_k().pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), source_pagetable_lock_perm.lock_id()) }),
        old(krnl).pt_mp.spec_index(target_pagetable).locking_thread() == (RwLockState::Read { reader_map: (if old(steps).snapshot_k().pt_mp.spec_index(target_pagetable).locking_thread() is Read
            { old(steps).snapshot_k().pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), target_pagetable_lock_perm.lock_id()) }),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        final(steps).snapshot_k() == *final(krnl),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pagetable_lock_map().dom().is_empty(),
        final(lctx).pagetable_window_lock_map().dom().is_empty(),
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr) == old(krnl).thr_mp.spec_index(current_thread_ptr),
        final(krnl).thr_mp.dom().contains(peer_thread_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr) == old(krnl).thr_mp.spec_index(peer_thread_ptr),
{
    let ghost entry_k = steps.snapshot_k();
    ipc_pages_unlock_pair_windows(
        krnl, source_range, target_range, source_pagetable, target_pagetable, Tracked(&mut *lctx), Tracked(&source_pagetable_lock_perm), Tracked(&target_pagetable_lock_perm),
        Tracked(source_windows), Tracked(target_windows),
    );
    proof {
        if entry_k.pt_mp.spec_index(source_pagetable).locking_thread() is Read {
            let readers = entry_k.pt_mp.spec_index(source_pagetable).locking_thread()->Read_reader_map;
            assert(readers.insert(lctx.thread_id(), source_pagetable_lock_perm.lock_id()).remove(lctx.thread_id()) =~= readers);
        } else {
            assert(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), source_pagetable_lock_perm.lock_id()).remove(lctx.thread_id()).dom() =~= Set::empty());
        }
        if entry_k.pt_mp.spec_index(target_pagetable).locking_thread() is Read {
            let readers = entry_k.pt_mp.spec_index(target_pagetable).locking_thread()->Read_reader_map;
            assert(readers.insert(lctx.thread_id(), target_pagetable_lock_perm.lock_id()).remove(lctx.thread_id()) =~= readers);
        } else {
            assert(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), target_pagetable_lock_perm.lock_id()).remove(lctx.thread_id()).dom() =~= Set::empty());
        }
    }
    krnl.runlock_pagetable(source_pagetable, Tracked(&mut *lctx), Tracked(source_pagetable_lock_perm));
    krnl.runlock_pagetable(target_pagetable, Tracked(&mut *lctx), Tracked(target_pagetable_lock_perm));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&entry_k, krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&entry_k, krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
        assert(kernel_endpoint_nonlock_fields_unchanged(entry_k.ep_mp, krnl.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq(&entry_k, &*krnl);
        krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
    }
}

/// Read-locks both page tables of a pages rendezvous and, when both ranges are user ranges, every existing 2M window of both ranges.
/// A target range missing an L2 directory entry releases every lock without a visible change, write-locks the target page table
/// instead, and locks the existing 2M windows again. The last attempt's locks are taken on `final(steps).snapshot_k()`.
fn ipc_pages_lock_tables_attempt(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
) -> (ret: (bool, bool, bool, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<Map<WindowVa, LockPerm>>, Tracked<Map<WindowVa, LockPerm>>,
    Ghost<LocalContext>))
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        (source_thread == current_thread_ptr) == (old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: IpcPagesTables::Unlocked, released: None }),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        old(krnl).prc_mp.dom().contains(source_process),
        old(krnl).prc_mp.dom().contains(target_process),
        !old(krnl).prc_mp.spec_index(source_process).view().zombie,
        !old(krnl).prc_mp.spec_index(target_process).view().zombie,
        old(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        old(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).view() == old(steps).view(),
        final(steps).nonlock_view() == old(steps).nonlock_view(),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..final(steps).snapshot_k() }),
        final(krnl).pt_mp.dom() == final(steps).snapshot_k().pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(p)]
            final(steps).snapshot_k().pt_mp.dom().contains(p) && p != source_pagetable && p != target_pagetable ==> final(krnl).pt_mp.spec_index(p) == final(steps).snapshot_k().pt_mp.spec_index(p),
        final(krnl).pt_lower.view() =~= final(steps).snapshot_k().pt_lower.view().insert(source_pagetable, final(krnl).pt_lower.view().spec_index(source_pagetable))
            .insert(target_pagetable, final(krnl).pt_lower.view().spec_index(target_pagetable)),
        final(krnl).pt_mp.spec_index(source_pagetable).view() == final(steps).snapshot_k().pt_mp.spec_index(source_pagetable).view(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_4k() == pagetable_c(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), source_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_2m() == pagetable_c(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), source_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).mapping_1g() == pagetable_c(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), source_pagetable).mapping_1g(),
        final(krnl).pt_mp.spec_index(target_pagetable).view() == final(steps).snapshot_k().pt_mp.spec_index(target_pagetable).view(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_4k() == pagetable_c(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), target_pagetable).mapping_4k(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_2m() == pagetable_c(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), target_pagetable).mapping_2m(),
        pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).mapping_1g() == pagetable_c(final(steps).snapshot_k().pt_mp, final(steps).snapshot_k().pt_lower.view(), target_pagetable).mapping_1g(),
        !(final(steps).snapshot_k().pt_mp.spec_index(source_pagetable).locking_thread() is Write),
        ret.0 ==> final(steps).snapshot_k().pt_mp.spec_index(target_pagetable).locking_thread() is None,
        !ret.0 ==> !(final(steps).snapshot_k().pt_mp.spec_index(target_pagetable).locking_thread() is Write),
        typed_lock_maps_aligned(&final(steps).snapshot_k(), &ret.7@),
        ret.7@.thread_id() == old(lctx).thread_id(),
        ret.7@.cpu_lock_map() == old(lctx).cpu_lock_map(),
        ret.7@.thread_lock_map() == old(lctx).thread_lock_map(),
        ret.7@.endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        ret.0 ==> final(krnl).pt_mp.spec_index(target_pagetable).locking_thread() is Write,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == final(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        (source_thread == current_thread_ptr) == (final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: IpcPagesTables::Unlocked, released: None }),
        final(krnl).thr_mp.dom().contains(peer_thread_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        final(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        final(krnl).prc_mp.dom().contains(source_process),
        final(krnl).prc_mp.dom().contains(target_process),
        !final(krnl).prc_mp.spec_index(source_process).view().zombie,
        !final(krnl).prc_mp.spec_index(target_process).view().zombie,
        final(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        final(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, if ret.0 { TypedLockMode::Write } else { TypedLockMode::Read }),
        ret.3@.state() is ReadLock,
        ret.3@.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&ret.3@),
        ret.4@.thread_id() == final(lctx).thread_id(),
        (ret.4@.state() is WriteLock) == ret.0,
        ret.0 ==> ret.4@.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !ret.0 ==> ret.4@.state() is ReadLock,
        !ret.0 ==> final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&ret.4@),
        ret.0 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        ret.0 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        ret.1 == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0),
        ret.2 == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && ret.5@.dom().contains(w) || p == target_pagetable && ret.6@.dom().contains(w)),
        ret.1 && ret.2 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.5@.dom().contains(w),
        ret.1 && ret.2 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.6@.dom().contains(w),
        forall|w: WindowVa| #![trigger ret.5@.dom().contains(w)] ret.5@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& ret.5@.index(w).state() is WriteLock
                &&& ret.5@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.5@.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger ret.6@.dom().contains(w)] ret.6@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& ret.6@.index(w).state() is WriteLock
                &&& ret.6@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.6@.index(w))
                &&& !ret.0 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !ret.0 ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !(ret.1 && ret.2) ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
        !ret.0 && ret.1 && ret.2 ==> forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(current_thread_ptr).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
{
    let ghost entry_lctx = *lctx;
    proof {
        krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), source_pagetable);
        krnl.pt_mp.typed_lock_map_aligned_locked_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable);
        assert(krnl.pt_mp.spec_index(source_pagetable).inv() && krnl.pt_mp.spec_index(target_pagetable).inv()) by {
            pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, source_pagetable); pagetable_perms_wf_at(krnl.pt_mp, target_pagetable);
        };
    }
    let (source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows)) =
        ipc_pages_lock_tables_and_windows(krnl, source_range, target_range, source_pagetable, target_pagetable, Tracked(&mut *lctx), false);
    if !(source_user && target_user) {
        return (false, source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows),
            Ghost(entry_lctx));
    }
    if ipc_pages_target_l2_present(&*krnl, target_range, target_pagetable, Tracked(&*lctx), Tracked(&target_pagetable_lock_perm)) {
        proof { va_range_2m_windows_contains_window_of_first_n_pages(*target_range, target_range.len as int); }
        return (false, true, true, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows), Ghost(entry_lctx));
    }
    ipc_pages_unlock_tables_and_windows(
        krnl, source_range, target_range, source_pagetable, target_pagetable, cpu_id, current_thread_ptr, peer_thread_ptr, endpoint_ptr, Tracked(&mut *lctx),
        Tracked(&mut *steps), Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows),
    );
    proof {
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
    }
    let ghost lock_pre_lctx = *lctx;
    let (source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows)) =
        ipc_pages_lock_tables_and_windows(krnl, source_range, target_range, source_pagetable, target_pagetable, Tracked(&mut *lctx), true);
    (true, source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows), Ghost(lock_pre_lctx))
}

/// After the pages enter step: locks both page tables and the existing 2M windows of both ranges, read-locking the target page table
/// when every target page has its L2 directory entry and write-locking it to fill them otherwise, and records the lock step.
pub(super) fn ipc_pages_lock_tables(
    krnl: &mut KernelK, source_range: &VaRange4K, target_range: &VaRange4K, source_thread: RwLockThreadPtr, target_thread: RwLockThreadPtr,
    cpu_id: CpuId, process_ptr: RwLockProcessPtr, current_thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, peer_thread_ptr: RwLockThreadPtr,
    source_process: RwLockProcessPtr, source_container: RwLockContainerPtr, source_pagetable: RwLockPageTableRoot, target_process: RwLockProcessPtr,
    target_container: RwLockContainerPtr, target_pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(current_thread_lock_perm): Tracked<&LockPerm>, Tracked(peer_thread_lock_perm): Tracked<&LockPerm>,
    Ghost(channel_index): Ghost<EndpointIdx>, Ghost(waiting_state): Ghost<ThreadState>, Ghost(start): Ghost<int>, Ghost(pre): Ghost<KernelU>,
) -> (ret: (bool, bool, bool, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<Map<WindowVa, LockPerm>>, Tracked<Map<WindowVa, LockPerm>>))
    requires
        old(krnl).inv(),
        old(steps).snapshot_k() == *old(krnl),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        (source_thread == current_thread_ptr) == (old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        old(krnl).thr_mp.dom().contains(current_thread_ptr),
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view() == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: IpcPagesTables::Unlocked, released: None }),
        old(krnl).thr_mp.dom().contains(peer_thread_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        old(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        old(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(old(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(source_thread).being_killed(),
        old(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        old(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        old(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !old(krnl).thr_mp.spec_index(target_thread).being_killed(),
        old(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        old(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        old(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        old(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        old(krnl).prc_mp.dom().contains(source_process),
        old(krnl).prc_mp.dom().contains(target_process),
        !old(krnl).prc_mp.spec_index(source_process).view().zombie,
        !old(krnl).prc_mp.spec_index(target_process).view().zombie,
        old(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        old(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        old(krnl).pt_mp.dom().contains(source_pagetable),
        old(krnl).pt_mp.dom().contains(target_pagetable),
        old(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        old(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).cpu_lock_map().dom() =~= set![cpu_id],
        old(lctx).container_lock_map().dom().is_empty(),
        old(lctx).process_lock_map().dom().is_empty(),
        old(lctx).thread_lock_map().dom() =~= set![current_thread_ptr, peer_thread_ptr],
        old(lctx).endpoint_lock_map().dom() =~= set![endpoint_ptr],
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).pcid_allocator_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(lctx).iommu_table_lock_map().dom().is_empty(),
        old(lctx).iommu_root_table_lock_map().dom().is_empty(),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(lctx).holds_no_allocator_locks(PageSize::SZ2m),
        old(lctx).holds_no_allocator_locks(PageSize::SZ1g),
        old(lctx).cpu_offline_flag_lock_map().dom().is_empty(),
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        old(lctx).pagetable_lock_map().dom().is_empty(),
        old(lctx).pagetable_window_lock_map().dom().is_empty(),
        0 <= start <= old(steps).view().len(),
        ipc_pages_trace_after_enter(old(steps).view().subrange(start, old(steps).view().len() as int), pre, cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range }),
        (waiting_state is SENDING) == (source_thread == current_thread_ptr),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view().len() == old(steps).view().len() + 1,
        final(steps).nonlock_view().len() == old(steps).nonlock_view().len() + 1,
        forall|base: Seq<KernelStep>| kernel_steps_prefix_unchanged(base, old(steps).view()) ==> #[trigger] kernel_steps_prefix_unchanged(base, final(steps).view()),
        ipc_pages_trace_after_lock(final(steps).view().subrange(start, final(steps).view().len() as int), pre, cpu_id, channel_index, waiting_state, if waiting_state is SENDING { *source_range } else { *target_range },
            if ret.0 { IpcPagesTables::Fill } else { IpcPagesTables::Read }),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == final(lctx).cpu_id(),
        current_thread_ptr != peer_thread_ptr,
        source_thread == current_thread_ptr && target_thread == peer_thread_ptr || source_thread == peer_thread_ptr && target_thread == current_thread_ptr,
        (source_thread == current_thread_ptr) == (final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING),
        typed_lock_map_contains_mode(final(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == false,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(process_ptr),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(current_thread_ptr),
        final(krnl).thr_mp.dom().contains(current_thread_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == (ThreadState::RUNNING { cpu_id }),
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), current_thread_ptr, TypedLockMode::Write),
        current_thread_lock_perm.state() is WriteLock,
        current_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        current_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(current_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().syscall_progress.view()
            == Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: if ret.0 { IpcPagesTables::Fill } else { IpcPagesTables::Read }, released: None }),
        final(krnl).thr_mp.dom().contains(peer_thread_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is SENDING || final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state is RECEIVING,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), peer_thread_ptr, TypedLockMode::Write),
        peer_thread_lock_perm.state() is WriteLock,
        peer_thread_lock_perm.thread_id() == final(lctx).thread_id(),
        peer_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(peer_thread_ptr).locking_thread()->Write_lock_id,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == Some(endpoint_ptr),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().syscall_progress.view() is None,
        !final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost().exited,
        !final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost().exited,
        final(krnl).ep_mp.dom().contains(endpoint_ptr),
        typed_lock_map_contains_mode(final(lctx).endpoint_lock_map(), endpoint_ptr, TypedLockMode::Write),
        !final(krnl).thr_mp.spec_index(source_thread).being_killed(),
        final(krnl).thr_mp.spec_index(source_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(source_thread).view().owning_proc == source_process,
        final(krnl).thr_mp.spec_index(source_thread).view().owning_container == source_container,
        final(krnl).thr_mp.spec_index(source_thread).view().proc_pagetable_ptr == source_pagetable,
        !final(krnl).thr_mp.spec_index(target_thread).being_killed(),
        final(krnl).thr_mp.spec_index(target_thread).view().free_quota_pending_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(target_thread).view().owning_proc == target_process,
        final(krnl).thr_mp.spec_index(target_thread).view().owning_container == target_container,
        final(krnl).thr_mp.spec_index(target_thread).view().proc_pagetable_ptr == target_pagetable,
        source_process != target_process,
        final(krnl).prc_mp.dom().contains(source_process),
        final(krnl).prc_mp.dom().contains(target_process),
        !final(krnl).prc_mp.spec_index(source_process).view().zombie,
        !final(krnl).prc_mp.spec_index(target_process).view().zombie,
        final(krnl).prc_mp.spec_index(source_process).view().pagetable == source_pagetable,
        final(krnl).prc_mp.spec_index(target_process).view().pagetable == target_pagetable,
        source_pagetable != target_pagetable,
        final(krnl).pt_mp.dom().contains(source_pagetable),
        final(krnl).pt_mp.dom().contains(target_pagetable),
        final(krnl).pt_mp.spec_index(source_pagetable).view().proc_ptr == source_process,
        final(krnl).pt_mp.spec_index(target_pagetable).view().proc_ptr == target_process,
        source_range.wf(),
        target_range.wf(),
        source_range.len == target_range.len,
        source_range.len > 0,
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).iommu_root_table_lock_map() == old(lctx).iommu_root_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).pagetable_lock_map().dom() =~= set![source_pagetable, target_pagetable],
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), source_pagetable, TypedLockMode::Read),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), target_pagetable, if ret.0 { TypedLockMode::Write } else { TypedLockMode::Read }),
        ret.3@.state() is ReadLock,
        ret.3@.thread_id() == final(lctx).thread_id(),
        final(krnl).pt_mp.spec_index(source_pagetable).read_lock_perm_match(&ret.3@),
        ret.4@.thread_id() == final(lctx).thread_id(),
        (ret.4@.state() is WriteLock) == ret.0,
        ret.0 ==> ret.4@.lock_id() == final(krnl).pt_mp.spec_index(target_pagetable).locking_thread()->Write_lock_id,
        !ret.0 ==> ret.4@.state() is ReadLock,
        !ret.0 ==> final(krnl).pt_mp.spec_index(target_pagetable).read_lock_perm_match(&ret.4@),
        ret.0 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).leaves_present(),
        ret.0 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus == Map::<(PageMapPtr, L2Index), Set<CpuId>>::empty(),
        ret.1 == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).kernel_l4_end() <= spec_va2index(source_range.start).0),
        ret.2 == (pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).kernel_l4_end() <= spec_va2index(target_range.start).0),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (p == source_pagetable && ret.5@.dom().contains(w) || p == target_pagetable && ret.6@.dom().contains(w)),
        ret.1 && ret.2 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
            va_range_2m_windows(*source_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.5@.dom().contains(w),
        ret.1 && ret.2 ==> forall|w: WindowVa| #![trigger va_range_2m_windows(*target_range).contains(w)]
            va_range_2m_windows(*target_range).contains(w) && pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> ret.6@.dom().contains(w),
        forall|w: WindowVa| #![trigger ret.5@.dom().contains(w)] ret.5@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (source_pagetable, w), TypedLockMode::Write)
                &&& ret.5@.index(w).state() is WriteLock
                &&& ret.5@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.5@.index(w))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_leaves_present(w)
                &&& !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), source_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        forall|w: WindowVa| #![trigger ret.6@.dom().contains(w)] ret.6@.dom().contains(w) ==> {
                &&& va_range_2m_windows(*target_range).contains(w)
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(final(lctx).pagetable_window_lock_map(), (target_pagetable, w), TypedLockMode::Write)
                &&& ret.6@.index(w).state() is WriteLock
                &&& ret.6@.index(w).thread_id() == final(lctx).thread_id()
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.l2_lock_of(pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)))
                    .lock_perm_match(spec_v2l2index(w.va), &ret.6@.index(w))
                &&& !ret.0 ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_leaves_present(w)
                &&& !ret.0 ==> !pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).lower.window_stale_cpus.dom().contains((
                    pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            },
        !(ret.1 && ret.2) ==> final(lctx).pagetable_window_lock_map().dom().is_empty(),
        !ret.0 && ret.1 && ret.2 ==> forall|j: int| #![trigger target_range.view().spec_index(j)] 0 <= j < target_range.len ==> {
                let va = target_range.view().spec_index(j);
                &&& final(lctx).pagetable_window_lock_map().dom().contains((target_pagetable, window_of(va)))
                &&& pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), target_pagetable).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some
            },
        final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        final(krnl).cpu_published[cpu_id as int].view() == old(krnl).cpu_published[cpu_id as int].view(),
        final(krnl).ep_mp.spec_index(endpoint_ptr) == old(krnl).ep_mp.spec_index(endpoint_ptr),
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().state == old(krnl).thr_mp.spec_index(current_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(current_thread_ptr).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(current_thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().state == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().state,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr == old(krnl).thr_mp.spec_index(peer_thread_ptr).view().blocking_endpoint_ptr,
        final(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(peer_thread_ptr).view_ghost(),
{
    let ghost range = if waiting_state is SENDING { *source_range } else { *target_range };
    let (fill, source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows),
        Ghost(lock_pre_lctx)) = ipc_pages_lock_tables_attempt(
        krnl, source_range, target_range, source_thread, target_thread, cpu_id, process_ptr, current_thread_ptr, endpoint_ptr, peer_thread_ptr, source_process,
        source_container, source_pagetable, target_process, target_container, target_pagetable, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(current_thread_lock_perm), Tracked(peer_thread_lock_perm),
    );
    let ghost tables = if fill { IpcPagesTables::Fill } else { IpcPagesTables::Read };
    let ghost lock_pre_k = steps.snapshot_k();
    let ghost attempted_k = *krnl;
    krnl.set_thread_syscall_progress(current_thread_ptr, Ghost(Some(SyscallProgress::IpcPages { source_range: *source_range, target_range: *target_range, peer: peer_thread_ptr, tables: tables, released: None })),
        Tracked(&*lctx), Tracked(current_thread_lock_perm));
    proof {
        ipc_pages_lock_tables_step_pre_from_k(&lock_pre_k, &lock_pre_lctx, cpu_id, current_thread_ptr, peer_thread_ptr, endpoint_ptr, source_thread, target_thread, source_process,
            target_process, source_pagetable, target_pagetable, tables);
        assert(ipc_pages_lock_tables_step(kernel_k_to_kernel_u(lock_pre_k), kernel_k_to_kernel_u(*krnl), cpu_id, tables)) by {
            if fill { krnl.pt_mp.typed_lock_map_aligned_write_at(lctx.pagetable_lock_map(), lctx.thread_id(), target_pagetable); }
            assert(krnl.pt_lower.view() =~= lock_pre_k.pt_lower.view().insert(source_pagetable, krnl.pt_lower.view().spec_index(source_pagetable))
                .insert(target_pagetable, krnl.pt_lower.view().spec_index(target_pagetable)));
            kernel_pagetable_pair_lock_modes_and_progress_changed_implies_u_step(&lock_pre_k, &*krnl, source_process, target_process, source_pagetable, target_pagetable,
                current_thread_ptr);
            ipc_pages_lock_tables_step_from_u(kernel_k_to_kernel_u(lock_pre_k), kernel_k_to_kernel_u(*krnl), cpu_id, current_thread_ptr, *source_range, *target_range,
                peer_thread_ptr, source_process, target_process, tables);
        };
        enter_kernel_view_release_preserving_lock_alignments(&*krnl, &mut *lctx);
        let ghost lock_before = steps.view();
        let ghost locked_k = *krnl;
        krnl.kernel_step_boundary_thread_syscall_progress_changed(&mut *lctx, &mut *steps, current_thread_ptr);
        ipc_pages_trace_lock_step(&*steps, lock_before, start, pre, kernel_k_to_kernel_u(lock_pre_k), kernel_k_to_kernel_u(locked_k), cpu_id, channel_index, waiting_state,
            range, tables);
        thread_cpu_wf_cpu_at(krnl.thr_mp, krnl.cpu_arr, cpu_id); thread_perms_wf_at(krnl.thr_mp, peer_thread_ptr);
        process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, source_thread); process_thread_wf_at(krnl.prc_mp, krnl.thr_mp, target_thread);
        process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, source_process); process_pagetable_match_process_at(krnl.prc_mp, krnl.pt_mp, target_process);
        va_range_2m_windows_contains_window_of_first_n_pages(*target_range, target_range.len as int);
    }
    (fill, source_user, target_user, Tracked(source_pagetable_lock_perm), Tracked(target_pagetable_lock_perm), Tracked(source_windows), Tracked(target_windows))
}
} // verus!
