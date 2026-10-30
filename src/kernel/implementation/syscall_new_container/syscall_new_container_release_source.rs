use vstd::prelude::*;
use crate::*;

verus! {
/// Releases the read-held source table `pagetable_ptr` of a rejected `new_container` and, when `windows_held`, first its
/// existing windows over `source_range` held with perms `source_window_perms`; the table's lock state returns to the one
/// it had in `base`, before this thread read-locked it.
pub(super) fn new_container_release_source_table(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_ptr: RwLockPageTableRoot, source_range: &VaRange4K, windows_held: bool,
    Ghost(base): Ghost<KernelK>, Tracked(pagetable_lock_perm): Tracked<LockPerm>, Tracked(source_window_perms): Tracked<Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        old(lctx).pagetable_lock_map().dom() =~= set![pagetable_ptr],
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock && pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        {
            let entry = base.pt_mp.spec_index(pagetable_ptr);
            &&& entry.inv() && !entry.wlocked() && !entry.locked_by_thread(old(lctx).thread_id())
            &&& old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == (RwLockState::Read {
                reader_map: (if entry.locking_thread() is Read { entry.locking_thread()->Read_reader_map } else { Map::empty() }).insert(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            })
        },
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (windows_held && p == pagetable_ptr && source_window_perms.dom().contains(w)),
        !windows_held ==> old(lctx).pagetable_window_lock_map().dom().is_empty(),
        windows_held ==> {
            let table = pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& source_range.wf() && source_range.len > 0
            &&& table.kernel_l4_end() <= spec_va2index(source_range.start).0
            &&& forall|w: WindowVa| #![trigger va_range_2m_windows(*source_range).contains(w)]
                va_range_2m_windows(*source_range).contains(w) && table.higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some ==> source_window_perms.dom().contains(w)
            &&& forall|w: WindowVa| #![trigger source_window_perms.dom().contains(w)] source_window_perms.dom().contains(w) ==> {
                &&& va_range_2m_windows(*source_range).contains(w)
                &&& table.higher.spec_resolve_mapping_l3(spec_v2l4index(w.va), spec_v2l3index(w.va)) is Some
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, w), TypedLockMode::Write)
                &&& source_window_perms.index(w).state() is WriteLock && source_window_perms.index(w).thread_id() == old(lctx).thread_id()
                &&& table.lower.l2_owner(table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)) == (SpinLockState::Some { thread_id: source_window_perms.index(w).thread_id(), lock_id: source_window_perms.index(w).lock_id() })
                &&& table.window_leaves_present(w)
                &&& !table.lower.window_stale_cpus.dom().contains((table.window_l2_page(spec_v2l4index(w.va), spec_v2l3index(w.va)), spec_v2l2index(w.va)))
            }
        },
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(krnl).ep_mp, final(krnl).ep_mp),
        kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), final(krnl)),
        *final(krnl) == (KernelK { pt_mp: final(krnl).pt_mp, pt_lower: final(krnl).pt_lower, ..*old(krnl) }),
        final(krnl).pt_mp.unchanged_except(&old(krnl).pt_mp, pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread() == base.pt_mp.spec_index(pagetable_ptr).locking_thread(),
        final(krnl).pt_lower.view() =~= old(krnl).pt_lower.view().insert(pagetable_ptr, final(krnl).pt_lower.view().spec_index(pagetable_ptr)),
        !windows_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks == pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks,
        windows_held ==> pagetable_c(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks
            == pagetable_window_locks_after_unlocking_range(pagetable_c(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).lower.pagetable_window_locks, *source_range),
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
{
    proof { pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr); }
    if windows_held {
        krnl.unlock_pagetable_range_existing_windows(pagetable_ptr, source_range, Tracked(&pagetable_lock_perm), Tracked(&mut *lctx), Tracked(source_window_perms));
    }
    proof {
        let entry = base.pt_mp.spec_index(pagetable_ptr);
        if entry.locking_thread() is Read {
            assert(entry.locking_thread()->Read_reader_map.insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id()) =~= entry.locking_thread()->Read_reader_map);
        } else {
            assert(Map::<LockThreadId, LockToken>::empty().insert(lctx.thread_id(), pagetable_lock_perm.lock_id()).remove(lctx.thread_id()).dom() =~= Set::empty());
        }
    }
    krnl.runlock_pagetable(pagetable_ptr, Tracked(&mut *lctx), Tracked(pagetable_lock_perm));
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; };
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(old(krnl), &*krnl)) by { broadcast use kernel_container_nonlock_fields_and_quotas_unchanged_transitive; };
    }
}
} // verus!
