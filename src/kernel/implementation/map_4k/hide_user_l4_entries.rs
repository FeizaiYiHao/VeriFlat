use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::hide_user_l4_entries_eof::*;
#[cfg(verus_keep_ghost)]
use super::hide_user_l4_entries_trace::*;

verus! {
/// Hide the resolving user root entry `l4i` of the write-held `pagetable` and end the kernel step, which is recorded when the
/// user view changed. Returns the state right before the step boundary.
fn hide_user_l4_entry_and_end_step(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    pagetable_perm: Tracked<&LockPerm>) -> (hidden: Ghost<KernelK>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0, NUM_CPUS),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= l4i && pei_valid(l4i),
        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(l4i) is Some,
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] !old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i)
                ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
    ensures
        hide_user_l4_entry_eof_transition_framing(*old(krnl), hidden.view(), pagetable, l4i),
        final(krnl).inv(),
        held_containers_unchanged(hidden.view().ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(hidden.view().prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(hidden.view().thrd_mp, final(krnl).thrd_mp, old(lctx)),
        held_endpoints_unchanged(hidden.view().ep_mp, final(krnl).ep_mp, old(lctx)),
        held_cpu_sets_unchanged(hidden.view().cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_iommu_tables_unchanged(hidden.view().it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(hidden.view().pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpus_unchanged(hidden.view().cpu_arr, final(krnl).cpu_arr, old(lctx)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == hidden.view().cpu_op.view().view()[old(lctx).cpu_id() as int],
        index_valid(NUM_CPUS, old(lctx).cpu_id()) && hidden.view().cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep
            ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == hidden.view().cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.lock_id_by_key(pagetable) == hidden.view().pt_mp.lock_id_by_key(pagetable),
        final(krnl).pt_mp.spec_index(pagetable) == hidden.view().pt_mp.spec_index(pagetable),
        whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable) == whole_pagetable(hidden.view().pt_mp, hidden.view().pt_lower.view(), pagetable),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view() == record_user_view_change(old(steps).view(), kernel_k_to_kernel_u(*old(krnl)), kernel_k_to_kernel_u(hidden.view())),
{
    let ghost pre = *krnl;
    pagetable_map_hide_l4_entry(&mut krnl.pt_mp, Tracked(krnl.pt_lower.borrow_mut()), pagetable, l4i, Tracked(&mut *lctx), pagetable_perm);
    let ghost mid = *krnl;
    let ghost mid_lctx = *lctx;
    proof {
        assert(hide_user_l4_entry_eof_transition_framing(pre, mid, pagetable, l4i)) by { reveal(hide_user_l4_entry_eof_transition_framing); };
        pre.pt_mp.typed_lock_map_aligned_write_at(old(lctx).pagetable_lock_map(), old(lctx).thread_id(), pagetable);
        hide_user_l4_entry_eof(pre, mid, pagetable, l4i);
        assert(kernel_container_nonlock_fields_and_quotas_unchanged(&pre, &mid)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
        assert(kernel_endpoint_nonlock_fields_unchanged(pre.ep_mp, mid.ep_mp)) by { broadcast use group_kernel_endpoint_nonlock_fields_unchanged_transitive; };
        if kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), mid.pt_mp, mid.pt_lower.view()) {
            assert(kernel_cpu_process_thread_nonlock_fields_unchanged(&pre, &mid)) by {
                broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
            };
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        } else {
            hide_user_l4_entries_hide_step_pre_from_k(&pre, &mid, pagetable, l4i);
            krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps);
        }
        assert(kernel_step_boundary_framing(mid, *krnl, mid_lctx));
    }
    Ghost(mid)
}

/// Hide every resolving user root entry of the write-held `pagetable` in index order, ending one kernel step per hidden entry;
/// a hide that leaves the user view unchanged records no step. `hidden` lists the recorded hides as `(l4i, pre, post)` in step
/// order. Every CPU is listed stale for the whole table, no window of the table is locked, and no L2 entry of it is locked.
/// Afterwards no user root entry resolves, the table maps nothing, and its held chain keeps every table page, with each
/// hidden root entry as a placeholder naming its L3 page.
pub fn hide_user_l4_entries(krnl: &mut KernelK, pagetable: RwLockPageTableRoot, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    pagetable_perm: Tracked<&LockPerm>) -> (hidden: Ghost<Seq<(L4Index, KernelK, KernelK)>>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).pt_mp.dom().contains(pagetable),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
        pagetable_perm.view().state() is WriteLock,
        pagetable_perm.view().thread_id() == old(lctx).thread_id(),
        pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
        old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0, NUM_CPUS),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] !old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)),
        forall|p: PageMapPtr, i: L2Index| #![trigger whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_perms.dom().contains(p) && pei_valid(i)
                ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).lower.l2_owner(p, i) is None,
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(steps).snapshot_k() == *final(krnl),
        final(steps).view().len() == old(steps).view().len() + hidden.view().len(),
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|k: int| #![trigger hidden.view()[k]] 0 <= k < hidden.view().len() ==> {
            &&& final(steps).view()[old(steps).view().len() + k] == (KernelStep { old_u: kernel_k_to_kernel_u(hidden.view()[k].1), new_u: kernel_k_to_kernel_u(hidden.view()[k].2) })
            &&& process_pagetable_wf(hidden.view()[k].1.prc_mp, hidden.view()[k].1.pt_mp)
            &&& hide_user_l4_entry_eof_transition_framing(hidden.view()[k].1, hidden.view()[k].2, pagetable, hidden.view()[k].0)
            &&& typed_lock_maps_aligned(&hidden.view()[k].1, old(lctx))
            &&& held_cpus_unchanged(old(krnl).cpu_arr, hidden.view()[k].1.cpu_arr, old(lctx)) && held_containers_unchanged(old(krnl).ctn_mp, hidden.view()[k].1.ctn_mp, old(lctx))
            &&& held_processes_unchanged(old(krnl).prc_mp, hidden.view()[k].1.prc_mp, old(lctx)) && held_threads_unchanged(old(krnl).thrd_mp, hidden.view()[k].1.thrd_mp, old(lctx))
        },
        forall|k: int, m: int| #![trigger hidden.view()[k], hidden.view()[m]] 0 <= k < m < hidden.view().len() ==> hidden.view()[k].0 < hidden.view()[m].0,
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)),
        held_endpoints_unchanged(old(krnl).ep_mp, final(krnl).ep_mp, old(lctx)),
        held_cpu_sets_unchanged(old(krnl).cpu_set_mp, final(krnl).cpu_set_mp, old(lctx)),
        held_iommu_tables_unchanged(old(krnl).it_mp, final(krnl).it_mp, old(lctx)),
        held_pages_unchanged(old(krnl).pg_arr, final(krnl).pg_arr, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        final(krnl).pt_mp.dom().contains(pagetable),
        final(krnl).pt_mp.lock_id_by_key(pagetable) == old(krnl).pt_mp.lock_id_by_key(pagetable),
        final(krnl).pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
        final(krnl).pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
        ({
            let old_h = old(krnl).pt_mp.spec_index(pagetable).view();
            let new_h = final(krnl).pt_mp.spec_index(pagetable).view();
            &&& new_h.table_stale_cpus == old_h.table_stale_cpus && new_h.kernel_l4_end == old_h.kernel_l4_end && new_h.kernel_entries == old_h.kernel_entries
            &&& new_h.cr3 == old_h.cr3 && new_h.pcid == old_h.pcid && new_h.did == old_h.did && new_h.proc_ptr == old_h.proc_ptr
            &&& new_h.l3_tables == old_h.l3_tables && new_h.l3_rev_map == old_h.l3_rev_map && new_h.l2_rev_map == old_h.l2_rev_map
        }),
        ({
            let old_c = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable);
            let new_c = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable);
            &&& new_c.lower.l2_perms == old_c.lower.l2_perms && new_c.lower.l1_rev_map == old_c.lower.l1_rev_map && new_c.lower.window_stale_cpus == old_c.lower.window_stale_cpus
            &&& new_c.page_closure() == old_c.page_closure()
            &&& new_c.mapping_4k().dom() =~= Set::<VAddr>::empty() && new_c.mapping_2m().dom() =~= Set::<VAddr>::empty() && new_c.mapping_1g().dom() =~= Set::<VAddr>::empty()
            &&& new_c.lower.pagetable_window_locks.dom() =~= Set::<WindowVa>::empty()
        }),
        forall|i4: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(i4)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(i4) is None,
        forall|i4: L4Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l4(i4)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l4(i4)
                    == if whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_resolve_mapping_l4(i4) is Some {
                        Some(PageEntry { addr: whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l4(i4)->0.addr,
                            perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } })
                    } else {
                        whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l4(i4)
                    },
        forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l3(i4, i3)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l3(i4, i3) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l3(i4, i3),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l2(i4, i3, i2)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_l2(i4, i3, i2) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_l2(i4, i3, i2),
        forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1)
                    == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1),
        forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2)]
            whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2)
                ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2) == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2),
{
    let ghost entry = *krnl;
    let ghost e = whole_pagetable(entry.pt_mp, entry.pt_lower.view(), pagetable);
    let ghost mut hidden: Seq<(L4Index, KernelK, KernelK)> = Seq::empty();
    proof {
        krnl.default_pagetable_wf_at(pagetable);
        held_kernel_objects_unchanged_reflexive(krnl, lctx);
    }
    let mut l4i: L4Index = KERNEL_MEM_END_L4INDEX;
    while l4i < 512
        invariant
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            lctx.kernel_view_locking_state() is Acquire,
            steps.snapshot_k() == *krnl,
            KERNEL_MEM_END_L4INDEX <= l4i <= 512,
            e == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable),
            e.kernel_l4_end() == KERNEL_MEM_END_L4INDEX,
            old(krnl).pt_mp.spec_index(pagetable).view().table_stale_cpus.view() == Set::range(0, NUM_CPUS),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable, TypedLockMode::Write),
            pagetable_perm.view().state() is WriteLock,
            pagetable_perm.view().thread_id() == old(lctx).thread_id(),
            pagetable_perm.view().lock_id() == old(krnl).pt_mp.spec_index(pagetable).locking_thread()->Write_lock_id,
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w))] !old(lctx).pagetable_window_lock_map().dom().contains((pagetable, w)),
            forall|p: PageMapPtr, i: L2Index| #![trigger e.lower.l2_owner(p, i)] e.lower.l2_perms.dom().contains(p) && pei_valid(i) ==> e.lower.l2_owner(p, i) is None,
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            steps.view().len() == old(steps).view().len() + hidden.len(),
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|k: int| #![trigger hidden[k]] 0 <= k < hidden.len() ==> {
                &&& steps.view()[old(steps).view().len() + k] == (KernelStep { old_u: kernel_k_to_kernel_u(hidden[k].1), new_u: kernel_k_to_kernel_u(hidden[k].2) })
                &&& process_pagetable_wf(hidden[k].1.prc_mp, hidden[k].1.pt_mp)
                &&& hide_user_l4_entry_eof_transition_framing(hidden[k].1, hidden[k].2, pagetable, hidden[k].0)
                &&& typed_lock_maps_aligned(&hidden[k].1, old(lctx))
                &&& held_cpus_unchanged(old(krnl).cpu_arr, hidden[k].1.cpu_arr, old(lctx)) && held_containers_unchanged(old(krnl).ctn_mp, hidden[k].1.ctn_mp, old(lctx))
                &&& held_processes_unchanged(old(krnl).prc_mp, hidden[k].1.prc_mp, old(lctx)) && held_threads_unchanged(old(krnl).thrd_mp, hidden[k].1.thrd_mp, old(lctx))
                &&& hidden[k].0 < l4i
            },
            forall|k: int, m: int| #![trigger hidden[k], hidden[m]] 0 <= k < m < hidden.len() ==> hidden[k].0 < hidden[m].0,
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_threads_unchanged(old(krnl).thrd_mp, krnl.thrd_mp, old(lctx)),
            held_endpoints_unchanged(old(krnl).ep_mp, krnl.ep_mp, old(lctx)),
            held_cpu_sets_unchanged(old(krnl).cpu_set_mp, krnl.cpu_set_mp, old(lctx)),
            held_iommu_tables_unchanged(old(krnl).it_mp, krnl.it_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            krnl.pt_mp.dom().contains(pagetable),
            krnl.pt_mp.lock_id_by_key(pagetable) == old(krnl).pt_mp.lock_id_by_key(pagetable),
            krnl.pt_mp.spec_index(pagetable).locking_thread() == old(krnl).pt_mp.spec_index(pagetable).locking_thread(),
            krnl.pt_mp.spec_index(pagetable).being_killed() == old(krnl).pt_mp.spec_index(pagetable).being_killed(),
            ({
                let old_h = old(krnl).pt_mp.spec_index(pagetable).view();
                let new_h = krnl.pt_mp.spec_index(pagetable).view();
                &&& new_h.table_stale_cpus == old_h.table_stale_cpus && new_h.kernel_l4_end == old_h.kernel_l4_end && new_h.kernel_entries == old_h.kernel_entries
                &&& new_h.cr3 == old_h.cr3 && new_h.pcid == old_h.pcid && new_h.did == old_h.did && new_h.proc_ptr == old_h.proc_ptr
                &&& new_h.l3_tables == old_h.l3_tables && new_h.l3_rev_map == old_h.l3_rev_map && new_h.l2_rev_map == old_h.l2_rev_map
            }),
            ({
                let new_c = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable);
                &&& new_c.lower.l2_perms == e.lower.l2_perms && new_c.lower.l1_rev_map == e.lower.l1_rev_map && new_c.lower.window_stale_cpus == e.lower.window_stale_cpus
                &&& new_c.page_closure() == e.page_closure()
            }),
            forall|i4: L4Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l4(i4)]
                e.kernel_l4_end() <= i4 && pei_valid(i4) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_resolve_mapping_l4(i4)
                    == if i4 < l4i { None } else { e.spec_resolve_mapping_l4(i4) },
            forall|i4: L4Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_l4(i4)]
                e.kernel_l4_end() <= i4 && pei_valid(i4) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_l4(i4)
                    == if i4 < l4i && e.spec_resolve_mapping_l4(i4) is Some {
                        Some(PageEntry { addr: e.spec_held_l4(i4)->0.addr, perm: PageEntryPerm { present: false, ps: false, write: false, execute_disable: false, user: false, kernel_present: true } })
                    } else {
                        e.spec_held_l4(i4)
                    },
            forall|i4: L4Index, i3: L3Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_l3(i4, i3)]
                e.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_l3(i4, i3) == e.spec_held_l3(i4, i3),
            forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_l2(i4, i3, i2)]
                e.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_l2(i4, i3, i2) == e.spec_held_l2(i4, i3, i2),
            forall|i4: L4Index, i3: L3Index, i2: L2Index, i1: L1Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1)]
                e.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) && pei_valid(i1)
                    ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_4k_l1(i4, i3, i2, i1) == e.spec_held_4k_l1(i4, i3, i2, i1),
            forall|i4: L4Index, i3: L3Index, i2: L2Index| #![trigger whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2)]
                e.kernel_l4_end() <= i4 && pei_valid(i4) && pei_valid(i3) && pei_valid(i2) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable).spec_held_2m_l2(i4, i3, i2) == e.spec_held_2m_l2(i4, i3, i2),
        decreases 512 - l4i,
    {
        proof { pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable); }
        let root = krnl.pt_mp.borrow_typed(pagetable, Ghost(lctx.pagetable_lock_map()), Tracked(&*lctx), pagetable_perm).get_entry_l4(l4i);
        if root.is_some() {
            let ghost before = steps.view();
            let ghost pre = *krnl;
            proof { assert(typed_lock_maps_aligned(&pre, old(lctx))); }
            let Ghost(post) = hide_user_l4_entry_and_end_step(krnl, pagetable, l4i, Tracked(&mut *lctx), Tracked(&mut *steps), pagetable_perm);
            proof {
                reveal(hide_user_l4_entry_eof_transition_framing);
                if steps.view().len() > before.len() { hidden = hidden.push((l4i, pre, post)); }
            }
        }
        l4i = l4i + 1;
    }
    proof { hide_user_l4_entries_eof(*krnl, pagetable); }
    Ghost(hidden)
}
}
