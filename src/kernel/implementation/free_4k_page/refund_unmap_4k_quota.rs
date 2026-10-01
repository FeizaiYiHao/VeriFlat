use vstd::prelude::*;
use crate::*;
use super::free_quota_4k::return_free_quota_4k;

verus! {
pub fn refund_unmap_4k_quota(krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, thread_perm: Tracked<&LockPerm>)
    requires
        old(steps).snapshot_k() == *old(krnl),
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).pcid_needflush_lock_map().dom().is_empty(),
        forall|held_cpu_id: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(held_cpu_id)] old(lctx).cpu_lock_map().dom().contains(held_cpu_id) ==> !(old(krnl).cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
        forall|held_page: PageIndex| #![trigger old(lctx).page_lock_map().dom().contains(held_page)] old(lctx).page_lock_map().dom().contains(held_page) ==> old(krnl).pg_arr.lock_id_by_index(held_page).major < QUOTA_MAJOR,
        old(lctx).allocator_quota_4k_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_2m_lock_map().dom().is_empty(),
        old(lctx).allocator_quota_1g_lock_map().dom().is_empty(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&old(steps).snapshot_k(), old(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(old(steps).snapshot_k().ep_mp, old(krnl).ep_mp),
        old(krnl).irt.owners() == old(steps).snapshot_k().irt.owners(),
        old(krnl).irt.iommu_roots() == old(steps).snapshot_k().irt.iommu_roots(),
        old(krnl).cpu_tlb.view() == old(steps).snapshot_k().cpu_tlb.view(),
        old(krnl).iommu_tlb.view() == old(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&old(steps).snapshot_k(), old(krnl)),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger old(indirect)[d]] 0 <= d < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[d] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
        index_valid(NUM_CPUS, old(lctx).cpu_id()),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), old(lctx).cpu_id(), TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable, TypedLockMode::Write),
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + MAX_CONTAINER_TREE_DEPTH + 1,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> {
            let old_u = final(steps).view()[j].old_u;
            let thread = old(krnl).thr_mp.spec_index(thread_ptr).view();
            &&& kernel_u_container_quota_4k_increased(old_u, final(steps).view()[j].new_u, thread.owning_container)
            &&& old_u.cpu_array[old(lctx).cpu_id() as int].lock_state is WriteLocked
            &&& old_u.cpu_array[old(lctx).cpu_id() as int].current_thread == old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_thread
            &&& old_u.thread_map.dom().contains(thread_ptr)
            &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
            &&& old_u.thread_map[thread_ptr].owning_container == thread.owning_container
            &&& old_u.thread_map[thread_ptr].owning_proc == thread.owning_proc
            &&& old_u.thread_map[thread_ptr].syscall_progress == thread.syscall_progress.view()
            &&& old_u.process_map.dom().contains(thread.owning_proc)
            &&& old_u.process_map[thread.owning_proc].lock_state is WriteLocked
            &&& old_u.process_map[thread.owning_proc].pagetable is Some
            &&& old_u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is WriteLocked
            &&& old_u.container_map.dom().contains(thread.owning_container)
            &&& old_u.container_map[thread.owning_container].lock_state is WriteLocked
        },
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        old(steps).nonlock_view().len() <= final(steps).nonlock_view().len(),
        final(steps).nonlock_view().len() <= old(steps).nonlock_view().len() + MAX_CONTAINER_TREE_DEPTH + 1,
        final(steps).nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*final(krnl)),
        kernel_cpu_process_thread_nonlock_fields_unchanged(&final(steps).snapshot_k(), final(krnl)),
        kernel_endpoint_nonlock_fields_unchanged(final(steps).snapshot_k().ep_mp, final(krnl).ep_mp),
        final(krnl).irt.owners() == final(steps).snapshot_k().irt.owners(),
        final(krnl).irt.iommu_roots() == final(steps).snapshot_k().irt.iommu_roots(),
        final(krnl).cpu_tlb.view() == final(steps).snapshot_k().cpu_tlb.view(),
        final(krnl).iommu_tlb.view() == final(steps).snapshot_k().iommu_tlb.view(),
        kernel_container_nonlock_fields_and_quotas_unchanged(&final(steps).snapshot_k(), final(krnl)),
        held_containers_unchanged(old(krnl).ctn_mp, final(krnl).ctn_mp, old(lctx)),
        held_processes_unchanged(old(krnl).prc_mp, final(krnl).prc_mp, old(lctx)),
        held_pagetables_unchanged(old(krnl).pt_mp, final(krnl).pt_mp, old(lctx)),
        held_cpus_unchanged(old(krnl).cpu_arr, final(krnl).cpu_arr, old(lctx)),
        final(krnl).thr_mp.dom().contains(thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        *final(direct) == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == 0,
        forall|d: int| #![trigger final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < final(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d) == 0,
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            old(lctx).pagetable_lock_map().dom().contains(pt)
            && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
{
    hide(Seq::contains);
    assert(krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(thread_ptr).inv()) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
    let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
    let thread_depth = thread.container_depth;
    let mut owner = thread.owning_container;
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_pagetables_unchanged(krnl.pt_mp, krnl.pt_mp, lctx) && held_pages_unchanged(krnl.pg_arr, krnl.pg_arr, lctx) && held_cpus_unchanged(krnl.cpu_arr, krnl.cpu_arr, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.ctn_mp.dom().contains(owner)) by { container_thread_wf_at(krnl.ctn_mp, krnl.thr_mp, thread_ptr); };
    assert(krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == thread_depth) by { reveal(container_thread_wf); };
    assert(thread_depth <= MAX_CONTAINER_TREE_DEPTH) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    let mut remaining = thread_depth + 1;
    proof { steps.rebase_snapshot_k_if_unchanged(&*krnl); }
    while remaining > 0
        invariant
            steps.snapshot_k() == *krnl,
            old(steps).view().len() <= steps.view().len() <= old(steps).view().len() + thread_depth + 1 - remaining,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> {
                let old_u = steps.view()[j].old_u;
                let thread = old(krnl).thr_mp.spec_index(thread_ptr).view();
                &&& kernel_u_container_quota_4k_increased(old_u, steps.view()[j].new_u, thread.owning_container)
                &&& old_u.cpu_array[old(lctx).cpu_id() as int].lock_state is WriteLocked
                &&& old_u.cpu_array[old(lctx).cpu_id() as int].current_thread == old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_thread
                &&& old_u.thread_map.dom().contains(thread_ptr)
                &&& old_u.thread_map[thread_ptr].lock_state is WriteLocked
                &&& old_u.thread_map[thread_ptr].owning_container == thread.owning_container
                &&& old_u.thread_map[thread_ptr].owning_proc == thread.owning_proc
                &&& old_u.thread_map[thread_ptr].syscall_progress == thread.syscall_progress.view()
                &&& old_u.process_map.dom().contains(thread.owning_proc)
                &&& old_u.process_map[thread.owning_proc].lock_state is WriteLocked
                &&& old_u.process_map[thread.owning_proc].pagetable is Some
                &&& old_u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is WriteLocked
                &&& old_u.container_map.dom().contains(thread.owning_container)
                &&& old_u.container_map[thread.owning_container].lock_state is WriteLocked
            },
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lctx.kernel_view_locking_state() is Acquire,
            steps.nonlock_snapshot_u() == kernel_k_to_nonlock_kernel_u(*krnl),
            kernel_cpu_process_thread_nonlock_fields_unchanged(&steps.snapshot_k(), krnl),
            kernel_endpoint_nonlock_fields_unchanged(steps.snapshot_k().ep_mp, krnl.ep_mp),
            krnl.irt.owners() == steps.snapshot_k().irt.owners(),
            krnl.irt.iommu_roots() == steps.snapshot_k().irt.iommu_roots(),
            krnl.cpu_tlb.view() == steps.snapshot_k().cpu_tlb.view(),
            krnl.iommu_tlb.view() == steps.snapshot_k().iommu_tlb.view(),
            kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), krnl),
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            *direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.pcid_needflush_lock_map().dom().is_empty(),
            forall|held_cpu_id: CpuId| #![trigger lctx.cpu_lock_map().dom().contains(held_cpu_id)] lctx.cpu_lock_map().dom().contains(held_cpu_id) ==> !(krnl.cpu_arr.spec_index(held_cpu_id).view().view().view().state is Off),
            forall|held_page: PageIndex| #![trigger lctx.page_lock_map().dom().contains(held_page)] lctx.page_lock_map().dom().contains(held_page) ==> krnl.pg_arr.lock_id_by_index(held_page).major < QUOTA_MAJOR,
            lctx.allocator_quota_4k_lock_map().dom().is_empty(),
            lctx.allocator_quota_2m_lock_map().dom().is_empty(),
            lctx.allocator_quota_1g_lock_map().dom().is_empty(),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            old(steps).nonlock_view().len() <= steps.nonlock_view().len(),
            steps.nonlock_view().len() <= old(steps).nonlock_view().len() + thread_depth + 1 - remaining,
            remaining <= thread_depth + 1,
            thread_depth <= MAX_CONTAINER_TREE_DEPTH,
            thread_depth == krnl.thr_mp.spec_index(thread_ptr).view().container_depth,
            krnl.ctn_mp.dom().contains(owner),
            remaining > 0 ==> krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == remaining - 1,
            remaining > 0 ==> (if remaining == thread_depth + 1 { owner == krnl.thr_mp.spec_index(thread_ptr).view().owning_container } else { krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(remaining as int - 1) == owner }),
            remaining <= thread_depth ==> *direct == 0,
            forall|d: int| #![trigger indirect[d]] remaining <= d < thread_depth ==> indirect[d] == 0,
            held_containers_unchanged(old(krnl).ctn_mp, krnl.ctn_mp, old(lctx)),
            held_processes_unchanged(old(krnl).prc_mp, krnl.prc_mp, old(lctx)),
            held_pagetables_unchanged(old(krnl).pt_mp, krnl.pt_mp, old(lctx)),
            held_pages_unchanged(old(krnl).pg_arr, krnl.pg_arr, old(lctx)),
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view())]
                old(lctx).pagetable_lock_map().dom().contains(pt)
                && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
                ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
            old(krnl).thr_mp.dom().contains(thread_ptr),
            index_valid(NUM_CPUS, old(lctx).cpu_id()),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), old(lctx).cpu_id(), TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).process_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc, TypedLockMode::Write),
            typed_lock_map_contains_mode(old(lctx).container_lock_map(), old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container, TypedLockMode::Write),
            !old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().zombie,
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), old(krnl).prc_mp.spec_index(old(krnl).thr_mp.spec_index(thread_ptr).view().owning_proc).view().pagetable, TypedLockMode::Write),
        decreases remaining,
    {
        let depth = remaining - 1;
        proof {
            use_type_invariant(&*steps);
            assert({
                let u = steps.snapshot_u();
                let thread = old(krnl).thr_mp.spec_index(thread_ptr).view();
                &&& u.cpu_array[old(lctx).cpu_id() as int].lock_state is WriteLocked
                &&& u.cpu_array[old(lctx).cpu_id() as int].current_thread == old(krnl).cpu_arr.spec_index(old(lctx).cpu_id()).view().view().view().current_thread
                &&& u.thread_map.dom().contains(thread_ptr)
                &&& u.thread_map[thread_ptr].lock_state is WriteLocked
                &&& u.thread_map[thread_ptr].owning_container == thread.owning_container
                &&& u.thread_map[thread_ptr].owning_proc == thread.owning_proc
                &&& u.thread_map[thread_ptr].syscall_progress == thread.syscall_progress.view()
                &&& u.process_map.dom().contains(thread.owning_proc)
                &&& u.process_map[thread.owning_proc].lock_state is WriteLocked
                &&& u.process_map[thread.owning_proc].pagetable is Some
                &&& u.process_map[thread.owning_proc].pagetable->Some_0.lock_state is WriteLocked
                &&& u.container_map.dom().contains(thread.owning_container)
                &&& u.container_map[thread.owning_container].lock_state is WriteLocked
            }) by {
                kernel_write_held_context_projection(&*krnl, &*lctx, lctx.cpu_id(), krnl.thr_mp.spec_index(thread_ptr).view().owning_proc, thread_ptr, None);
            };
        }
        assert(krnl.ctn_mp.perms_wf() && krnl.allc_4k_mp.perms_wf()) by { container_perms_wf_at(krnl.ctn_mp, owner); reveal(allocator_perms_wf); };
        let ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
        let parent = ro.parent;
        let allocator_ptr = ro.allocator_ptr_4k;
        assert(depth > 0 ==> parent is Some && krnl.ctn_mp.dom().contains(parent.unwrap()) && krnl.ctn_mp.spec_index(parent.unwrap()).view_rodata().view().depth == depth - 1
            && krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int - 1) == parent.unwrap()) by {
            reveal(Seq::contains); reveal(container_thread_wf); reveal(container_root_wf); reveal(container_children_depth_wf); reveal(container_uppertree_seq_wf);
            reveal(container_perms_wf); reveal(container_tree_fields_wf);
        };
        let mut counter = if depth == thread_depth { *direct } else { indirect[depth] };
        if counter != 0 {
            let amount = counter;
            assert(krnl.allc_4k_mp.dom().contains(allocator_ptr) && krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by { reveal(container_allocator_wf); reveal(allocator_perms_wf); };
            proof {
                let origin = old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container;
                assert(steps.snapshot_k().ctn_mp.dom().contains(origin) && (owner == origin || steps.snapshot_k().ctn_mp.spec_index(origin).view_ghost().uppertree_seq.view().contains(owner))) by {
                    reveal(container_thread_wf); reveal(thread_perms_wf); broadcast use vstd::seq::Seq::lemma_index_contains;
                };
            }
            let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
            proof {
                assert(kernel_container_nonlock_fields_and_quotas_unchanged(&steps.snapshot_k(), &*krnl)) by { reveal(kernel_container_nonlock_fields_and_quotas_unchanged); };
            }
            return_free_quota_4k(krnl, thread_ptr, owner, depth, allocator_ptr, &mut counter, Tracked(&mut *lctx), thread_perm, Tracked(&quota_perm));
            assert(krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by { reveal(allocator_perms_wf); };
            krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
            proof {
                assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedHeldLock { lock_id: krnl.allc_4k_mp.spec_index(allocator_ptr).quota.lock_id(), mode: TypedLockMode::Write }); };
                assert(kernel_container_quota_4k_changed(&steps.snapshot_k(), &*krnl, owner, amount as int)) by {
                    reveal(kernel_container_quota_4k_changed); reveal(kernel_cpu_process_thread_nonlock_fields_unchanged);
                    broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive; reveal(kernel_container_nonlock_fields_and_quotas_unchanged);
                    broadcast use kernel_endpoint_nonlock_fields_unchanged_transitive; reveal(container_allocator_wf);
                };
                krnl.kernel_step_boundary_container_quota_4k_changed(&mut *lctx, &mut *steps, owner, amount as int, old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container);
                assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().parent == parent && (depth > 0 ==> krnl.ctn_mp.dom().contains(parent.unwrap()) && krnl.ctn_mp.spec_index(parent.unwrap()).view_rodata().view().depth == depth - 1)) by { reveal(thread_perms_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); broadcast use vstd::seq::Seq::lemma_index_contains; };
            }
        }
        if depth == thread_depth { *direct = 0; } else { indirect[depth] = 0; }
        if depth > 0 { owner = parent.unwrap(); }
        remaining = depth;
    }
}
}
