use vstd::prelude::*;
use crate::*;
use super::free_quota_4k::return_free_quota_4k;

verus! {
pub fn refund_unmap_4k_quota(krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, indirect: &mut [usize; MAX_CONTAINER_TREE_DEPTH], direct: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, thread_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(lctx).held_lock_majors_lt(QUOTA_MAJOR),
        old(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        old(steps).snap_shot == kernel_k_to_kernel_u(*old(krnl)),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        *old(direct) == old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
        forall|d: int| #![trigger old(indirect)[d]] 0 <= d < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth ==> old(indirect)[d] == old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
    ensures
        index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> final(krnl).cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        final(lctx).holds_no_allocator_locks(PageSize::SZ4k),
        final(steps).steps == old(steps).steps,
        final(steps).snap_shot == kernel_k_to_kernel_u(*final(krnl)),
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
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)] old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
{
    assert(krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(thread_ptr).inv()) by { reveal(thread_perms_wf); };
    let thread = krnl.thr_mp.borrow_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), thread_perm);
    let thread_depth = thread.container_depth;
    let mut owner = thread.owning_container;
    assert(held_containers_unchanged(krnl.ctn_mp, krnl.ctn_mp, lctx) && held_processes_unchanged(krnl.prc_mp, krnl.prc_mp, lctx) && held_pagetables_unchanged(krnl.pt_mp, krnl.pt_mp, lctx) && held_cpus_unchanged(krnl.cpu_arr, krnl.cpu_arr, lctx)) by { held_kernel_objects_unchanged_reflexive(krnl, lctx); };
    assert(krnl.ctn_mp.dom().contains(owner)) by { reveal(container_thread_wf); };
    assert(krnl.ctn_mp.spec_index(owner).view_rodata().view().depth == thread_depth) by { reveal(container_thread_wf); };
    assert(thread_depth <= MAX_CONTAINER_TREE_DEPTH) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    let mut remaining = thread_depth + 1;
    while remaining > 0
        invariant
            index_valid(NUM_CPUS, old(lctx).cpu_id()) ==> krnl.cpu_published[old(lctx).cpu_id() as int].view() == old(krnl).cpu_published[old(lctx).cpu_id() as int].view(),
            krnl.inv(),
            typed_lock_maps_aligned(krnl, lctx),
            lock_id_set_aligned(lctx),
            lctx.kernel_view_locking_state() is Acquire,
            lctx.held_lock_majors_lt(QUOTA_MAJOR),
            lctx.holds_no_allocator_locks(PageSize::SZ4k),
            steps.snap_shot == kernel_k_to_kernel_u(*krnl),
            krnl.thr_mp.dom().contains(thread_ptr),
            typed_lock_map_contains_mode(lctx.thread_lock_map(), thread_ptr, TypedLockMode::Write),
            thread_perm.view().state() is WriteLock,
            thread_perm.view().thread_id() == lctx.thread_id(),
            thread_perm.view().lock_id() == krnl.thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
            *direct == krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view(),
            forall|d: int| #![trigger indirect[d]] #![trigger krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d)] 0 <= d < krnl.thr_mp.spec_index(thread_ptr).view().container_depth ==> indirect[d] == krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().spec_index(d),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            steps.steps == old(steps).steps,
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
            held_cpus_unchanged(old(krnl).cpu_arr, krnl.cpu_arr, old(lctx)),
            krnl.thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: krnl.thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
            krnl.thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
            krnl.thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
            forall|pt: RwLockPageTableRoot| #![trigger krnl.pt_mp.spec_index(pt)] old(lctx).pagetable_lock_map().dom().contains(pt) && pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view()) ==> pagetable_tlb_entries_present(krnl.cpu_tlb, krnl.cpu_arr, krnl.pcid_needflush, pt, krnl.pt_mp.spec_index(pt).view()),
        decreases remaining,
    {
        let depth = remaining - 1;
        assert(krnl.ctn_mp.perms_wf() && krnl.allc_4k_mp.perms_wf()) by { reveal(container_perms_wf); reveal(allocator_perms_wf); };
        let ro = krnl.ctn_mp.borrow_rodata(owner).borrow();
        let parent = ro.parent;
        let allocator_ptr = ro.allocator_ptr_4k;
        let mut counter = if depth == thread_depth { *direct } else { indirect[depth] };
        if counter != 0 {
            assert(krnl.allc_4k_mp.dom().contains(allocator_ptr) && krnl.allc_4k_mp.spec_index(allocator_ptr).wf() && lctx.allocator_quota_4k_lock_map().dom().is_empty()) by { reveal(container_allocator_wf); reveal(allocator_perms_wf); reveal(LocalContext::holds_no_allocator_locks); };
            let Tracked(quota_perm) = krnl.wlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx));
            return_free_quota_4k(krnl, thread_ptr, owner, depth, allocator_ptr, &mut counter, Tracked(&mut *lctx), thread_perm, Tracked(&quota_perm));
            assert(krnl.allc_4k_mp.spec_index(allocator_ptr).wf()) by { reveal(allocator_perms_wf); };
            krnl.wunlock_allocator_quota_4k(allocator_ptr, Tracked(&mut *lctx), Tracked(quota_perm));
            proof {
                assert(typed_lock_maps_unchanged(old(lctx), lctx)) by { map_insert_remove_absent_lemma(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedHeldLock { lock_id: krnl.allc_4k_mp.spec_index(allocator_ptr).quota.lock_id(), mode: TypedLockMode::Write }); };
                assert(lctx.holds_no_allocator_locks(PageSize::SZ4k)) by { reveal(LocalContext::holds_no_allocator_locks); };
                assert(lctx.held_lock_majors_lt(QUOTA_MAJOR)) by { broadcast use held_lock_major_lt_preserved_for_typed_maps_unchanged; };
                assert(steps.snap_shot == kernel_k_to_kernel_u(*krnl)) by { reveal(kernel_k_to_kernel_u); };
                krnl.kernel_step_boundary(&mut *lctx, &mut *steps);
                assert(krnl.ctn_mp.dom().contains(owner) && krnl.ctn_mp.spec_index(owner).view_rodata().view().parent == parent) by { reveal(thread_perms_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); broadcast use vstd::seq::Seq::lemma_index_contains; };
            }
        }
        if depth == thread_depth { *direct = 0; } else { indirect[depth] = 0; }
        if depth > 0 {
            assert(parent is Some && krnl.ctn_mp.dom().contains(parent.unwrap()) && krnl.ctn_mp.spec_index(parent.unwrap()).view_rodata().view().depth == depth - 1 && krnl.thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int - 1) == parent.unwrap()) by { reveal(container_thread_wf); reveal(container_root_wf); reveal(container_children_depth_wf); reveal(container_uppertree_seq_wf); reveal(container_perms_wf); reveal(container_tree_fields_wf); };
            owner = parent.unwrap();
        }
        remaining = depth;
    }
}
}
