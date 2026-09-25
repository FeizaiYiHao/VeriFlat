use vstd::prelude::*;
use crate::*;

verus! {
pub fn return_free_quota_4k(krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr, counter: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, thread_perm: Tracked<&LockPerm>, quota_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        lock_id_set_aligned(old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr,
        depth <= old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth,
        if depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { owner == old(krnl).thr_mp.spec_index(thread_ptr).view().owning_container } else { old(krnl).thr_mp.spec_index(thread_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.is_init(),
        *old(counter) == old(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_4k_lock_map(), allocator_ptr, TypedLockMode::Write),
        quota_perm.view().state() is WriteLock,
        quota_perm.view().thread_id() == old(lctx).thread_id(),
        quota_perm.view().lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        lock_id_set_aligned(final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).lock_id_set() == old(lctx).lock_id_set(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        *final(counter) == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k, indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == if depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { 0usize } else { old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() },
        final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() == if depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, 0usize) } else { old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.inv(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.lock_id(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().value == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().value + *old(counter),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages == old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool == old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool,
        *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
{
    assert(krnl.allc_4k_mp.spec_index(allocator_ptr).quota.view().value as int + *counter as int <= krnl.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view()) by {
        reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_process_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf); reveal(process_perms_wf); reveal(thread_perms_wf);
        let direct = krnl.ctn_mp.spec_index(owner).view_ghost().owned_threads.view();
        let indirect = krnl.ctn_mp.spec_index(owner).view_ghost().owned_indirect_threads.view();
        lemma_process_effective_quota_4k_fold_nonneg(krnl.ctn_mp.spec_index(owner).view().owned_processes.view(), krnl.prc_mp);
        let effective = |t: RwLockThreadPtr| thread_effective_quota_4k(krnl.thr_mp.spec_index(t));
        assert((|sum: int, t: RwLockThreadPtr| sum + effective(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + thread_effective_quota_4k(krnl.thr_mp.spec_index(t))) && direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + effective(t)) >= 0) by { lemma_set_fold_int_sum_nonneg(direct, effective); };
        lemma_thread_direct_pending_4k_fold_nonneg(direct, krnl.thr_mp);
        lemma_thread_indirect_pending_4k_fold_nonneg(indirect, krnl.thr_mp, depth as int);
        if depth == krnl.thr_mp.spec_index(thread_ptr).view().container_depth {
            let value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
            assert((|sum: int, t: RwLockThreadPtr| sum + value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view()) && direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + value(t)) >= value(thread_ptr)) by { lemma_set_fold_int_sum_ge_member(direct, value, thread_ptr); };
        } else {
            let value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth as int) as int;
            assert((|sum: int, t: RwLockThreadPtr| sum + value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(depth as int)) && indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + value(t)) >= value(thread_ptr)) by { lemma_set_fold_int_sum_ge_member(indirect, value, thread_ptr); };
        }
    };
    let amount = *counter;
    assert(krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { reveal(allocator_perms_wf); reveal(container_allocator_wf); };
    assert(krnl.thr_mp.spec_index(thread_ptr).inv()) by { thread_perms_wf_at(krnl.thr_mp, thread_ptr); };
    thread_map_clear_free_quota_pending_4k(&mut krnl.thr_mp, thread_ptr, depth, counter, Tracked(&*lctx), thread_perm);
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), quota_perm);
        quota.value = quota.value + amount;
    }
    proof {
        assert(krnl.subsystems_inv()) by { reveal(allocator_perms_wf); reveal(KernelK::default_pagetable_wf); };
        assert(krnl.memory_management_inv()) by {
            assert(allocator_pages_wf(krnl.pg_arr, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { lemma_allocator_pages_wf_preserved_for_allocator_quota_value_framed_fields_forall(); };
            assert(container_allocator_wf(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp)) by { reveal(container_allocator_wf); };
            assert(krnl.allocator_free_pages_wf()) by { reveal(allocator_free_page_ptrs_wf); };
            assert(container_allocator_free_4k_page_wf(krnl.allc_4k_mp, krnl.pg_arr)) by { reveal(container_allocator_free_4k_page_wf); reveal(container_allocator_global_free_4k_page_wf); reveal(container_allocator_cpu_cache_free_4k_page_wf); };
            assert(thread_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_pages_wf); };
            assert(thread_staged_pages_wf(krnl.thr_mp, krnl.pg_arr)) by { reveal(thread_staged_pages_4k_wf); reveal(thread_staged_pages_2m_wf); reveal(thread_staged_pages_1g_wf); };
            assert(container_process_allocator_quota_4k_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_4k_mp)) by {
                reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); reveal(container_thread_wf); reveal(container_uppertree_seq_wf);
                lemma_thread_effective_quota_4k_fold_sum_eq_forall();
                if !(forall|c: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k]
                    krnl.ctn_mp.dom().contains(c) ==> (process_effective_quota_4k_fold_sum(krnl.ctn_mp.spec_index(c).view().owned_processes.view(), krnl.prc_mp)
                    + thread_effective_quota_4k_fold_sum(krnl.ctn_mp.spec_index(c).view_ghost().owned_threads.view(), krnl.thr_mp)
                    + thread_direct_pending_4k_fold_sum(krnl.ctn_mp.spec_index(c).view_ghost().owned_threads.view(), krnl.thr_mp)
                    + thread_indirect_pending_4k_fold_sum_at_depth(krnl.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view(), krnl.thr_mp, krnl.ctn_mp.spec_index(c).view_rodata().view().depth as int)
                    + krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
                    == krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).total_free_pages.view())) {
                    let c = choose|c: RwLockContainerPtr| #![trigger krnl.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k] krnl.ctn_mp.dom().contains(c) && !(process_effective_quota_4k_fold_sum(krnl.ctn_mp.spec_index(c).view().owned_processes.view(), krnl.prc_mp)
                    + thread_effective_quota_4k_fold_sum(krnl.ctn_mp.spec_index(c).view_ghost().owned_threads.view(), krnl.thr_mp)
                    + thread_direct_pending_4k_fold_sum(krnl.ctn_mp.spec_index(c).view_ghost().owned_threads.view(), krnl.thr_mp)
                    + thread_indirect_pending_4k_fold_sum_at_depth(krnl.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view(), krnl.thr_mp, krnl.ctn_mp.spec_index(c).view_rodata().view().depth as int)
                    + krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).quota.view().view()
                    == krnl.allc_4k_mp.spec_index(krnl.ctn_mp.spec_index(c).view_rodata().view().allocator_ptr_4k).total_free_pages.view());
                    let direct = krnl.ctn_mp.spec_index(c).view_ghost().owned_threads.view();
                    let indirect = krnl.ctn_mp.spec_index(c).view_ghost().owned_indirect_threads.view();
                    let c_depth = krnl.ctn_mp.spec_index(c).view_rodata().view().depth as int;
                    if c == owner && depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth {
                        let pre_value = |t: RwLockThreadPtr| old(krnl).thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
                        let post_value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view() as int;
                        assert({
                            &&& (|sum: int, t: RwLockThreadPtr| sum + pre_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + old(krnl).thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view())
                            &&& (|sum: int, t: RwLockThreadPtr| sum + post_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().direct_free_quota_pending_4k.view())
                            &&& direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + post_value(t)) == direct.fold(0int, |sum: int, t: RwLockThreadPtr| sum + pre_value(t)) - amount
                        }) by { lemma_set_fold_int_sum_change_by(direct, pre_value, post_value, thread_ptr, -(amount as int)); };
                    } else {
                        lemma_thread_direct_pending_4k_fold_eq(direct, old(krnl).thr_mp, krnl.thr_mp);
                    }
                    if c == owner && depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth {
                        let pre_value = |t: RwLockThreadPtr| old(krnl).thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(c_depth) as int;
                        let post_value = |t: RwLockThreadPtr| krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(c_depth) as int;
                        assert({
                            &&& (|sum: int, t: RwLockThreadPtr| sum + pre_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + old(krnl).thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(c_depth))
                            &&& (|sum: int, t: RwLockThreadPtr| sum + post_value(t)) =~= (|sum: int, t: RwLockThreadPtr| sum + krnl.thr_mp.spec_index(t).view().indirect_free_quota_pending_4k.view().spec_index(c_depth))
                            &&& indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + post_value(t)) == indirect.fold(0int, |sum: int, t: RwLockThreadPtr| sum + pre_value(t)) - amount
                        }) by { lemma_set_fold_int_sum_change_by(indirect, pre_value, post_value, thread_ptr, -(amount as int)); };
                    } else {
                        lemma_thread_indirect_pending_4k_fold_eq_at_depth(indirect, old(krnl).thr_mp, krnl.thr_mp, c_depth);
                    }
                }
            };
            assert(container_process_allocator_quota_2m_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_2m_mp)) by { container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_2m_mp); };
            assert(container_process_allocator_quota_1g_wf(krnl.ctn_mp, krnl.prc_mp, krnl.thr_mp, krnl.allc_1g_mp)) by { container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(krnl.ctn_mp, krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.allc_1g_mp); };
        };
        assert(krnl.process_management_inv()) by {
            thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
            thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
            container_thread_endpoint_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.ep_mp);
            container_thread_scheduler_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp, krnl.sched_mp);
            container_thread_wf_preserved_for_thread_process_management_fields(krnl.ctn_mp, old(krnl).thr_mp, krnl.thr_mp);
            process_thread_wf_preserved_for_thread_process_management_fields(krnl.prc_mp, old(krnl).thr_mp, krnl.thr_mp);
            thread_cpu_wf_preserved_for_thread_process_management_fields(old(krnl).thr_mp, krnl.thr_mp, krnl.cpu_arr);
            assert(thread_caller_callee_wf(krnl.thr_mp)) by { reveal(thread_caller_callee_wf); };
        };
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        };
    }
}
}
