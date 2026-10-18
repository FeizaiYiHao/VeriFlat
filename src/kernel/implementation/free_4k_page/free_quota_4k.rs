use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::free_quota_4k_eof::{return_free_quota_4k_eof, return_free_quota_4k_eof_transition_framing};

verus! {
pub fn return_free_quota_4k(krnl: &mut KernelK, thread_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allocator_ptr: RwLockPageAllocatorPtr, counter: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, thread_perm: Tracked<&LockPerm>, quota_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
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
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        *final(counter) == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).view().free_quota_pending_4k_at_depth(depth) == 0,
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        final(krnl).thr_mp.unchanged_except(&old(krnl).thr_mp, thread_ptr),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { direct_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k,
            indirect_free_quota_pending_4k: final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() == if depth == old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { 0usize } else { old(krnl).thr_mp.spec_index(thread_ptr).view().direct_free_quota_pending_4k.view() },
        final(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view()
            == if depth < old(krnl).thr_mp.spec_index(thread_ptr).view().container_depth { old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view().update(depth as int, 0usize) }
            else { old(krnl).thr_mp.spec_index(thread_ptr).view().indirect_free_quota_pending_4k.view() },
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.inv(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.locking_thread(),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.lock_id() == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.lock_id(),
        final(krnl).allc_4k_mp.unchanged_except(&old(krnl).allc_4k_mp, allocator_ptr),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().value == old(krnl).allc_4k_mp.spec_index(allocator_ptr).quota.view().value + *old(counter),
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages == old(krnl).allc_4k_mp.spec_index(allocator_ptr).total_free_pages,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches == old(krnl).allc_4k_mp.spec_index(allocator_ptr).cpu_caches,
        final(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool == old(krnl).allc_4k_mp.spec_index(allocator_ptr).global_pool,
        *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, allc_4k_mp: final(krnl).allc_4k_mp, ..*old(krnl) }),
        kernel_container_quota_4k_changed(old(krnl), final(krnl), owner, *old(counter) as int),
{
    assert(krnl.allc_4k_mp.spec_index(allocator_ptr).quota.view().value as int + *counter as int <= krnl.allc_4k_mp.spec_index(allocator_ptr).total_free_pages.view()) by { lemma_thread_pending_4k_quota_bounded(krnl, thread_ptr, owner, depth); };
    let amount = *counter;
    assert(krnl.allc_4k_mp.perms_wf() && krnl.allc_4k_mp.dom().contains(allocator_ptr)) by { allocator_perms_wf_map(krnl.allc_4k_mp); container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); };
    thread_map_clear_free_quota_pending_4k(&mut krnl.thr_mp, thread_ptr, depth, counter, Tracked(&*lctx), thread_perm);
    {
        let quota = krnl.allc_4k_mp.borrow_mut_quota_typed(allocator_ptr, Ghost(lctx.allocator_quota_4k_lock_map()), Ghost(lctx.allocator_cache_4k_lock_map()), Ghost(lctx.allocator_global_pool_4k_lock_map()), Tracked(&*lctx), quota_perm);
        quota.value = quota.value + amount;
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        };
        assert(return_free_quota_4k_eof_transition_framing(*old(krnl), *krnl, thread_ptr, depth, allocator_ptr, amount)) by { reveal(return_free_quota_4k_eof_transition_framing); };
        return_free_quota_4k_eof(*old(krnl), *krnl, thread_ptr, owner, depth, allocator_ptr, amount);
    }
}
}
