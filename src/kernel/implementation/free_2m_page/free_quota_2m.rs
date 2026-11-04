use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::free_quota_2m_eof::{return_free_quota_2m_eof, return_free_quota_2m_eof_transition_framing};

verus! {
pub fn return_free_quota_2m(krnl: &mut KernelK, thrd_ptr: RwLockThreadPtr, owner: RwLockContainerPtr, depth: usize, allc_ptr: RwLockPageAllocatorPtr, counter: &mut usize, Tracked(lctx): Tracked<&mut LocalContext>, thread_perm: Tracked<&LockPerm>, quota_perm: Tracked<&LockPerm>)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(lctx).kernel_view_locking_state() is Acquire,
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        old(krnl).ctn_mp.dom().contains(owner),
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().depth == depth,
        old(krnl).ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_2m == allc_ptr,
        depth <= old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth,
        if depth == old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { owner == old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container } else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().upper_container_seq.view().spec_index(depth as int) == owner },
        old(krnl).allc_2m_mp.spec_index(allc_ptr).quota.is_init(),
        *old(counter) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == old(lctx).thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(old(lctx).allocator_quota_2m_lock_map(), allc_ptr, TypedLockMode::Write),
        quota_perm.view().state() is WriteLock,
        quota_perm.view().thread_id() == old(lctx).thread_id(),
        quota_perm.view().lock_id() == old(krnl).allc_2m_mp.spec_index(allc_ptr).quota.locking_thread()->Write_lock_id,
    ensures
        final(krnl).inv(),
        kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), final(krnl)),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        *final(counter) == 0,
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().free_quota_pending_2m_at_depth(depth) == 0,
        final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
        final(krnl).thrd_mp.dom() == old(krnl).thrd_mp.dom(),
        final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost() == old(krnl).thrd_mp.spec_index(thrd_ptr).view_ghost(),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { direct_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m,
            indirect_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() == if depth == old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { 0usize } else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() },
        final(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view()
            == if depth < old(krnl).thrd_mp.spec_index(thrd_ptr).view().container_depth { old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view().update(depth as int, 0usize) }
            else { old(krnl).thrd_mp.spec_index(thrd_ptr).view().indirect_free_quota_pending_2m.view() },
        final(krnl).allc_2m_mp.spec_index(allc_ptr).quota.inv(),
        final(krnl).allc_2m_mp.spec_index(allc_ptr).quota.locking_thread() == old(krnl).allc_2m_mp.spec_index(allc_ptr).quota.locking_thread(),
        final(krnl).allc_2m_mp.spec_index(allc_ptr).quota.lock_id() == old(krnl).allc_2m_mp.spec_index(allc_ptr).quota.lock_id(),
        final(krnl).allc_2m_mp.unchanged_except(&old(krnl).allc_2m_mp, allc_ptr),
        final(krnl).allc_2m_mp.spec_index(allc_ptr).quota.view().value == old(krnl).allc_2m_mp.spec_index(allc_ptr).quota.view().value + *old(counter),
        final(krnl).allc_2m_mp.spec_index(allc_ptr).total_free_pages == old(krnl).allc_2m_mp.spec_index(allc_ptr).total_free_pages,
        final(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches == old(krnl).allc_2m_mp.spec_index(allc_ptr).cpu_caches,
        final(krnl).allc_2m_mp.spec_index(allc_ptr).global_pool == old(krnl).allc_2m_mp.spec_index(allc_ptr).global_pool,
        *final(krnl) == (KernelK { thrd_mp: final(krnl).thrd_mp, allc_2m_mp: final(krnl).allc_2m_mp, ..*old(krnl) }),
        kernel_container_quota_2m_changed(old(krnl), final(krnl), owner, *old(counter) as int),
{
    assert(krnl.allc_2m_mp.spec_index(allc_ptr).quota.view().value as int + *counter as int <= krnl.allc_2m_mp.spec_index(allc_ptr).total_free_pages.view()) by { kernel_inv_implies_thread_pending_2m_quota_bounded(krnl, thrd_ptr, owner, depth); };
    let amount = *counter;
    assert(krnl.allc_2m_mp.perms_wf() && krnl.allc_2m_mp.dom().contains(allc_ptr)) by { allocator_perms_wf_map(krnl.allc_2m_mp); container_allocator_wf_at(krnl.ctn_mp, krnl.allc_4k_mp, krnl.allc_2m_mp, krnl.allc_1g_mp, owner); };
    thread_map_clear_free_quota_pending_2m(&mut krnl.thrd_mp, thrd_ptr, depth, counter, Tracked(&*lctx), thread_perm);
    {
        let quota = krnl.allc_2m_mp.borrow_mut_quota_typed(allc_ptr, Ghost(lctx.allocator_quota_2m_lock_map()), Ghost(lctx.allocator_cache_2m_lock_map()), Ghost(lctx.allocator_global_pool_2m_lock_map()), Tracked(&*lctx), quota_perm);
        quota.value = quota.value + amount;
    }
    proof {
        assert(kernel_cpu_process_thread_nonlock_fields_unchanged(old(krnl), krnl)) by {
            broadcast use group_kernel_cpu_process_thread_nonlock_fields_unchanged_transitive;
            reveal(kernel_cpu_process_thread_nonlock_fields_unchanged); reveal(kernel_thread_nonlock_fields_unchanged);
        };
        assert(return_free_quota_2m_eof_transition_framing(*old(krnl), *krnl, thrd_ptr, depth, allc_ptr, amount)) by { reveal(return_free_quota_2m_eof_transition_framing); };
        return_free_quota_2m_eof(*old(krnl), *krnl, thrd_ptr, owner, depth, allc_ptr, amount);
    }
}
}
