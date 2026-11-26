use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_unmap_2m_refund_to_thread_eof::{refund_unmap_2m_quota_to_thread_eof, refund_unmap_2m_quota_to_thread_eof_transition_framing};

verus! {
/// When the direct pending 2M quota `direct` of the write-held thread `thrd_ptr` is non-zero and the thread's 2M quota stays at
/// most `THREAD_QUOTA_2M_REFUND_CAP` after adding it, moves it into that quota and returns true; otherwise changes nothing and
/// returns false, leaving the pending quota for the thread's container.
pub(super) fn refund_unmap_2m_quota_to_thread(krnl: &mut KernelK, thrd_ptr: RwLockThreadPtr, direct: &mut usize, Tracked(lctx): Tracked<&LocalContext>, thread_perm: Tracked<&LockPerm>)
    -> (credited: bool)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), lctx),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        typed_lock_map_contains_mode(lctx.thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        thread_perm.view().state() is WriteLock,
        thread_perm.view().thread_id() == lctx.thread_id(),
        thread_perm.view().lock_id() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread()->Write_lock_id,
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        *old(direct) == old(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view(),
    ensures
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), lctx),
        credited == (*old(direct) != 0 && *old(direct) <= THREAD_QUOTA_2M_REFUND_CAP && old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m <= THREAD_QUOTA_2M_REFUND_CAP - *old(direct)),
        !credited ==> *final(krnl) == *old(krnl) && *final(direct) == *old(direct),
        credited ==> *final(direct) == 0,
        credited ==> *final(krnl) == (KernelK { thrd_mp: final(krnl).thrd_mp, ..*old(krnl) }),
        credited ==> final(krnl).thrd_mp.unchanged_except(&old(krnl).thrd_mp, thrd_ptr),
        credited ==> final(krnl).thrd_mp.spec_index(thrd_ptr).view() == (Thread { quota_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m,
            direct_free_quota_pending_2m: final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m, ..old(krnl).thrd_mp.spec_index(thrd_ptr).view() }),
        credited ==> final(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m == old(krnl).thrd_mp.spec_index(thrd_ptr).view().quota_2m + *old(direct),
        credited ==> final(krnl).thrd_mp.spec_index(thrd_ptr).view().direct_free_quota_pending_2m.view() == 0,
        credited ==> final(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread() == old(krnl).thrd_mp.spec_index(thrd_ptr).locking_thread(),
        credited ==> final(krnl).thrd_mp.spec_index(thrd_ptr).being_killed() == old(krnl).thrd_mp.spec_index(thrd_ptr).being_killed(),
{
    assert(krnl.thrd_mp.perms_wf() && krnl.thrd_mp.spec_index(thrd_ptr).inv()) by { thread_perms_wf_implies_map_perms_wf(krnl.thrd_mp); thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); };
    let quota = krnl.thrd_mp.borrow_typed(thrd_ptr, Ghost(lctx.thread_lock_map()), Tracked(lctx), thread_perm).quota_2m;
    let amount = *direct;
    if amount != 0 && amount <= THREAD_QUOTA_2M_REFUND_CAP && quota <= THREAD_QUOTA_2M_REFUND_CAP - amount {
        thread_map_refund_direct_free_quota_pending_2m(&mut krnl.thrd_mp, thrd_ptr, direct, Tracked(lctx), thread_perm);
        proof {
            assert(refund_unmap_2m_quota_to_thread_eof_transition_framing(*old(krnl), *krnl, thrd_ptr, amount)) by { reveal(refund_unmap_2m_quota_to_thread_eof_transition_framing); };
            refund_unmap_2m_quota_to_thread_eof(*old(krnl), *krnl, thrd_ptr, amount);
        }
        true
    } else { false }
}
} // verus!
