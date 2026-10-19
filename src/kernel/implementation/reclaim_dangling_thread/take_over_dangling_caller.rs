use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::take_over_dangling_caller_spec::take_over_dangling_caller_eof_transition_framing;
#[cfg(verus_keep_ghost)]
use super::take_over_dangling_caller_eof::take_over_dangling_caller_eof;

verus! {
/// The thread `thread_ptr` takes over the dangling thread `dangling_ptr` of its killed caller: both drop their call link, and
/// the dangling thread becomes killed, which sinks its lock id below the page lock its reclamation takes.
pub fn take_over_dangling_caller(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, thread_ptr: RwLockThreadPtr, dangling_ptr: RwLockThreadPtr, Tracked(thread_lock_perm): Tracked<&LockPerm>,
    Tracked(dangling_lock_perm): Tracked<&LockPerm>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).thr_mp.dom().contains(thread_ptr),
        old(krnl).thr_mp.spec_index(thread_ptr).view().state is RUNNING || old(krnl).thr_mp.spec_index(thread_ptr).view().state is KILLED
            || old(krnl).thr_mp.spec_index(thread_ptr).view().state is WAITING_REPLY,
        old(krnl).thr_mp.spec_index(thread_ptr).view().caller == Some(dangling_ptr),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thread_ptr, TypedLockMode::Write),
        thread_lock_perm.state() is WriteLock,
        thread_lock_perm.thread_id() == old(lctx).thread_id(),
        thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(dangling_ptr),
        !old(krnl).thr_mp.spec_index(dangling_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(dangling_ptr).view().state is DANGLING,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), dangling_ptr, TypedLockMode::Write),
        dangling_lock_perm.state() is WriteLock,
        dangling_lock_perm.thread_id() == old(lctx).thread_id(),
        dangling_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(dangling_ptr).locking_thread()->Write_lock_id,
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_inserted(old(lctx), final(lctx), KernelObjId::Thread(dangling_ptr), TypedHeldLock { lock_id: final(krnl).thr_mp.lock_id_by_key(dangling_ptr), mode: TypedLockMode::Write }),
        final(krnl).inv(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        *final(krnl) == (KernelK { thr_mp: final(krnl).thr_mp, ..*old(krnl) }),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        forall|t: RwLockThreadPtr| #![trigger final(krnl).thr_mp.spec_index(t)]
            old(krnl).thr_mp.dom().contains(t) && t != thread_ptr && t != dangling_ptr ==> final(krnl).thr_mp.spec_index(t) == old(krnl).thr_mp.spec_index(t),
        final(krnl).thr_mp.spec_index(thread_ptr).view_ghost() == old(krnl).thr_mp.spec_index(thread_ptr).view_ghost(),
        final(krnl).thr_mp.spec_index(thread_ptr).view() == (Thread { caller: None, ..old(krnl).thr_mp.spec_index(thread_ptr).view() }),
        final(krnl).thr_mp.spec_index(thread_ptr).locking_thread() == old(krnl).thr_mp.spec_index(thread_ptr).locking_thread(),
        final(krnl).thr_mp.spec_index(thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(thread_ptr).being_killed(),
        final(krnl).thr_mp.lock_id_by_key(thread_ptr) == old(krnl).thr_mp.lock_id_by_key(thread_ptr),
        final(krnl).thr_mp.spec_index(dangling_ptr).view() == (Thread { state: ThreadState::KILLED, callee: None, ..old(krnl).thr_mp.spec_index(dangling_ptr).view() }),
        final(krnl).thr_mp.spec_index(dangling_ptr).locking_thread() == old(krnl).thr_mp.spec_index(dangling_ptr).locking_thread(),
        !final(krnl).thr_mp.spec_index(dangling_ptr).being_killed(),
        final(krnl).thr_mp.spec_index(dangling_ptr).view().quota_4k == 0,
        final(krnl).thr_mp.spec_index(dangling_ptr).view().quota_2m == 0,
        final(krnl).thr_mp.spec_index(dangling_ptr).view().quota_1g == 0,
        final(krnl).thr_mp.spec_index(dangling_ptr).view().temp_alloc_clean(),
        final(krnl).thr_mp.spec_index(dangling_ptr).view().proc_linkedlist_node.is_init(),
{
    proof {
        thread_perms_wf_at(krnl.thr_mp, thread_ptr); thread_perms_wf_map(krnl.thr_mp); thread_perms_wf_at(krnl.thr_mp, dangling_ptr);
        krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), dangling_ptr);
        krnl.thr_mp.typed_lock_map_aligned_write_at(lctx.thread_lock_map(), lctx.thread_id(), thread_ptr);
    }
    let ghost pre = *krnl;
    {
        let thread_mut = krnl.thr_mp.borrow_mut_typed(thread_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(thread_lock_perm));
        thread_mut.release_caller();
    }
    let ghost old_dangling_lock_id = krnl.thr_mp.lock_id_by_key(dangling_ptr);
    {
        let dangling_mut = krnl.thr_mp.borrow_mut_typed(dangling_ptr, Ghost(lctx.thread_lock_map()), Tracked(&*lctx), Tracked(dangling_lock_perm));
        dangling_mut.dangling_to_killed();
    }
    proof {
        lctx.enter_kernel_view_release();
        lctx.update_lock_id(KernelObjId::Thread(dangling_ptr), old_dangling_lock_id, krnl.thr_mp.lock_id_by_key(dangling_ptr));
        assert(take_over_dangling_caller_eof_transition_framing(pre, *krnl, thread_ptr, dangling_ptr)) by { reveal(take_over_dangling_caller_eof_transition_framing); };
        take_over_dangling_caller_eof(pre, *krnl, thread_ptr, dangling_ptr);
    }
}
} // verus!
