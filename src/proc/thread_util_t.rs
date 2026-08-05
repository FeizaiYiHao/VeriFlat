use vstd::prelude::*;
verus! {

use crate::*;
use vstd::simple_pptr::*;

    /// TCB: reinterpret a raw 4k page's memory as a fresh, WRITE-LOCKED
    /// `RwLock<Thread>` and mint the corresponding `LockPerm`.
    ///
    /// This is a MINT, not an acquire: the page is exclusively ours (staged,
    /// slot write-locked), so no other thread can contend on the new thread
    /// lock and no wait cycle is possible. The retype reinterprets the page's
    /// physical memory as a `ThreadRwLock`, initializes it with `thread_value`,
    /// sets the lock state to Write, and registers `Thread(page_ptr)` in `lctx`.
    ///
    /// The `thread_map` domain growth is done separately by
    /// `LockedMap::insert_with_perm`; the page-state flip and process unstage
    /// stay in verified code.
    #[verifier::external_body]
    pub fn retype_page_perm_to_thread(
        page_ptr: PagePtr,
        thread_value: Thread,
        Tracked(page_perm): Tracked<PagePerm4k>,
        Tracked(lctx): Tracked<&mut LocalContext>,
        obj_id: Ghost<KernelObjId>,
    ) -> (ret: (Tracked<PointsTo<ThreadRwLock>>, Tracked<LockPerm>))
        requires
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            thread_value.inv(),
            old(lctx).obj_id_fresh(obj_id.view()),
        ensures
            // ---- the ThreadRwLock: initialized, write-locked, holds thread_value ----
            ret.0.view().addr() == page_ptr,
            ret.0.view().is_init(),
            ret.0.view().value().is_init(),
            ret.0.view().value().view() == thread_value,
            ret.0.view().value().being_killed() == false,
            ret.0.view().value().locking_thread() == (RwLockState::Write {
                thread_id: final(lctx).thread_id(),
                lock_id: ret.1.view().lock_id(),
            }),
            // ---- the LockPerm ----
            ret.1.view().state() is WriteLock,
            ret.1.view().thread_id() == final(lctx).thread_id(),
            // ---- lctx: the thread lock id registered under obj_id ----
            lock_ensures(old(lctx), final(lctx), thread_value, LockId{
                container: LockOwnerId::NotApp,
                process: LockOwnerId::NotApp,
                major: thread_value.current_lock_major(),
                minor: page_ptr,
            }, obj_id.view()),
    {
        unimplemented!()
    }
}
