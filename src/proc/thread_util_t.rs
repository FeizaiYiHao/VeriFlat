use vstd::prelude::*;
verus! {

use crate::*;
use vstd::simple_pptr::*;

    /// TCB: reinterpret a raw 4k page's memory as a fresh `RwLock<Thread>`.
    ///
    /// The narrow retype converter — mirrors `page_perm_to_page_map`
    /// (`pagetable_seq/pagemap_util_t.rs`) and atmosphere's `page_to_thread`:
    /// it consumes the page's byte-array permission (`PagePerm4k`) and hands
    /// back a typed `PointsTo<ThreadRwLock>` at the SAME address, holding
    /// `thread_value`, initialized and UNLOCKED. No lock is taken and `lctx` is
    /// untouched here — this primitive only reinterprets memory. The write-lock
    /// registration (mint the `LockPerm`, register in `lctx`, flip
    /// `locking_thread` to `Write`) and the `thread_map` domain growth are done
    /// by `LockedMap::insert` when it accepts this perm; the page-state flip
    /// (`Owned4k -> Allocated4k{AsThread}`) and the process unstage / quota
    /// decrement stay in verified code. Keeping this converter pure (one
    /// `unsafe` reinterpret, no ghost lock machinery) is what makes it a small,
    /// defensible TCB axiom rather than a fat multi-subsystem mutation.
    #[verifier::external_body]
    pub fn retype_page_perm_to_thread(
        page_ptr: PagePtr,
        thread_value: Thread,
        Tracked(page_perm): Tracked<PagePerm4k>,
    ) -> (ret: Tracked<PointsTo<ThreadRwLock>>)
        requires
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            thread_value.inv(),
        ensures
            ret@.addr() == page_ptr,
            ret@.is_init(),
            ret@.value().is_init(),
            ret@.value().view() == thread_value,
            ret@.value().locking_thread() is None,
            ret@.value().being_killed() == false,
    {
        unimplemented!()
    }
}
