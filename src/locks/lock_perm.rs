use vstd::prelude::*;
use crate::{define::*};

verus! {

pub tracked enum LockState {
    Mutex,
    ReadLock,
    WriteLock,
}

/// Opaque identity of an acquired lock instance. This authorizes access to an
/// `RwLock`; `ordering_lock_id` records the structured id registered in the
/// held-lock ledger at acquisition time.
pub type LockToken = usize;

pub tracked struct LockPerm {
    local_thread_id: LockThreadId,
    lock_id: LockToken,
    ordering_lock_id: LockId,
    state: LockState,
}

impl LockPerm{
    pub closed spec fn lock_id(&self) -> LockToken{
        self.lock_id
    }

    pub closed spec fn ordering_lock_id(&self) -> LockId {
        self.ordering_lock_id
    }

    pub closed spec fn thread_id(&self) -> LockThreadId{
        self.local_thread_id
    }

    pub closed spec fn state(&self) -> LockState{
        self.state
    }
}
}
