use vstd::prelude::*;
use crate::{define::*};

verus! {

pub tracked enum LockState {
    Mutex,
    ReadLock,
    WriteLock,
}

/// Opaque identity of an acquired lock instance. This authorizes access to an
/// `RwLock` but deliberately carries no deadlock-ordering information.
pub type LockToken = usize;

pub tracked struct LockPerm {
    local_thread_id: LockThreadId,
    lock_id: LockToken,
    state: LockState,
}

impl LockPerm{
    pub closed spec fn lock_id(&self) -> LockToken{
        self.lock_id
    }

    pub closed spec fn thread_id(&self) -> LockThreadId{
        self.local_thread_id
    }

    pub closed spec fn state(&self) -> LockState{
        self.state
    }
}
}
