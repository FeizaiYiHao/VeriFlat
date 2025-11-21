use vstd::prelude::*;
use crate::{define::*};

verus! {

pub tracked enum LockState {
    Mutex,
    ReadLock,
    WriteLock,
}

pub tracked struct LockPerm {
    local_thread_id: LockThreadId,
    lock_major: LockMajorId,
    lock_minor: LockMinorId,
    state: LockState
}

impl LockPerm{
    pub closed spec fn lock_id(&self) -> LockId{
        LockId{
            major:self.lock_major,
            minor:self.lock_minor,
        }
    }

    pub closed spec fn thread_id(&self) -> LockThreadId{
        self.local_thread_id
    }

    pub closed spec fn state(&self) -> LockState{
        self.state
    }
}
}