use vstd::prelude::*;
use crate::{define::*};

verus! {

pub tracked enum LockState {
    Mutex,
    ReadLock,
    WriteLock,
}

pub tracked struct LockPerm {
    pub local_thread_id: LockThreadId,
    pub lock_major: LockMajorId,
    pub lock_minor: LockMinorId,
    pub state: LockState
}

impl LockPerm{
    pub open spec fn lock_id(&self) -> LockId{
        LockId{
            major:self.lock_major,
            minor:self.lock_minor,
        }
    }

    pub open spec fn thread_id(&self) -> LockThreadId{
        self.local_thread_id
    }
}
}