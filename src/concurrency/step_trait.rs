use vstd::prelude::*;
use crate::locks::*;

verus! {
    pub trait Step{
        spec fn step_spec(self, old:&Self, lock_manager: &LockManager) -> bool;
        proof fn step(&mut self, lock_manager: &LockManager)
            ensures
                self.step_spec(old(self), lock_manager),
        ;
    }
}