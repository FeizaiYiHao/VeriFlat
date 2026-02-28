use vstd::prelude::*;
use crate::locks::*;

verus! {
    pub trait Step{
        spec fn step_spec(self, old:&Self, lctx: &LocalContext) -> bool;
        proof fn step(&mut self, lctx: &LocalContext)
            ensures
                self.step_spec(old(self), lctx),
        ;
    }
}