use vstd::prelude::*;
use crate::locks::*;

verus! {
    pub trait Step{
        spec fn random_step_spec(self, old:&Self, lctx: &LocalContext) -> bool;
        proof fn random_step(&mut self, lctx: &LocalContext)
            ensures
                self.random_step_spec(old(self), lctx),
        ;
    }
}