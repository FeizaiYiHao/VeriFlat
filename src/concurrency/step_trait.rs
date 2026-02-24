use vstd::prelude::*;
use crate::locks::*;

verus! {
    pub trait Step{
        spec fn step_spec(self, old:&Self, cctx: &ConcurrencyContext) -> bool;
        proof fn step(&mut self, cctx: &ConcurrencyContext)
            ensures
                self.step_spec(old(self), cctx),
        ;
    }
}