use vstd::prelude::*;
verus! {
use crate::define::*;

pub proof fn lemma_u64_to_usize_roundtrip(x: u64)
    ensures
        x as usize as u64 == x,
{
}
} // verus!
