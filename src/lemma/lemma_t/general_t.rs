use vstd::prelude::*;
verus! {

use crate::define::*;

pub proof fn lemma_usize_u64(x: u64)
    ensures
        x as usize as u64 == x,
{
    assert(x as usize as u64 == x) by (bit_vector);
}

} // verus!
