use vstd::prelude::*;
use crate::define::*;
verus! {

pub trait LockInv {
    spec fn inv(&self) -> bool;
    spec fn lock_minor(&self) -> LockMinorId;
}
    
}