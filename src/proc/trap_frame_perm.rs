use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
/// Permission to a thread's saved `Registers`, sealed: verified code moves it but cannot read or write the frame.
pub tracked struct TrapFramePerm {
    tracked perm: PointsTo<Registers>,
}

impl TrapFramePerm {
    pub closed spec fn addr(&self) -> usize { self.perm.addr() }

    pub closed spec fn value(&self) -> Registers { self.perm.value() }

    pub proof fn new(tracked perm: PointsTo<Registers>) -> (tracked ret: Self)
        requires
            perm.is_init(),
        ensures
            ret.addr() == perm.addr(),
            ret.value() == perm.value(),
    {
        TrapFramePerm { perm }
    }
}
} // verus!
