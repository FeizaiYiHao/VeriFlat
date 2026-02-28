use vstd::prelude::*;

use super::*;

verus! {

    pub trait ToUsize{
        spec fn spec_to_usize(&self) -> usize;

        #[verifier(when_used_as_spec(spec_to_usize))]
        fn to_usize(&self) -> (ret:usize)
            ensures
                self.to_usize() == ret
        ;

    }

    impl ToUsize for RwLockPageTableRoot{
        closed spec fn spec_to_usize(&self) -> usize{
            self.v
        }
        fn to_usize(&self) -> (ret:usize)
            ensures
                ret == self.to_usize(),
        {
            self.v
        } 
        // pub fn from_usize(v:usize) -> (ret:Self)
        //     ensures
        //         ret.to_usize() == v,
        // {
        //     RwLockPageTableRoot{
        //         v: v,
        //     }
        // } 
    }

}