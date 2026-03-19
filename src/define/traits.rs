use vstd::prelude::*;

use super::*;

verus! {

    pub trait ToUsize: Sized{
        spec fn spec_to_usize(&self) -> usize;

        #[verifier(when_used_as_spec(spec_to_usize))]
        fn to_usize(&self) -> (ret:usize)
            ensures
                self.to_usize() == ret
        ;
        fn from_usize(v:usize) -> (ret:Self)
            ensures
                ret.to_usize() == v
        ;
    }

    impl ToUsize for RwLockPageTableRoot{
        closed spec fn spec_to_usize(&self) -> usize{
            self.v
        }
        fn to_usize(&self) -> (ret:usize)
        {
            self.v
        } 
        fn from_usize(v:usize) -> (ret:Self)
            ensures
                ret.to_usize() == v,
        {
            RwLockPageTableRoot{
                v: v,
            }
        } 
    }

    impl ToUsize for RwLockContainerPtr{
        closed spec fn spec_to_usize(&self) -> usize{
            self.v
        }
        fn to_usize(&self) -> (ret:usize)
        {
            self.v
        } 
        fn from_usize(v:usize) -> (ret:Self)
            ensures
                ret.to_usize() == v,
        {
            RwLockContainerPtr{
                v: v,
            }
        } 
    }

    impl ToUsize for RwLockProcessPtr{
        closed spec fn spec_to_usize(&self) -> usize{
            self.v
        }
        fn to_usize(&self) -> (ret:usize)
        {
            self.v
        } 
        fn from_usize(v:usize) -> (ret:Self)
        {
            RwLockProcessPtr{
                v: v,
            }
        } 
    }

    impl ToUsize for RwLockThreadPtr{
        closed spec fn spec_to_usize(&self) -> usize{
            self.v
        }
        fn to_usize(&self) -> (ret:usize)
        {
            self.v
        } 
        fn from_usize(v:usize) -> (ret:Self)
        {
            RwLockThreadPtr{
                v: v,
            }
        } 
    }

    impl ToUsize for RwLockEndpointPtr{
        closed spec fn spec_to_usize(&self) -> usize{
            self.v
        }
        fn to_usize(&self) -> (ret:usize)
        {
            self.v
        } 
        fn from_usize(v:usize) -> (ret:Self)
        {
            RwLockEndpointPtr{
                v: v,
            }
        } 
    }

    impl ToUsize for RwLockPageAllocatorPtr{
        closed spec fn spec_to_usize(&self) -> usize{
            self.v
        }
        fn to_usize(&self) -> (ret:usize)
        {
            self.v
        } 
        fn from_usize(v:usize) -> (ret:Self)
        {
            RwLockPageAllocatorPtr{
                v: v,
            }
        } 
    }
}