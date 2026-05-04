use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub open spec fn endpoint_perms_wf(&self) -> bool{
            &&&
            self.endpoint_map.perms_wf()
            &&&
            self.endpoints_inv()
        }
        pub open spec fn endpoints_inv(&self) -> bool{
        &&&
        forall|endpoint_p:RwLockEndpointPtr|
            #![auto]
            self.endpoint_map.dom().contains(endpoint_p)
            ==>
            self.endpoint_map[endpoint_p].inv()
    }
    }
}