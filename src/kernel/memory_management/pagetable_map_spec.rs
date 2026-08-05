use vstd::prelude::*;
use crate::*;
use super::*;
verus! {
    #[verifier::opaque]
    pub open spec fn pagetable_perms_wf(pagetable_perms: PageTableLockedMap) -> bool{
        &&&
        pagetable_perms.perms_wf()
        &&&
        pagetables_inv(pagetable_perms)
    }
    pub open spec fn pagetables_inv(pagetable_perms: PageTableLockedMap) -> bool{
        &&&
        forall|pagetable_p:RwLockPageTableRoot|
            #![auto]
            pagetable_perms.dom().contains(pagetable_p)
            ==>
            pagetable_perms.spec_index(pagetable_p).inv()
    }

}