use vstd::prelude::*;
use crate::*;
use super::*;
verus! {
    pub open spec fn pagetable_perms_wf(pagetable_perms: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>) -> bool{
        &&&
        pagetable_perms.perms_wf()
        &&&
        pagetables_wlocked_or_inv(pagetable_perms)
    }
    pub open spec fn pagetables_wlocked_or_inv(pagetable_perms: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>) -> bool{
        &&&
        forall|pagetable_p:RwLockPageTableRoot|
            #![auto]
            pagetable_perms.dom().contains(pagetable_p)
            ==>
            pagetable_perms[pagetable_p].wlocked() || pagetable_perms[pagetable_p].inv()
    }

}