use vstd::prelude::*;
use crate::*;
use super::*;
verus! {
    #[verifier::opaque]
    pub open spec fn pagetable_perms_wf(pagetable_perms: PageTableLockedMap) -> bool {
        &&& pagetable_perms.perms_wf()
        &&& pagetables_inv(pagetable_perms)
        &&& pagetable_hidden_leaves_only_when_wlocked(pagetable_perms)
    }

    /// A pagetable with a leaf the user cannot see is write-locked: unmap clears present bits and reclaims
    /// those leaves before it releases the table.
    #[verifier::opaque]
    pub open spec fn pagetable_hidden_leaves_only_when_wlocked(pagetable_perms: PageTableLockedMap) -> bool {
        forall|pagetable_p: RwLockPageTableRoot|
            #![trigger pagetable_perms.spec_index(pagetable_p).locking_thread()]
            pagetable_perms.dom().contains(pagetable_p) && !pagetable_perms.spec_index(pagetable_p).view().leaves_present()
            ==> pagetable_perms.spec_index(pagetable_p).locking_thread() is Write
    }

    pub proof fn pagetable_perms_wf_map(pagetable_perms: PageTableLockedMap) requires pagetable_perms_wf(pagetable_perms) ensures pagetable_perms.perms_wf() { reveal(pagetable_perms_wf); }
    pub open spec fn pagetables_inv(pagetable_perms: PageTableLockedMap) -> bool{
        &&&
        forall|pagetable_p:RwLockPageTableRoot|
            #![auto]
            pagetable_perms.dom().contains(pagetable_p)
            ==>
            pagetable_perms.spec_index(pagetable_p).inv()
    }

    pub proof fn pagetable_perms_wf_at(
        pagetable_perms: PageTableLockedMap,
        pagetable_ptr: RwLockPageTableRoot,
    )
        requires
            pagetable_perms_wf(pagetable_perms),
            pagetable_perms.dom().contains(pagetable_ptr),
        ensures
            pagetable_perms.perms_wf(),
            pagetable_perms.view().spec_index(pagetable_ptr).is_init(),
            pagetable_perms.view().spec_index(pagetable_ptr).addr()
                == pagetable_ptr,
            pagetable_perms.spec_index(pagetable_ptr).inv(),
            pagetable_perms.spec_index(pagetable_ptr).is_init(),
            pagetable_perms.spec_index(pagetable_ptr).view().inv(),
    {
        reveal(pagetable_perms_wf);
    }
}
