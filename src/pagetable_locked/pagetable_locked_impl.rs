
use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::define::*;
use crate::pagetable_seq::pagetable_spec::*;
use crate::primitive::*;
verus! {

pub type PageTablePerm = PointsTo<PageTable>;
pub struct PageTableLocked{
    pub perm: PageTablePerm,
}

impl RwLockTrait for PageTableLocked {
    uninterp spec fn rlocked(&self, thread_id:LockThreadId) -> bool; 
    uninterp spec fn wlocked(&self, thread_id:LockThreadId) -> bool; 
    open spec fn locked(&self, thread_id:LockThreadId) -> bool{
        self.rlocked(thread_id) || self.wlocked(thread_id)
    } 
}

impl PageTableLocked{
    pub open spec fn lock_id(&self) -> LockId{
        LockId{
            major: PAGE_TABLE_LOCK_MAJOR,
            minor: self.perm.value().cr3,
        }
    }

    pub open spec fn addr(&self) -> usize {
        self.perm.addr()
    }
    pub open spec fn is_init(&self) -> bool {
        self.perm.is_init()
    }
    pub open spec fn view(&self) -> PageTable
    {
        self.perm.value()
    }

    #[verifier::external_body]
    pub fn read_lock(&mut self, Tracked(lm): Tracked<&mut LockManager>) -> (ret:Tracked<LockPerm>)
        requires
            old(self).locked(old(lm).thread_id()) == false,
            old(lm).lock_seq().len() == 0 ||
                old(self).lock_id().greater(&old(lm).lock_seq().last()),
        ensures
            self.rlocked(lm.thread_id()),
            self.wlocked(lm.thread_id()) == false,
            self.lock_id() == old(self).lock_id(),
            self.addr() == old(self).addr(),
            self.is_init() == old(self).is_init(),
            self.view() == old(self).view(),
            lm.thread_id() == old(lm).thread_id(),
            lm.lock_seq() == old(lm).lock_seq().push(self.lock_id()),
            ret@.local_thread_id == lm.thread_id(),
            ret@.state == LockState::ReadLock,
            ret@.lock_id() == self.lock_id()
    {
        Tracked::assume_new()
    }

}


}