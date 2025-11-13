
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
    uninterp spec fn rlocked_by(&self, thread_id:LockThreadId) -> bool; 
    uninterp spec fn wlocked_by(&self, thread_id:LockThreadId) -> bool; 
    open spec fn locked(&self, thread_id:LockThreadId) -> bool{
        self.rlocked_by(thread_id) || self.wlocked_by(thread_id)
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
    pub fn read_lock(&mut self, Tracked(lock_manager): Tracked<&mut LockManager>) -> (ret:Tracked<LockPerm>)
        requires
            old(self).locked(old(lock_manager).thread_id()) == false,
            old(lock_manager).lock_seq().len() == 0 ||
                old(self).lock_id().greater(old(lock_manager).lock_seq().last()),
        ensures
            self.rlocked_by(lock_manager.thread_id()),
            self.wlocked_by(lock_manager.thread_id()) == false,
            self.lock_id() == old(self).lock_id(),
            self.addr() == old(self).addr(),
            self.is_init() == old(self).is_init(),
            self.view() == old(self).view(),
            lock_manager.thread_id() == old(lock_manager).thread_id(),
            lock_manager.lock_seq() == old(lock_manager).lock_seq().push(self.lock_id()),
            ret@.thread_id() == lock_manager.thread_id(),
            ret@.state == LockState::ReadLock,
            ret@.lock_id() == self.lock_id()
    {
        Tracked::assume_new()
    }

}


}