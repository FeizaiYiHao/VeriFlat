use vstd::prelude::*;

use crate::{define::*, page_array::page::*, primitive::*, util::page_index_util::page_index_wf};

verus! {

pub struct PageArray{
    pub phy_pages: Array<RwLockPage, NUM_PAGES>, 
}

impl PageArray{
    pub open spec fn phy_page_minor_inv(&self) -> bool{
        &&&
        forall|p_i:usize| #![auto]  page_index_wf(p_i) ==> self@[p_i as int].lock_minor() == p_i
    }

    pub open spec fn inv(&self) -> bool{
        &&&
        self.phy_pages.wf()
        &&&
        self.phy_page_minor_inv()
    }

    pub open spec fn view(&self) -> Seq<RwLockPage>{
        self.phy_pages@
    }

    #[verifier(external_body)]
    pub fn wlock_page(&mut self, page_index: PageIndex, Tracked(lock_manager): Tracked<&mut LockManager>) -> (ret: Tracked<LockPerm>)
        requires
            page_index_wf(page_index),
            old(self).inv(),
            old(self)@[page_index as int].locked(old(lock_manager).thread_id()) == false,
            old(lock_manager).lock_seq().len() == 0 ||
                old(self)@[page_index as int].lock_id().greater(old(lock_manager).lock_seq().last()),
        ensures
            forall|p_i:usize| #![auto] page_index_wf(p_i) && p_i != page_index ==> self@[p_i as int] == old(self)@[p_i as int],
            self@[page_index as int].rlocked(lock_manager.thread_id()) == false,
            self@[page_index as int].wlocked(lock_manager.thread_id()),
            self@[page_index as int].lock_id() == old(self)@[page_index as int].lock_id(),
            self@[page_index as int].view() == old(self)@[page_index as int].view(),
            lock_manager.thread_id() == old(lock_manager).thread_id(),
            lock_manager.lock_seq() == old(lock_manager).lock_seq().push(self@[page_index as int].lock_id()),
            ret@.thread_id() == lock_manager.thread_id(),
            ret@.state == LockState::WriteLock,
            ret@.lock_id() == self@[page_index as int].lock_id()
    {
        self.phy_pages.ar[page_index].wlock(Tracked(&mut lock_manager))
    }

    #[verifier(external_body)]
    pub fn wunlock_page(&mut self, page_index: PageIndex, Tracked(lock_manager): Tracked<&mut LockManager>, lp: Tracked<LockPerm>)
        requires
            page_index_wf(page_index),
            old(self).inv(),
            old(self)@[page_index as int].wlocked(old(lock_manager).thread_id()),
            lp@.thread_id() == old(lock_manager).thread_id(),
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self)@[page_index as int].lock_id(),
        ensures
            forall|p_i:usize| #![auto] page_index_wf(p_i) && p_i != page_index ==> self@[p_i as int] == old(self)@[p_i as int],
            self@[page_index as int].rlocked(lock_manager.thread_id()) == false,
            self@[page_index as int].wlocked(lock_manager.thread_id()) == false,
            self@[page_index as int].lock_id() == old(self)@[page_index as int].lock_id(),
            self@[page_index as int].view() == old(self)@[page_index as int].view(),
            lock_manager.thread_id() == old(lock_manager).thread_id(),
            lock_manager.lock_seq() == old(lock_manager).lock_seq().remove_value(self@[page_index as int].lock_id()),
    {
        self.phy_pages.ar[page_index].wunlock(Tracked(&mut lock_manager), lp)
    }

    #[verifier(external_body)]
    pub fn take_page(&mut self, page_index: PageIndex, Tracked(lock_manager): Tracked<&LockManager>, lp: Tracked<&LockPerm>) -> (ret: Page)
        requires
            page_index_wf(page_index),
            old(self).inv(),
            old(self)@[page_index as int].wlocked(lock_manager.thread_id()),
            old(self)@[page_index as int].is_init(),
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self)@[page_index as int].lock_id(),
        ensures
            forall|p_i:usize| #![auto] page_index_wf(p_i) && p_i != page_index ==> self@[p_i as int] == old(self)@[p_i as int],

            self@[page_index as int].rlocked(lock_manager.thread_id()) == old(self)@[page_index as int].rlocked(lock_manager.thread_id()),
            self@[page_index as int].wlocked(lock_manager.thread_id()) == old(self)@[page_index as int].wlocked(lock_manager.thread_id()),
            self@[page_index as int].lock_id() == old(self)@[page_index as int].lock_id(),
            self@[page_index as int].is_init() == false,
            ret == old(self)@[page_index as int].view(),
    {
        self.phy_pages.ar[page_index].take(lp)
    }

        #[verifier(external_body)]
    pub fn put_page(&mut self, page_index: PageIndex, Tracked(lock_manager): Tracked<&LockManager>, lp: Tracked<&LockPerm>, v: Page)
        requires
            page_index_wf(page_index),
            old(self).inv(),
            old(self)@[page_index as int].wlocked(lock_manager.thread_id()),
            old(self)@[page_index as int].is_init() == false,
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self)@[page_index as int].lock_id(),
        ensures
            forall|p_i:usize| #![auto] page_index_wf(p_i) && p_i != page_index ==> self@[p_i as int] == old(self)@[p_i as int],

            self@[page_index as int].rlocked(lock_manager.thread_id()) == old(self)@[page_index as int].rlocked(lock_manager.thread_id()),
            self@[page_index as int].wlocked(lock_manager.thread_id()) == old(self)@[page_index as int].wlocked(lock_manager.thread_id()),
            self@[page_index as int].lock_id() == old(self)@[page_index as int].lock_id(),
            self@[page_index as int].view() == v,
            self@[page_index as int].is_init(),
    {
        self.phy_pages.ar[page_index].set(lp, v)
    }

}

}