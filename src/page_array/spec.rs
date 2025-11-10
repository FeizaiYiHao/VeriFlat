use vstd::prelude::*;

use crate::{define::*, page_array::page::*, primitive::*, util::page_index_util::page_index_wf};

verus! {

pub struct PageArray{
    pub phy_pages: Array<Page, NUM_PAGES>, 
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

    pub open spec fn view(&self) -> Seq<Page>{
        self.phy_pages@
    }

    #[verifier(external_body)]
    pub fn wlock_page(&mut self, page_index: PageIndex, Tracked(lm): Tracked<&mut LockManager>) -> (ret: Tracked<LockPerm>)
        requires
            page_index_wf(page_index),
            old(self).inv(),
            old(self)@[page_index as int].locked(old(lm).thread_id()) == false,
            old(lm).lock_seq().len() == 0 ||
                old(self)@[page_index as int].lock_id().greater(&old(lm).lock_seq().last()),
        ensures
            forall|p_i:usize| #![auto] page_index_wf(p_i) && p_i != page_index ==> self@[p_i as int] == old(self)@[p_i as int],
            self@[page_index as int].rlocked(lm.thread_id()) == false,
            self@[page_index as int].wlocked(lm.thread_id()),
            self@[page_index as int].lock_id() == old(self)@[page_index as int].lock_id(),
            self@[page_index as int].view() == old(self)@[page_index as int].view(),
            lm.thread_id() == old(lm).thread_id(),
            lm.lock_seq() == old(lm).lock_seq().push(self@[page_index as int].lock_id()),
            ret@.local_thread_id == lm.thread_id(),
            ret@.state == LockState::WriteLock,
            ret@.lock_id() == self@[page_index as int].lock_id()
    {
        self.phy_pages.ar[page_index].wlock(Tracked(&mut lm))
    }

    #[verifier(external_body)]
    pub fn wunlock_page(&mut self, page_index: PageIndex, Tracked(lm): Tracked<&mut LockManager>, lp: Tracked<LockPerm>)
        requires
            page_index_wf(page_index),
            old(self).inv(),
            old(self)@[page_index as int].wlocked(old(lm).thread_id()),
            lp@.local_thread_id == old(lm).thread_id(),
            lp@.state == LockState::WriteLock,
            lp@.lock_id() == old(self)@[page_index as int].lock_id(),
        ensures
            forall|p_i:usize| #![auto] page_index_wf(p_i) && p_i != page_index ==> self@[p_i as int] == old(self)@[p_i as int],
            self@[page_index as int].rlocked(lm.thread_id()) == false,
            self@[page_index as int].wlocked(lm.thread_id()) == false,
            self@[page_index as int].lock_id() == old(self)@[page_index as int].lock_id(),
            self@[page_index as int].view() == old(self)@[page_index as int].view(),
            lm.thread_id() == old(lm).thread_id(),
            lm.lock_seq() == old(lm).lock_seq().remove_value(self@[page_index as int].lock_id()),
    {
        self.phy_pages.ar[page_index].wunlock(Tracked(&mut lm), lp)
    }
}

}