use vstd::prelude::*;

use crate::{define::*, page_array::page::*, primitive::*, util::{page_index_util::page_index_wf, seq_util::no_change_except}};

verus! {

pub struct PageArray{
    pub phy_pages: Array<RwLockPage, NUM_PAGES>, 
}

impl PageArray{
    pub open spec fn pages_inv(&self) -> bool {
        &&&
        forall|p_i:PageIndex|
            #![auto]
            page_index_wf(p_i)
            ==>{
                |||
                self[p_i].wlocked()
                |||
                self[p_i].inv()
            }
    }

    pub open spec fn inv(&self) -> bool{
        &&&
        self.phy_pages.wf()
        &&&
        self.pages_inv()
    }

    pub open spec fn spec_index(&self, page_index: PageIndex) -> RwLockPage
        recommends 
            page_index_wf(page_index)
    {
        self.phy_pages@[page_index as int]
    }

    pub open spec fn view(&self) -> Seq<RwLockPage>{
        self.phy_pages@
    }

    pub fn page_add_mapping_4k(&mut self, page_index: PageIndex, Tracked(lock_perm): Tracked<&LockPerm>, pagetable_root:PageTableRoot, v_addr: VAddr)
        requires
            page_index_wf(page_index),
            old(self).inv(),
            old(self)[page_index].wlocked_by(lock_perm.thread_id()) == true,
            old(self)[page_index].inv(),

            lock_perm.state == LockState::WriteLock,
            lock_perm.lock_id().major == PHY_PAGE_LOCK_MAJOR,
            lock_perm.lock_id().minor == old(self)[page_index]@.addr,

            old(self)[page_index]@.state == PageState::Mapped4k,
            old(self)[page_index]@.ref_count != usize::MAX,
            old(self)[page_index]@.mappings_4k().contains((pagetable_root, v_addr)) == false
        ensures
            self.inv(),

            no_change_except(self@, old(self)@, page_index),

            self[page_index].wlocked_by(lock_perm.thread_id()) == true,
            self[page_index].inv(),
            self[page_index]@.state == old(self)[page_index]@.state,
            self[page_index]@.addr == old(self)[page_index]@.addr,
    {
        let mut page = self.phy_pages.take(page_index, Tracked(lock_perm));
        page.ref_count = page.ref_count + 1;
        page.mappings_4k = Ghost(page.mappings_4k@.insert((pagetable_root, v_addr)));
        self.phy_pages.put(page_index,Tracked(lock_perm), page);
    }

    pub fn lock_page(&mut self, page_index: PageIndex, Tracked(lock_manager): Tracked<&mut LockManager>) -> (ret: Tracked<LockPerm>)
        requires
            page_index_wf(page_index),
            old(self).inv(),

            old(self)[page_index].locked(old(lock_manager).thread_id()) == false,
                old(lock_manager).lock_seq().len() == 0 ||
                    old(self)[page_index].lock_id().greater(old(lock_manager).lock_seq().last()),
        ensures
            self.inv(),

            self[page_index].wlocked_by(lock_manager.thread_id()) == true,
            self[page_index].inv(),
    {
        self.phy_pages.wlock(page_index, Tracked(lock_manager))
    }

}

}