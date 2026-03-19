use vstd::prelude::*;

use crate::{define::*, page_array::page::*, primitive::*, util::*};
use crate::locks::*;

verus! {

pub struct PageArray{
    pub phy_pages: LockedArray<Page, PAGE_HAS_KILL_STATE, NUM_PAGES>, 
}

impl PageArray{
    pub open spec fn pages_inv(&self) -> bool {
        &&&
        forall|p_i:PageIndex|
            #![auto]
            page_index_wf(p_i)
            ==>{
                |||
                self[p_i]@.wlocked()
                |||
                self[p_i]@.inv()
            }
    }

    pub open spec fn inv(&self) -> bool{
        &&&
        self.phy_pages.inv()
        &&&
        self.pages_inv()
    }

    pub open spec fn spec_index(&self, page_index: PageIndex) -> LockedArrayElement<Page, PAGE_HAS_KILL_STATE>
        recommends 
            page_index_wf(page_index)
    {
        self.phy_pages[page_index]
    }

    pub open spec fn view(&self) -> Seq<RwLock<Page, PAGE_HAS_KILL_STATE>>{
        self.phy_pages@
    }
    pub open spec fn unchanged_except(&self, old: &Self, index:usize) -> bool{
        &&&
        forall|i:usize|
            #![auto]
            0 <= i < NUM_PAGES && i != index
            ==>
            self[i] == old[i]
    }
    pub fn page_add_mapping_4k(&mut self, page_index: PageIndex, Tracked(lctx): Tracked<&LocalContext>, Tracked(lock_perm): Tracked<&LockPerm>, pagetable_root:RwLockPageTableRoot, v_addr: VAddr)
        requires
            page_index_wf(page_index),

            old(self).inv(),
            old(self)[page_index]@.wlocked_by(lctx),
            old(self)[page_index]@.is_init(),

            lock_perm.state() is WriteLock,
            lock_perm.thread_id() == lctx.thread_id(),
            lock_perm.lock_id() == old(self)[page_index]@.locking_thread() -> Write_lock_id,

            old(self)[page_index]@@.ref_count != usize::MAX,
            old(self)[page_index]@@.state is Mapped4k,
            old(self)[page_index]@@.mappings_4k().contains((pagetable_root, v_addr)) == false,
        ensures
            self.inv(),

            self.unchanged_except(old(self), page_index),

            self[page_index]@.wlocked_by(lctx),
            self[page_index]@.is_init(),
            self[page_index]@@.state == old(self)[page_index]@@.state,
            old(self)[page_index]@@.inv() ==> self[page_index]@@.inv() 
    {
        let mut page = self.phy_pages.take(page_index, Tracked(lctx), Tracked(lock_perm));
        page.ref_count = page.ref_count + 1;
        page.mappings_4k = Ghost(page.mappings_4k@.insert((pagetable_root, v_addr)));
        self.phy_pages.put(page_index, Tracked(lctx),Tracked(lock_perm), page);
    }

    pub fn wlock_page(&mut self, page_index: PageIndex, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
        requires
            page_index_wf(page_index),
            old(self).inv(),

            old(self)[page_index].container_depth() == lock_id@.container,
            old(self)[page_index].process_depth() == lock_id@.process,
            old(self)[page_index].lock_major_sat(lock_id@.major),
            old(self)[page_index].lock_minor() == lock_id@.minor,

            wlock_requires(old(self)[page_index]@, old(lctx)),
            old(lctx).lock_id_acyclic(lock_id@),
        ensures
            self.inv(),
            self.unchanged_except(old(self), page_index),

            wlock_ensures(old(self)[page_index]@, self[page_index]@, lock_id@, lctx.thread_id(), ret@),
            lock_ensures(old(lctx), lctx, lock_id@),
    {
        self.phy_pages.wlock(page_index, Tracked(lctx), lock_id)
    }

    pub fn wunlock_page(&mut self, page_index: PageIndex, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>)
        requires
            page_index_wf(page_index),
            old(self).inv(),

            old(self)[page_index]@.wlocked_by(old(lctx)),
            old(self)[page_index]@.being_killed() == false,
            old(self)[page_index].inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[page_index]@.locking_thread() -> Write_lock_id,
        ensures
            self.inv(),
            self.unchanged_except(old(self), page_index),

            wunlock_ensures(old(self)[page_index]@, self[page_index]@),
            unlock_ensures(old(lctx), lctx, lock_perm@.lock_id()),
    {
        self.phy_pages.wunlock(page_index, Tracked(lctx), lock_perm);
    }

    pub fn take(&mut self, page_index:PageIndex, Tracked(lctx): Tracked<&LocalContext>, lock_perm:Tracked<&LockPerm>) -> (ret:Page)
            requires
                old(self).inv(),
                page_index_wf(page_index),

                old(self)[page_index]@.wlocked_by(lctx),
                old(self)[page_index]@.being_killed() == false,
                old(self)[page_index].inv(),

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == lctx.thread_id(),
                lock_perm@.lock_id() == old(self)[page_index]@.locking_thread() -> Write_lock_id,
            ensures
                self.inv(),
                self.unchanged_except(old(self), page_index),

                take_ensures(old(self)[page_index]@, self[page_index]@),
                
                ret == old(self)[page_index]@@,
        {
            assert(self.phy_pages[page_index]@.is_init());
            self.phy_pages.take(page_index, Tracked(lctx), lock_perm)
        } 

        pub fn put(&mut self, page_index:PageIndex, Tracked(lctx): Tracked<&LocalContext>, lock_perm:Tracked<&LockPerm>, v:Page)
            requires
                old(self).inv(),
                page_index_wf(page_index),

                old(self)[page_index]@.wlocked_by(lctx),
                old(self)[page_index]@.being_killed() == false,
                old(self)[page_index]@.is_init() == false,

                lock_perm@.state() is WriteLock,
                lock_perm@.thread_id() == lctx.thread_id(),
                lock_perm@.lock_id() == old(self)[page_index]@.locking_thread() -> Write_lock_id,
            ensures
                self.inv(),
                self.unchanged_except(old(self), page_index),

                put_ensures(old(self)[page_index]@, self[page_index]@, v),
        {
            self.phy_pages.put(page_index, Tracked(lctx), lock_perm, v);
        } 
}

}