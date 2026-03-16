use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;
verus! {

pub struct LinkedListNode<T, const MAJOR: LockMajorId>{
    pub value: LinkedList<T>,
    pub external_node: ExternalNode<usize>,
}

impl<T,const MAJOR: LockMajorId> LockedUtil for LinkedListNode<T, MAJOR>{
    open spec fn inv(&self) -> bool {
        self.value.wf()
    }

    open spec fn lock_major_1(&self) -> crate::LockMajorId {
        MAJOR
    }

    open spec fn lock_major_2(&self) -> crate::LockMajorId {
        233
    }

    open spec fn lock_major_3(&self) -> crate::LockMajorId {
        233
    }

    open spec fn lock_major_default(&self) -> crate::LockMajorId {
        233
    }

    open spec fn lock_major_1_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_2_predicate(&self) -> bool {
        false
    }

    open spec fn lock_major_3_predicate(&self) -> bool {
        false
    }

    open spec fn lock_major_default_predicate(&self) -> bool {
        false
    }
}

pub struct LinkedLinkedList<T:LockedUtil, const MAJOR: LockMajorId>{
    pub list: RwLock<LinkedList<usize>, false>,
    pub perms:  Tracked<Map<usize, PointsTo<RwLock<LinkedListNode<T, MAJOR>, false>>>>,
}

impl<T:LockedUtil, const MAJOR: LockMajorId> LinkedLinkedList<T, MAJOR>{
    pub open spec fn list_dom_wf(&self) -> bool{
        &&&
        {
            |||
            self.list.wlocked()
            |||
            {
                &&&
                self.perms@.dom() == self.list.view().view().to_set()
                &&&
                forall|list_ptr:usize|
                #![auto]
                    self.list.view().view().contains(list_ptr)
                    ==>
                    self.perms@[list_ptr].is_init()
                    &&
                    self.perms@[list_ptr].addr() == list_ptr
            }
        }
    }
    pub open spec fn lists_wf(&self) -> bool{
        |||
        self.list.wlocked()
        |||
        {
            &&&
            forall|list_ptr:usize|
            #![auto]
            self.list.view().view().contains(list_ptr)
            ==>
            {
                |||
                self.perms.view()[list_ptr].value().wlocked()
                |||
                self.perms.view()[list_ptr].value().inv()
            }
        }
    }
    pub open spec fn nodes_wf(&self) -> bool{
        |||
        self.list.wlocked()
        |||
        {
            &&&
            forall|list_ptr:usize|
            #![auto]
            self.list.view().view().contains(list_ptr)
            ==>
            self.perms@[list_ptr].value().external_node.addr() == list_ptr
        }
    }
}

}