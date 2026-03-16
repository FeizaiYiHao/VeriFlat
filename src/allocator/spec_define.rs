use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;
verus! {

pub struct LinkedListNode<T>{
    pub value: RwLock<LinkedList<T>, false>,
    pub external_node: ExternalNode<usize>,
}


pub struct LinkedLinkedList<T:LockedUtil>{
    pub list: RwLock<LinkedList<usize>, false>,
    pub perms:  Tracked<Map<usize, PointsTo<RwLock<LinkedListNode<T>, false>>>>,
}

impl<T:LockedUtil,> LinkedLinkedList<T>{
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
                self.perms.view()[list_ptr].value().view().wlocked()
                |||
                self.perms.view()[list_ptr].value().value.inv()
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
            &&
            self.perms@[list_ptr].value().external_node.is_init() == false
        }
    }
}

}