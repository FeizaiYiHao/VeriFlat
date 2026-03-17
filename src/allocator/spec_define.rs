use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;
verus! {

pub struct LinkedListNode<T, const MAJOR: LockMajorId>{
    pub value: RwLock<LinkedList<T, MAJOR>, false>,
    pub external_node: ExternalNode<usize>,
}

pub struct AllocatorQuota{
    pub value: usize,
    pub minor: Ghost<LockMinorId>,
    pub container_depth: usize,
}

impl LockedUtil for AllocatorQuota {
    open spec fn inv(&self) -> bool {
        true
    }

    open spec fn lock_major_1(&self) -> LockMajorId {
        QUOTA_MAJOR
    }

    open spec fn lock_major_2(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_3(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_default(&self) -> LockMajorId {
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

impl LockMinor for AllocatorQuota {
    open spec fn lock_minor(&self) -> LockMinorId{
        self.minor@
    }
}

impl LockOwnerIdUtil for AllocatorQuota{
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.container_depth)
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::None
    }
}

impl AllocatorQuota{
    #[verifier(external_body)]
    pub fn exec_lock_minor(&self) -> (ret:LockMinorId)
        ensures
            ret == self.lock_minor(),
    {
        self as *const AllocatorQuota as LockMinorId
    }
}

pub tracked struct PageAllocatorTicket{
    pub id: int,
    pub remaining_value: usize, 
}

pub struct PageAllocatorSet<T>{
    pub list: RwLock<LinkedList<usize, PAGE_ALLOCATOR_LIST_MAJOR>, false>,
    pub quota: RwLock<AllocatorQuota, false>,
    pub allocator_perms:  Tracked<Map<usize, PointsTo<LinkedListNode<T, PAGE_ALLOCATOR_MAJOR>>>>,

    pub sent_tickets: Ghost<Map<int, usize>>,
}


impl<T> PageAllocatorSet<T>{
    pub open spec fn list_dom_wf(&self) -> bool{
        &&&
        {
            |||
            self.list.wlocked()
            |||
            {
                &&&
                self.alloactor_perms@.dom() == self.list.view().view().to_set()
                &&&
                forall|list_ptr:usize|
                #![auto]
                    self.list.view().view().contains(list_ptr)
                    ==>
                    self.alloactor_perms@[list_ptr].is_init()
                    &&
                    self.alloactor_perms@[list_ptr].addr() == list_ptr
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
                self.alloactor_perms.view()[list_ptr].value().value.wlocked()
                |||
                self.alloactor_perms.view()[list_ptr].value().value.inv()
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
            self.alloactor_perms@[list_ptr].value().external_node.addr() == list_ptr
            &&
            self.alloactor_perms@[list_ptr].value().external_node.is_init() == false
        }
    }

    pub open spec fn inv(&self) ->bool {
        &&&
        self.list_dom_wf()
        &&&
        self.lists_wf()
        &&&
        self.nodes_wf()
    }

    pub fn rlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).inv(),
            
            old(self)@[key].lock_major_sat(lock_id@.major),
            old(self)@[key].lock_minor() == lock_id@.minor,

            wlock_requires(old(self)[key], old(lctx)),
            old(lctx).lock_id_valid(lock_id@)
    {

    }
}

}