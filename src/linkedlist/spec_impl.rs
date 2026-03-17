use std::num::NonZero;

use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::lemma::seq_push_head_lemma;
use crate::lemma::seq_push_head_unique_lemma;
use crate::lemma::seq_push_lemma;
use crate::lemma::seq_push_unique_lemma;
use crate::lemma::seq_remove_lemma;
use crate::lemma::seq_remove_lemma_2;
use crate::lemma::seq_skip_index_of_lemma;
use crate::lemma::seq_skip_lemma;
use crate::LockMajorId;
use crate::LockOwnerId;
use crate::LockOwnerIdUtil;
use crate::LockedUtil;

use super::*;

verus! {
pub struct LinkedList<T, const MAJOR: LockMajorId>{
    pub perms: Tracked<Map<usize, PointsTo<Node<T>>>>,
    pub addr_list: Ghost<Seq<usize>>,
    pub value_list: Ghost<Seq<T>>,
    pub length: usize,
    pub head: Option<usize>,
    pub tail: Option<usize>,
    pub map: Ghost<Map<usize, T>>,

    pub container_depth: Option<usize>,
}

impl<T, const MAJOR: LockMajorId> LockOwnerIdUtil for LinkedList<T, MAJOR>{
    open spec fn container_depth(&self) -> LockOwnerId {
        if self.container_depth is Some{
            LockOwnerId::Some(self.container_depth.unwrap())
        }
        else{
            LockOwnerId::None
        }
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::None
    }
}

impl<T, const MAJOR: LockMajorId> LockedUtil for LinkedList<T, MAJOR>{
    open spec fn inv(&self) -> bool {
        self.wf()
    }

    open spec fn lock_major_1(&self) -> LockMajorId {
        MAJOR
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
//spec
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR>{
    pub open spec fn view(&self) -> Seq<T>{
        self.value_list@
    }

    pub open spec fn spec_index(&self, index:usize) -> T
        recommends
            index < self.length,
    {
        self.value_list@[index as int]
    } 

    pub open spec fn dom(&self) -> Set<usize>
    {
        self.perms@.dom()
    } 

    pub open spec fn map(&self) ->  Map<usize, T>{
        self.map@
    }

    pub open spec fn wf_perms(&self) -> bool{
        &&&
        forall|addr:usize|
            #![trigger self.perms@[addr].is_init()]
            #![trigger self.perms@[addr].addr()]
            #![trigger self.perms@.dom().contains(addr)]
            self.perms@.dom().contains(addr)
            ==>
            self.perms@[addr].is_init()
            &&
            self.perms@[addr].addr() == addr
        &&&
        forall|addr:usize|
            #![trigger self.perms@.dom().contains(addr)]
            #![trigger self.addr_list@.contains(addr)]
        self.perms@.dom().contains(addr) == self.addr_list@.contains(addr)
    }

    pub open spec fn wf_value_list(&self) -> bool {
        &&&
        self.value_list@.len() == self.length
        &&&
        forall|i:int|
            #![trigger self.value_list@[i]]
            #![trigger self.perms@[self.addr_list@[i]].value()@]
            0<=i<self.length
            ==>
            self.value_list@[i] == self.perms@[self.addr_list@[i]].value()@
    }

    pub open spec fn wf_addr_list(&self) -> bool{
        &&&
        self.addr_list@.len() == self.length
        &&&
        self.addr_list@.no_duplicates()
    }

    pub open spec fn wf_head(&self) -> bool{
        &&&
        self.length == 0 <==> self.head is None
        &&&
        self.head is Some 
        ==> 
        self.addr_list@[0] == self.head.unwrap()
        &&
        self.perms@[self.head.unwrap()].value().prev is None
    }

    pub open spec fn wf_tail(&self) -> bool{
        &&&
        self.length == 0 <==> self.tail is None
        &&&
        self.tail is Some 
            ==> 
            self.addr_list@[self.length - 1] == self.tail.unwrap()
            &&
            self.perms@[self.tail.unwrap()].value().next is None
    }

    pub open spec fn wf_prev(&self) -> bool{
        &&&
        forall|i:int|
            #![trigger self.perms@[self.addr_list@[i]].value().prev]
            1<=i<self.length
            ==>
            self.perms@[self.addr_list@[i]].value().prev is Some 
            && 
            self.perms@[self.addr_list@[i]].value().prev.unwrap() == self.addr_list@[i - 1]
        
    }
    pub open spec fn wf_next(&self) -> bool{
        &&&
        forall|i:int|
            #![trigger  self.perms@[self.addr_list@[i]].value().next]
            0<=i<self.length -1
            ==>
            self.perms@[self.addr_list@[i]].value().next is Some 
            && 
            self.perms@[self.addr_list@[i]].value().next.unwrap() == self.addr_list@[i + 1]
    }

    pub open spec fn wf_map(&self) -> bool{
        &&&
        self.map().dom() == self.perms@.dom()
        &&&
        forall|addr:usize|
            #![trigger self.map()[addr]]
            #![trigger self.perms@[addr]]
        self.map().dom().contains(addr) 
        ==>
        self.map()[addr] == self.perms@[addr].value()@
    }

    pub closed spec fn wf(&self) -> bool{
        &&&
        self.wf_perms()
        &&&
        self.wf_addr_list()
        &&&
        self.wf_value_list()
        &&&
        self.wf_head()
        &&&
        self.wf_tail()
        &&&
        self.wf_prev()
        &&&
        self.wf_next()
        &&&
        self.wf_map()
    }
}

// exec
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR>{
    pub fn new(container_depth: Option<usize>) -> (ret: Self)
        ensures
            ret.wf(),
    {
        Self { 
            perms: Tracked(Map::<usize, PointsTo<Node<T>>>::tracked_empty()),
            addr_list: Ghost(Seq::empty()), 
            value_list: Ghost(Seq::empty()), 
            length: 0, 
            head: None, 
            tail: None, 
            map: Ghost(Map::empty()),
            container_depth: container_depth,
        }
    }

    pub fn push_tail(&mut self, addr: usize, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).wf(),
            old(self).length != usize::MAX,
            perm@.is_init(),
            perm@.addr() == addr,
        ensures
            self.wf(),
            self.length == old(self).length + 1,
            self@ == old(self)@.push(perm@.value()@),
            self.dom() == old(self).dom().insert(addr),
            self.container_depth == old(self).container_depth,
    {
        let mut perm = perm;
        if self.length == 0 {
            self.length = self.length + 1;
            self.addr_list = Ghost(self.addr_list@.push(addr));
            self.value_list = Ghost(self.value_list@.push(perm@.value()@));
            node_update_prev(addr, &mut perm, None);
            node_update_next(addr, &mut perm, None);
            self.tail = Some(addr);
            self.head = Some(addr);
            self.map = Ghost(self.map@.insert(addr, perm@.value()@));
            proof{
                self.perms.borrow_mut().tracked_insert(addr, perm.get());
            }
            
            proof{
                seq_push_lemma::<usize>();
            }
            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.wf());
        }else {
            proof{
                node_perm_disjoint(perm.borrow_mut(), self.perms.borrow_mut());
            }
            self.length = self.length + 1;
            self.addr_list = Ghost(self.addr_list@.push(addr));
            self.value_list = Ghost(self.value_list@.push(perm@.value()@));
            node_update_prev(addr, &mut perm, self.tail);
            node_update_next(addr, &mut perm, None);
            
            let old_tail_addr = self.tail.unwrap();
            let mut old_tail_perm = Tracked(self.perms.borrow_mut().tracked_remove(old_tail_addr));
            node_update_next::<T>(old_tail_addr, &mut old_tail_perm, Some(addr));
            proof{
                self.perms.borrow_mut().tracked_insert(old_tail_addr, old_tail_perm.get());
            }

            self.tail = Some(addr);
            self.map = Ghost(self.map@.insert(addr, perm@.value()@));
            proof{
                self.perms.borrow_mut().tracked_insert(addr, perm.get());
            }

            proof{
                seq_push_lemma::<usize>();
                seq_push_lemma::<T>();
                seq_push_unique_lemma::<usize>();
            }

            assert(self.wf_perms());
            assert(old(self).dom().contains(addr) == false);
            assert(old(self).addr_list@.contains(addr) == false);
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.addr_list@[self.length - 1] == self.tail.unwrap());
            assert(self.perms@[self.tail.unwrap()].value().next is None);
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.wf());
        }
    }

    pub fn push_head(&mut self, addr: usize, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).wf(),
            old(self).length != usize::MAX,
            perm@.is_init(),
            perm@.addr() == addr,
        ensures
            self.wf(),
            self.length == old(self).length + 1,
            self@ == old(self)@.insert(0,perm@.value()@),
            self.dom() == old(self).dom().insert(addr),
            self.map() == old(self).map().insert(addr, perm@.value()@),
            self.container_depth == old(self).container_depth,
    {
        let mut perm = perm;
        if self.length == 0 {
            self.length = self.length + 1;
            self.addr_list = Ghost(self.addr_list@.push(addr));
            self.value_list = Ghost(self.value_list@.push(perm@.value()@));
            node_update_prev(addr, &mut perm, None);
            node_update_next(addr, &mut perm, None);
            self.tail = Some(addr);
            self.head = Some(addr);
            self.map = Ghost(self.map@.insert(addr, perm@.value()@));
            proof{
                self.perms.borrow_mut().tracked_insert(addr, perm.get());
            }

            proof{
                seq_push_lemma::<usize>();
            }
            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.wf());
        }else {
            proof{
                node_perm_disjoint(perm.borrow_mut(), self.perms.borrow_mut());
            }
            self.length = self.length + 1;
            self.addr_list = Ghost(self.addr_list@.insert(0, addr));
            self.value_list = Ghost(self.value_list@.insert(0, perm@.value()@));
            node_update_prev(addr, &mut perm, None);
            node_update_next(addr, &mut perm, self.head);
            
            let old_head_addr = self.head.unwrap();
            let mut old_head_perm = Tracked(self.perms.borrow_mut().tracked_remove(old_head_addr));
            node_update_prev::<T>(old_head_addr, &mut old_head_perm, Some(addr));
            proof{
                self.perms.borrow_mut().tracked_insert(old_head_addr, old_head_perm.get());
            }

            self.head = Some(addr);
            self.map = Ghost(self.map@.insert(addr, perm@.value()@));
            proof{
                self.perms.borrow_mut().tracked_insert(addr, perm.get());
            }

            proof{
                seq_push_head_lemma::<usize>();
                seq_push_head_lemma::<T>();
                seq_push_head_unique_lemma::<usize>();
            }

            assert(self.wf_perms());
            assert(old(self).dom().contains(addr) == false);
            assert(old(self).addr_list@.contains(addr) == false);
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.addr_list@[self.length - 1] == self.tail.unwrap());
            assert(self.perms@[self.tail.unwrap()].value().next is None);
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.wf());
        }
    }

    pub fn pop_head(&mut self) -> (ret:(usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).wf(),
            old(self).length != 0,
        ensures
            self.wf(),
            self.dom() == old(self).dom().remove(ret.0),
            self@ == old(self)@.skip(1),
            self.length == old(self).length - 1,
            self.map() == old(self).map().remove(ret.0),

            ret.1@.is_init(),
            ret.1@.addr() == ret.0,
            ret.1@.value()@ == old(self)@[0],
            self.container_depth == old(self).container_depth,
    {
        if self.length != 1 {
            proof{
                seq_skip_lemma::<usize>();
                seq_skip_lemma::<T>();
                seq_skip_index_of_lemma::<usize>();
                seq_skip_index_of_lemma::<T>();
            }
            let old_head_addr = self.head.unwrap();
            let tracked old_head_perm = self.perms.borrow_mut().tracked_remove(old_head_addr);
            let old_head: &Node<T> = PPtr::<Node<T>>::from_usize(old_head_addr).borrow(Tracked(&old_head_perm));
            let new_head_addr = old_head.next.unwrap();
            self.head = Some(new_head_addr);
            self.length = self.length - 1;
            let mut new_head_perm = Tracked(self.perms.borrow_mut().tracked_remove(new_head_addr));
            node_update_prev::<T>(new_head_addr, &mut new_head_perm, None);
            proof{
                self.perms.borrow_mut().tracked_insert(new_head_addr, new_head_perm.get());
            }
            self.addr_list = Ghost(self.addr_list@.skip(1));
            self.value_list = Ghost(self.value_list@.skip(1));
            self.map = Ghost(self.map@.remove(old_head_addr));

            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.wf());

            (old_head_addr, Tracked(old_head_perm))
        }else{
            let old_head_addr = self.head.unwrap();
            let tracked old_head_perm = self.perms.borrow_mut().tracked_remove(old_head_addr);
            self.addr_list = Ghost(Seq::empty()); 
            self.value_list = Ghost(Seq::empty()); 
            self.length = 0; 
            self.head = None; 
            self.tail = None;
            self.map = Ghost(self.map@.remove(old_head_addr));

            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.wf());

            (old_head_addr, Tracked(old_head_perm))
        }
    }

    pub fn remove_helper(&mut self, addr:usize) -> (ret:(usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).wf(),
            old(self).dom().contains(addr),
            old(self).length != 0,
            old(self).head.unwrap() != addr,
            old(self).tail.unwrap() != addr,
        ensures
            ret.1@.is_init(),
            ret.1@.addr() == ret.0,
            ret.1@.value()@ == old(self).map()[addr],

            self.wf(),
            self.dom() == old(self).dom().remove(addr),
            self.map() == old(self).map().remove(addr),
            self.length == old(self).length - 1,
            old(self)@.no_duplicates() ==> self@ == old(self)@.remove_value(old(self).map()[addr]),
            self.container_depth == old(self).container_depth,
    {
            proof {
                seq_remove_lemma::<usize>();
                seq_remove_lemma::<T>();
                seq_remove_lemma_2::<usize>();
                seq_remove_lemma_2::<T>();
            }
            let ghost_index = Ghost(self.addr_list@.index_of(addr));

            let tracked old_perm = self.perms.borrow_mut().tracked_remove(addr);
            let old_node: &Node<T> = PPtr::<Node<T>>::from_usize(addr).borrow(Tracked(&old_perm));
            let prev = old_node.prev.unwrap();
            let next = old_node.next.unwrap();

            assert(self.addr_list@[ghost_index@ - 1] == prev);
            assert(self.addr_list@[ghost_index@ + 1] == next);

            let mut prev_perm = Tracked(self.perms.borrow_mut().tracked_remove(prev));
            let mut next_perm = Tracked(self.perms.borrow_mut().tracked_remove(next));
            node_update_next::<T>(prev, &mut prev_perm, Some(next));
            node_update_prev::<T>(next, &mut next_perm, Some(prev));

            proof{
                self.perms.borrow_mut().tracked_insert(prev, prev_perm.get());
                self.perms.borrow_mut().tracked_insert(next, next_perm.get());
            }
            self.addr_list = Ghost(self.addr_list@.subrange(0, ghost_index@).add(self.addr_list@.subrange(ghost_index@ + 1, self.length as int)));
            self.value_list = Ghost(self.value_list@.subrange(0, ghost_index@).add(self.value_list@.subrange(ghost_index@ + 1, self.length as int)));
            self.map = Ghost(self.map@.remove(addr));
            self.length = self.length - 1;

            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.addr_list@ == old(self).addr_list@.subrange(0, ghost_index@).add(old(self).addr_list@.subrange(ghost_index@ + 1, old(self).length as int)));
            assert(
                forall|i:int|
                    #![trigger self.addr_list@[i]]
                    ghost_index@ <= i < self.length
                    ==>
                    self.addr_list@[i] == old(self).addr_list@[i + 1] 
            );
            assert(self.wf_prev()) by {
                assert(        
                    forall|i:int|
                        #![trigger self.addr_list@[i]]
                        1<=i<ghost_index@ + 1
                        ==>
                        self.perms@[self.addr_list@[i]].value().prev == old(self).perms@[old(self).addr_list@[i]].value().prev
                    );
                assert(        
                    forall|i:int|
                        #![trigger self.addr_list@[i]]
                        1<=i<ghost_index@ + 1
                        ==>
                        self.perms@[self.addr_list@[i]].value().prev is Some 
                        &&
                        self.perms@[self.addr_list@[i]].value().prev.unwrap() == self.addr_list@[i - 1]
                    );
                assert(        
                    forall|i:int|
                        #![trigger self.addr_list@[i]]
                        ghost_index@ + 1 <=i< self.length
                        ==>
                        self.perms@[self.addr_list@[i]].value().prev == old(self).perms@[old(self).addr_list@[i + 1]].value().prev
                    );
                assert(        
                    forall|i:int|
                        #![trigger self.addr_list@[i]]
                        ghost_index@ + 1 <=i < self.length
                        ==>
                        self.perms@[self.addr_list@[i]].value().prev is Some 
                        &&
                        self.perms@[self.addr_list@[i]].value().prev.unwrap() == self.addr_list@[i - 1]
                    );
            };
            assert(self.wf_next()) by {
                assert(        
                    forall|i:int|
                        #![trigger self.addr_list@[i]]
                        0<=i<ghost_index@ - 1
                        ==>
                        self.perms@[self.addr_list@[i]].value().next == old(self).perms@[old(self).addr_list@[i]].value().next
                    );
                assert(        
                    forall|i:int|
                        #![trigger self.addr_list@[i]]
                        0<=i<ghost_index@ - 1
                        ==>
                        self.perms@[self.addr_list@[i]].value().next is Some 
                        &&
                        self.perms@[self.addr_list@[i]].value().next.unwrap() == self.addr_list@[i + 1]
                    );
                assert(        
                    forall|i:int|
                        #![trigger self.addr_list@[i]]
                        ghost_index@<=i< self.length - 1
                        ==>
                        self.perms@[self.addr_list@[i]].value().next == old(self).perms@[old(self).addr_list@[i + 1]].value().next
                    );
                assert(        
                    forall|i:int|
                        #![trigger self.addr_list@[i]]
                        ghost_index@ <=i< self.length - 1
                        ==>
                        self.perms@[self.addr_list@[i]].value().next is Some 
                        &&
                        self.perms@[self.addr_list@[i]].value().next.unwrap() == self.addr_list@[i + 1]
                    );
            };
            assert(self.map().dom() == self.perms@.dom());
            assert(
                forall|addr:usize|
                    #![trigger self.map()[addr]]
                    self.map().dom().contains(addr) 
                    ==>
                    self.map()[addr] == self.perms@[addr].value()@
            );
            assert(self.wf());

        (addr, Tracked(old_perm))
    }
    pub fn remove(&mut self, addr:usize) -> (ret:(usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).wf(),
            old(self).dom().contains(addr),

        ensures 
            ret.1@.is_init(),
            ret.1@.addr() == ret.0,
            ret.1@.value()@ == old(self).map()[addr],

            self.wf(),
            self.dom() == old(self).dom().remove(addr),
            self.map() == old(self).map().remove(addr),
            self.length == old(self).length - 1,
            old(self)@.no_duplicates() ==> self@ == old(self)@.remove_value(old(self).map()[addr]),
            self.container_depth == old(self).container_depth,
    {
        assert(self.length != 0);
        if self.length == 1 {
           proof{
                seq_skip_lemma::<usize>();
                seq_skip_lemma::<T>();
                seq_skip_index_of_lemma::<usize>();
                seq_skip_index_of_lemma::<T>();
            }
            return self.pop_head();
        }else if self.head.unwrap() == addr {
            proof{
                seq_skip_lemma::<usize>();
                seq_skip_lemma::<T>();
                seq_skip_index_of_lemma::<usize>();
                seq_skip_index_of_lemma::<T>();
            }
            let old_head_addr = addr;
            let tracked old_head_perm = self.perms.borrow_mut().tracked_remove(old_head_addr);
            let old_head: &Node<T> = PPtr::<Node<T>>::from_usize(old_head_addr).borrow(Tracked(&old_head_perm));
            let new_head_addr = old_head.next.unwrap();
            self.head = Some(new_head_addr);
            self.length = self.length - 1;
            let mut new_head_perm = Tracked(self.perms.borrow_mut().tracked_remove(new_head_addr));
            node_update_prev::<T>(new_head_addr, &mut new_head_perm, None);
            proof{
                self.perms.borrow_mut().tracked_insert(new_head_addr, new_head_perm.get());
            }
            self.addr_list = Ghost(self.addr_list@.skip(1));
            self.value_list = Ghost(self.value_list@.skip(1));
            self.map = Ghost(self.map@.remove(old_head_addr));

            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.wf());

            return (addr, Tracked(old_head_perm));
        }else if self.tail.unwrap() == addr{

            proof {
                seq_remove_lemma::<usize>();
                seq_remove_lemma::<T>();
            }

            let old_tail_addr = addr;
            let tracked old_tail_perm = self.perms.borrow_mut().tracked_remove(old_tail_addr);
            let old_tail: &Node<T> = PPtr::<Node<T>>::from_usize(old_tail_addr).borrow(Tracked(&old_tail_perm));
            let new_tail_addr = old_tail.prev.unwrap();
            self.tail = Some(new_tail_addr);
            let mut new_tail_perm = Tracked(self.perms.borrow_mut().tracked_remove(new_tail_addr));
            node_update_next::<T>(new_tail_addr, &mut new_tail_perm, None);
            proof{
                self.perms.borrow_mut().tracked_insert(new_tail_addr, new_tail_perm.get());
            }
            self.addr_list = Ghost(self.addr_list@.subrange(0,self.length as int - 1).add(self.addr_list@.subrange(self.length as int ,self.length as int)));
            self.value_list = Ghost(self.value_list@.subrange(0,self.length as int - 1).add(self.value_list@.subrange(self.length as int ,self.length as int)));
            self.map = Ghost(self.map@.remove(old_tail_addr));
            self.length = self.length - 1;

            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.wf());
            
            return (addr, Tracked(old_tail_perm));
        }else{
            return self.remove_helper(addr);
        }
    }
}
}