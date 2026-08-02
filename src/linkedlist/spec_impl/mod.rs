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
use crate::*;

use super::*;

verus! {

#[verifier::reject_recursive_types(T)]
pub struct LinkedList<T, const MAJOR: LockMajorId>{
    pub perms: Tracked<Map<usize, PointsTo<Node<T>>>>,
    pub addr_list: Ghost<Seq<usize>>,
    pub value_list: Ghost<Seq<T>>,
    pub length: usize,
    pub head: Option<usize>,
    pub tail: Option<usize>,
    pub map: Ghost<Map<usize, T>>,
    pub reverse_map: Ghost<Map<T, usize>>,

    pub container_depth: Option<usize>,

    pub minor: Option<usize>,
}


impl<T, const MAJOR: LockMajorId> LockOwnerIdTrait for LinkedList<T, MAJOR>{
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}
impl<T, const MAJOR: LockMajorId> LockInvTrait for LinkedList<T, MAJOR>{
    open spec fn inv(&self) -> bool {
        self.wf()
    }
}

impl<T, const MAJOR: LockMajorId> LockMajorTrait for LinkedList<T, MAJOR>{
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

impl<T, const MAJOR: LockMajorId> LockMinorTrait for LinkedList<T, MAJOR>{
    open spec fn lock_minor(&self) -> LockMinorId {
        if self.minor is Some{
            self.minor.unwrap()
        }else{
            233
        }
    }
}

impl <T, const MAJOR: LockMajorId> LockUserVisibilityTrait for LinkedList<T, MAJOR>{
    open spec fn is_user_visible() -> bool {
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

    pub open spec fn revese_map(&self) ->  Map<T, usize>{
        self.reverse_map.view()
    }

    pub open spec fn spec_len(&self) -> usize{
        self.view().len() as usize
    }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret:usize)
        requires
            self.wf()
        ensures
            ret == self.len()
    {
        proof{
            reveal(LinkedList::wf_value_list);
        }
        self.length
    }

    /// Expose the (otherwise closed-`wf`) fact that the stored `length` equals
    /// the view length. Additive helper — mirrors `LockedArray::lemma_view_len`.
    pub proof fn lemma_len_view(&self)
        requires
            self.wf(),
        ensures
            self.view().len() == self.spec_len(),
    {
        reveal(LinkedList::wf_value_list);
    }

    /// Address ↔ value uniqueness: in a wf list whose VALUES have no
    /// duplicates, the address holding a given value is unique. Concretely,
    /// any two in-domain addresses mapping to the same value are equal.
    ///
    /// Proof idiom (per remove_helper): materialize each address's position in
    /// `addr_list`, push the value equality through `wf_value_list` so both
    /// positions hold the same `view()` element, then `no_duplicates` on the
    /// values forces the positions — hence the addresses — equal.
    pub proof fn lemma_value_addr_unique(&self, a: usize, b: usize)
        requires
            self.wf(),
            self.view().no_duplicates(),
            self.map().dom().contains(a),
            self.map().dom().contains(b),
            self.map()[a] == self.map()[b],
        ensures
            a == b,
    {
        reveal(LinkedList::wf_perms);
        reveal(LinkedList::wf_addr_list);
        reveal(LinkedList::wf_value_list);
        reveal(LinkedList::wf_map);
        reveal(LinkedList::value_list_unique);
        // a, b are in addr_list (wf_perms: perms.dom == addr_list membership).
        assert(self.perms@.dom().contains(a));
        assert(self.perms@.dom().contains(b));
        assert(self.addr_list@.contains(a));
        assert(self.addr_list@.contains(b));
        let ia = self.addr_list@.index_of(a);
        let ib = self.addr_list@.index_of(b);
        // index_of lands in range and recovers the element.
        assert(0 <= ia < self.length) by {
            let k = choose|k: int| 0 <= k < self.addr_list@.len() && self.addr_list@[k] == a;
            assert(self.addr_list@[k] == a);
        }
        assert(0 <= ib < self.length) by {
            let k = choose|k: int| 0 <= k < self.addr_list@.len() && self.addr_list@[k] == b;
            assert(self.addr_list@[k] == b);
        }
        assert(self.addr_list@[ia] == a);
        assert(self.addr_list@[ib] == b);
        // wf_value_list: view()[i] == perms[addr_list[i]].value()@; wf_map:
        // map[addr] == perms[addr].value()@. So both positions hold the value.
        assert(self.view()[ia] == self.perms@[a].value()@);
        assert(self.view()[ib] == self.perms@[b].value()@);
        assert(self.map()[a] == self.perms@[a].value()@);
        assert(self.map()[b] == self.perms@[b].value()@);
        assert(self.view()[ia] == self.view()[ib]);
        // values have no duplicates ⟹ equal value at two positions ⟹ ia == ib.
        if ia != ib {
            assert(self.view()[ia] != self.view()[ib]);
        }
        assert(ia == ib);
        assert(a == self.addr_list@[ia]);
        assert(b == self.addr_list@[ib]);
    }

    #[verifier::opaque]
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

    #[verifier::opaque]
    pub open spec fn wf_value_list(&self) -> bool {
        &&&
        self.len() == self.length
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

    #[verifier::opaque]
    pub open spec fn value_list_unique(&self) -> bool {
        &&&
        forall|i:int, j:int|
            #![trigger self.value_list@[i], self.value_list@[j] ]
            0<=i<self.length && 0<=j<self.length && i != j
            ==>
            self.value_list@[i] != self.value_list@[j] 
    }

    #[verifier::opaque]
    pub open spec fn wf_addr_list(&self) -> bool{
        &&&
        self.addr_list@.len() == self.length
        &&&
        self.addr_list@.no_duplicates()
    }

    #[verifier::opaque]
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

    #[verifier::opaque]
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

    #[verifier::opaque]
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

    #[verifier::opaque]
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

    #[verifier::opaque]
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
        &&&
        forall|i:usize, j:usize|
            #![trigger self.map()[i], self.map()[j]]
            self.map().dom().contains(i) &&  self.map().dom().contains(j) && i != j
            ==>
            self.map()[i] != self.map()[j] 
    }

    #[verifier::opaque]
    pub open spec fn wf_reverse_map(&self) -> bool{
        // &&&
        // self.revese_map().dom() == self.map().values()
        // &&&
        // forall|i:T, j:T|
        //     #![trigger self.revese_map()[i], self.revese_map()[j]]
        //     self.revese_map().dom().contains(i) && self.revese_map().dom().contains(j) && i != j
        //     ==>
        //     self.revese_map()[i] != self.revese_map()[j] 
        &&&
        forall|addr:usize|
            #![trigger self.map().dom().contains(addr)]
            #![trigger self.map()[addr]]
            self.map().dom().contains(addr) 
            ==>
            self.revese_map().dom().contains(self.map()[addr]) 
            &&
            self.revese_map().spec_index(self.map()[addr]) == addr
        &&&
            forall|v:T|
                #![trigger self.revese_map().dom().contains(v)]
                #![trigger self.revese_map()[v]]
                #![trigger self.perms.dom().contains(self.revese_map()[v])]
            self.revese_map().dom().contains(v) 
            ==>
            // self.perms.dom().contains(self.revese_map()[v])
            // &&
            self.map().dom().contains(self.revese_map()[v]) 
            &&
            self.map().spec_index(self.revese_map()[v]) == v
    }

    pub open spec fn wf(&self) -> bool{
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
        &&&
        self.value_list_unique()
        &&&
        self.wf_reverse_map()
    }
}

// exec
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR>{
    pub fn new(container_depth: Option<usize>, minor: Option<usize>) -> (ret: Self)
        ensures
            ret.wf(),
    {
        proof{
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
            reveal(LinkedList::wf_head);
            reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_prev);
            reveal(LinkedList::wf_next);
            reveal(LinkedList::wf_map);
            reveal(LinkedList::value_list_unique);
            reveal(LinkedList::wf_reverse_map);
        }
        Self {
            perms: Tracked(Map::<usize, PointsTo<Node<T>>>::tracked_empty()),
            addr_list: Ghost(Seq::empty()),
            value_list: Ghost(Seq::empty()),
            length: 0,
            head: None,
            tail: None,
            map: Ghost(Map::empty()),
            reverse_map: Ghost(Map::empty()),
            container_depth: container_depth,
            minor:minor,
        }
    }

    pub fn push_tail(&mut self, addr: usize, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).wf(),
            old(self).length != usize::MAX,
            perm@.is_init(),
            perm@.addr() == addr,
            old(self).view().contains(perm@.value()@) == false,
        ensures
            final(self).wf(),
            final(self).length == old(self).length + 1,
            final(self)@ == old(self)@.push(perm@.value()@),
            final(self).dom() == old(self).dom().insert(addr),
            final(self).map() == old(self).map().insert(addr, perm@.value()@),
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
            old(self).dom().contains(addr) == false,
            old(self).map().dom().contains(addr) == false,
    {
        proof{
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
            reveal(LinkedList::wf_head);
            reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_prev);
            reveal(LinkedList::wf_next);
            reveal(LinkedList::wf_map);
            reveal(LinkedList::value_list_unique);
            reveal(LinkedList::wf_reverse_map);
        }
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
            self.reverse_map = Ghost(self.reverse_map@.insert(perm@.value()@, addr));
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
            assert(self.value_list_unique());
            assert(self.wf_reverse_map()) by {
                broadcast use vstd::map::group_map_lemmas;
                let v = perm@.value()@;
                if old(self).revese_map().dom().contains(v) {
                    assert(old(self).map().dom().contains(old(self).revese_map()[v]));
                }
            }
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
            self.reverse_map = Ghost(self.reverse_map@.insert(perm@.value()@, addr));
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
            assert(self.value_list_unique());
            assert(self.wf_reverse_map());
            assert(self.wf());
        }
    }

    pub fn push_head(&mut self, addr: usize, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).wf(),
            old(self).length != usize::MAX,
            perm@.is_init(),
            perm@.addr() == addr,
            old(self).view().contains(perm@.value()@) == false,
        ensures
            final(self).wf(),
            final(self).length == old(self).length + 1,
            final(self)@ == old(self)@.insert(0,perm@.value()@),
            final(self).dom() == old(self).dom().insert(addr),
            final(self).map() == old(self).map().insert(addr, perm@.value()@),
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
            old(self).dom().contains(addr) == false,
            old(self).map().dom().contains(addr) == false,
    {
        proof{
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
            reveal(LinkedList::wf_head);
            reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_prev);
            reveal(LinkedList::wf_next);
            reveal(LinkedList::wf_map);
            reveal(LinkedList::value_list_unique);
            reveal(LinkedList::wf_reverse_map);
        }
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
            self.reverse_map = Ghost(self.reverse_map@.insert(perm@.value()@, addr));
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
            assert(self.value_list_unique());
            assert(self.wf_reverse_map()) by {
                broadcast use vstd::map::group_map_lemmas;
                let v = perm@.value()@;
                if old(self).revese_map().dom().contains(v) {
                    assert(old(self).map().dom().contains(old(self).revese_map()[v]));
                }
            }
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
            self.reverse_map = Ghost(self.reverse_map@.insert(perm@.value()@, addr));
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
            assert(self.value_list_unique());
            assert(self.wf_reverse_map());
            assert(self.wf());
        }
    }

    /// Non-mutating read of the head node's address and stored value. Lets a
    /// caller learn the head's payload (and node address) WITHOUT popping, so it
    /// can act on that page (e.g. lock its slot) while the list still satisfies
    /// `wf()`. The returned value/address match what a subsequent `pop_head`
    /// would yield.
    pub fn peek_head(&self) -> (ret: (usize, T))
        where T: Copy
        requires
            self.wf(),
            self.len() != 0,
        ensures
            // address is the head, exposed only through the logical map.
            self.dom().contains(ret.0),
            self.map().dom().contains(ret.0),
            // value is the head element, == map[head].
            ret.1 == self@[0],
            ret.1 == self.map()[ret.0],
    {
        proof{
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
            reveal(LinkedList::wf_head);
            reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_prev);
            reveal(LinkedList::wf_next);
            reveal(LinkedList::wf_map);
            reveal(LinkedList::value_list_unique);
            reveal(LinkedList::wf_reverse_map);
        }
        let head_addr = self.head.unwrap();
        let tracked head_perm = self.perms.borrow().tracked_borrow(head_addr);
        let node: &Node<T> = PPtr::<Node<T>>::from_usize(head_addr).borrow(Tracked(head_perm));
        (head_addr, node.value)
    }

    pub fn pop_head(&mut self) -> (ret:(usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).wf(),
            old(self).len() != 0,
        ensures
            final(self).wf(),
            final(self).dom() == old(self).dom().remove(ret.0),
            final(self)@ == old(self)@.skip(1),
            final(self).length == old(self).length - 1,
            final(self).map() == old(self).map().remove(ret.0),

            ret.1@.is_init(),
            ret.1@.addr() == ret.0,
            ret.1@.value()@ == old(self)@[0],
            ret.1@.value()@ == old(self).map()[ret.0],
            // The popped node was the head — hence in the pre-pop domain. (Used
            // by callers that need map[ret.0] to be a live entry.)
            old(self).dom().contains(ret.0),
            old(self).map().dom().contains(ret.0),
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
    {
        proof{
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
            reveal(LinkedList::wf_head);
            reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_prev);
            reveal(LinkedList::wf_next);
            reveal(LinkedList::wf_map);
            reveal(LinkedList::value_list_unique);
            reveal(LinkedList::wf_reverse_map);
        }
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
            self.reverse_map = Ghost(self.reverse_map@.remove(self.map@[old_head_addr]));
            self.map = Ghost(self.map@.remove(old_head_addr));

            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.value_list_unique());
            assert(self.wf_reverse_map());
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
            self.reverse_map = Ghost(self.reverse_map@.remove(self.map@[old_head_addr]));
            self.map = Ghost(self.map@.remove(old_head_addr));

            assert(self.wf_perms());
            assert(self.wf_addr_list());
            assert(self.wf_value_list());
            assert(self.wf_head());
            assert(self.wf_tail());
            assert(self.wf_prev());
            assert(self.wf_next());
            assert(self.value_list_unique());
            assert(self.wf_reverse_map());
            assert(self.wf());

            (old_head_addr, Tracked(old_head_perm))
        }
    }

    pub fn pop_head_batch(&mut self, i: usize) -> (ret: LinkedList<T, MAJOR>)
        requires
            old(self).wf(),
            0 < i < old(self).length,
        ensures
            // ---- both halves are well-formed ----
            final(self).wf(),
            ret.wf(),
            // ---- views split at i ----
            final(self)@ == old(self)@.subrange(i as int, old(self).length as int),
            ret@ == old(self)@.subrange(0, i as int),
            final(self).length == old(self).length - i,
            ret.length == i,
            // ---- domains / maps split by the prefix address set ----
            final(self).map() == old(self).map().remove_keys(old(self).addr_list@.subrange(0, i as int).to_set()),
            ret.map() == old(self).map().restrict(old(self).addr_list@.subrange(0, i as int).to_set()),
            final(self).dom() == old(self).dom().difference(old(self).addr_list@.subrange(0, i as int).to_set()),
            ret.dom() == old(self).dom().intersect(old(self).addr_list@.subrange(0, i as int).to_set()),
            // ---- metadata framed ----
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
            ret.container_depth == old(self).container_depth,
            ret.lock_minor() == old(self).lock_minor(),
    {
        proof{
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
            reveal(LinkedList::wf_head);
            reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_prev);
            reveal(LinkedList::wf_next);
            reveal(LinkedList::wf_map);
            reveal(LinkedList::value_list_unique);
            reveal(LinkedList::wf_reverse_map);
        }
        proof {
            seq_subrange_split_lemma::<usize>();
            seq_subrange_split_lemma::<T>();
            seq_to_set_lemma::<usize>();
            seq_to_set_lemma::<T>();
        }

        let ghost prefix_set = old(self).addr_list@.subrange(0, i as int).to_set();
        let ghost prefix_value_set = old(self).value_list@.subrange(0, i as int).to_set();
        let head0 = self.head;

        // traverse to the prefix tail (index i-1); reads only
        let mut cur = self.head.unwrap();
        let mut k: usize = 0;
        while k < i - 1
            invariant
                self.wf(),
                self.addr_list@ == old(self).addr_list@,
                self.perms@ == old(self).perms@,
                self.length as int == old(self).length as int,
                (i as int) < old(self).length as int,
                0 <= k <= i - 1,
                cur == old(self).addr_list@[k as int],
            decreases i - 1 - k,
        {
            proof{
                reveal(LinkedList::wf_perms);
                reveal(LinkedList::wf_addr_list);
                reveal(LinkedList::wf_next);
            }
            let tracked node_perm = self.perms.borrow().tracked_borrow(cur);
            let node = PPtr::<Node<T>>::from_usize(cur).borrow(Tracked(node_perm));
            cur = node.next.unwrap();
            k = k + 1;
        }
        let prefix_tail_addr = cur;

        let tracked pt_perm_ref = self.perms.borrow().tracked_borrow(prefix_tail_addr);
        let pt_node = PPtr::<Node<T>>::from_usize(prefix_tail_addr).borrow(Tracked(pt_perm_ref));
        let cut_addr = pt_node.next.unwrap();

        // sever: the three O(1) writes
        let mut cut_perm = Tracked(self.perms.borrow_mut().tracked_remove(cut_addr));
        node_update_prev::<T>(cut_addr, &mut cut_perm, None);
        proof {
            self.perms.borrow_mut().tracked_insert(cut_addr, cut_perm.get());
        }

        let mut pt_perm = Tracked(self.perms.borrow_mut().tracked_remove(prefix_tail_addr));
        node_update_next::<T>(prefix_tail_addr, &mut pt_perm, None);
        proof {
            self.perms.borrow_mut().tracked_insert(prefix_tail_addr, pt_perm.get());
        }

        self.head = Some(cut_addr);

        // split the perms map in O(1)
        let tracked prefix_perms = self.perms.borrow_mut().tracked_remove_keys(prefix_set);

        // finish self (suffix)
        self.addr_list = Ghost(old(self).addr_list@.subrange(i as int, old(self).length as int));
        self.value_list = Ghost(old(self).value_list@.subrange(i as int, old(self).length as int));
        self.map = Ghost(old(self).map@.remove_keys(prefix_set));
        self.reverse_map = Ghost(old(self).reverse_map@.remove_keys(prefix_value_set));
        self.length = self.length - i;

        // build ret (prefix)
        let ret = LinkedList::<T, MAJOR> {
            perms: Tracked(prefix_perms),
            addr_list: Ghost(old(self).addr_list@.subrange(0, i as int)),
            value_list: Ghost(old(self).value_list@.subrange(0, i as int)),
            length: i,
            head: head0,
            tail: Some(prefix_tail_addr),
            map: Ghost(old(self).map@.restrict(prefix_set)),
            reverse_map: Ghost(old(self).reverse_map@.restrict(prefix_value_set)),
            container_depth: self.container_depth,
            minor: self.minor,
        };

        // ---- ret.wf() ----
        assert(ret.wf_perms());
        assert(ret.wf_addr_list());
        assert(ret.wf_value_list());
        assert(ret.wf_head());
        assert(ret.wf_tail());
        assert(ret.wf_prev());
        assert(ret.wf_next());
        assert(ret.wf_map());
        assert(ret.value_list_unique());
        assert(ret.wf_reverse_map());
        assert(ret.wf());

        // ---- self.wf() (suffix) ----
        assert(self.wf_perms());
        assert(self.wf_addr_list());
        assert(self.wf_value_list());
        assert(self.wf_head());
        assert(self.wf_tail());
        assert(self.wf_prev());
        assert(self.wf_next());
        assert(self.wf_map());
        assert(self.value_list_unique());
        assert(self.wf_reverse_map());
        assert(self.wf());

        ret
    }

    pub fn append_prefix(&mut self, prefix: LinkedList<T, MAJOR>)
        requires
            old(self).wf(),
            old(self).length == 0,
            prefix.wf(),
        ensures
            // ---- self now holds the whole prefix ----
            final(self).wf(),
            final(self)@ == prefix@,
            final(self).length == prefix.length,
            final(self).dom() == prefix.dom(),
            final(self).map() == prefix.map(),
            // ---- self keeps its own lock identity ----
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
    {
        proof{
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
            reveal(LinkedList::wf_head);
            reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_prev);
            reveal(LinkedList::wf_next);
            reveal(LinkedList::wf_map);
            reveal(LinkedList::value_list_unique);
            reveal(LinkedList::wf_reverse_map);
        }
        self.perms = prefix.perms;
        self.addr_list = prefix.addr_list;
        self.value_list = prefix.value_list;
        self.length = prefix.length;
        self.head = prefix.head;
        self.tail = prefix.tail;
        self.map = prefix.map;
        self.reverse_map = prefix.reverse_map;

        assert(self.wf_perms());
        assert(self.wf_addr_list());
        assert(self.wf_value_list());
        assert(self.wf_head());
        assert(self.wf_tail());
        assert(self.wf_prev());
        assert(self.wf_next());
        assert(self.wf_map());
        assert(self.value_list_unique());
        assert(self.wf_reverse_map()) by {
            assert(self.map() == prefix.map());
            assert(self.revese_map() == prefix.revese_map());
            assert(prefix.wf_reverse_map());
        }
        assert(self.wf());
    }

}

} // verus!

mod remove_impl;

