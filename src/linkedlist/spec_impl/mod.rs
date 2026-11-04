use vstd::prelude::*;
use vstd::simple_pptr::*;

use crate::*;

use super::*;

verus! {
/// A doubly linked list of nodes in memory, with ghost views of its node addresses and values.
#[verifier::reject_recursive_types(T)]
pub struct LinkedList<T, const MAJOR: LockMajorId> {
    /// Points-to tokens of the nodes, keyed by node address.
    pub perms: Tracked<Map<usize, PointsTo<Node<T>>>>,
    /// Node addresses from head to tail.
    pub addr_list: Ghost<Seq<usize>>,
    /// Node values from head to tail.
    pub value_list: Ghost<Seq<T>>,
    pub length: usize,
    pub head: Option<usize>,
    pub tail: Option<usize>,
    /// Node address to node value.
    pub map: Ghost<Map<usize, T>>,

    /// Lock-ordering metadata only; never read by exec code.
    pub container_depth: Ghost<Option<usize>>,

    /// Lock minor id of the list (`lock_minor`).
    pub minor: Ghost<Option<usize>>,
}

impl<T, const MAJOR: LockMajorId> LockOwnerIdTrait for LinkedList<T, MAJOR> {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::None }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::None }
}
impl<T, const MAJOR: LockMajorId> LockInvTrait for LinkedList<T, MAJOR> {
    open spec fn inv(&self) -> bool { self.wf() }
}

impl<T, const MAJOR: LockMajorId> LockMajorTrait for LinkedList<T, MAJOR> {
    open spec fn lock_major_1(&self) -> LockMajorId { MAJOR }
    open spec fn lock_major_2(&self) -> LockMajorId { 233 }
    open spec fn lock_major_3(&self) -> LockMajorId { 233 }
    open spec fn lock_major_default(&self) -> LockMajorId { 233 }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}

impl<T, const MAJOR: LockMajorId> LockMinorTrait for LinkedList<T, MAJOR> {
    open spec fn lock_minor(&self) -> LockMinorId {
        if self.minor.view() is Some { seq![self.minor.view().unwrap()] }
        else { seq![233] }
    }
}

//spec
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR> {
    pub open spec fn view(&self) -> Seq<T> { self.value_list.view() }

    pub open spec fn spec_index(&self, index: usize) -> T
        recommends
            index < self.length,
    {
        self.value_list.view().spec_index(index as int)
    }

    pub open spec fn dom(&self) -> Set<usize>
    {
        self.perms.view().dom()
    }

    pub open spec fn map(&self) -> Map<usize, T> { self.map.view() }
    pub open spec fn spec_len(&self) -> usize { self.view().len() as usize }

    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (ret: usize)
        requires
            self.wf()
        ensures
            ret == self.len()
    {
        proof { reveal(LinkedList::wf_value_list); }
        self.length
    }

    /// Expose the opaque `wf_value_list` fact that the stored `length` equals the view length.
    pub proof fn wf_implies_view_len_eq_len(&self)
        requires
            self.wf(),
        ensures
            self.view().len() == self.spec_len(),
            self.view().len() == self.length,
    {
        reveal(LinkedList::wf_value_list);
    }

    /// Address ↔ value uniqueness: in a wf list the address holding a given value is unique. Concretely, any two
    /// in-domain addresses mapping to the same value are equal.
    pub proof fn wf_and_equal_values_implies_equal_addrs(&self, a: usize, b: usize)
        requires
            self.wf(),
            self.map().dom().contains(a),
            self.map().dom().contains(b),
            self.map().spec_index(a) == self.map().spec_index(b),
        ensures
            a == b,
    { reveal(LinkedList::wf_map); }

    /// Point instance of `wf_map` at `addr`: map membership agrees with `dom()` and the mapped value is the node's value.
    pub proof fn wf_map_at(&self, addr: usize)
        requires
            self.wf_map(),
        ensures
            self.map().dom().contains(addr) == self.dom().contains(addr),
            self.map().dom().contains(addr) ==> self.map().spec_index(addr) == self.perms.view().spec_index(addr).value().view(),
    { reveal(LinkedList::wf_map); }

    /// Every node token is initialized at its own address, and the tokens are exactly the nodes of `addr_list`.
    #[verifier::opaque]
    pub open spec fn wf_perms(&self) -> bool {
        &&& forall|addr: usize|
            #![trigger self.perms.view().spec_index(addr).is_init()]
            #![trigger self.perms.view().spec_index(addr).addr()]
            #![trigger self.perms.view().dom().contains(addr)]
            self.perms.view().dom().contains(addr)
                ==>
                self.perms.view().spec_index(addr).is_init()
                && self.perms.view().spec_index(addr).addr() == addr
        &&& forall|addr: usize|
            #![trigger self.perms.view().dom().contains(addr)]
            #![trigger self.addr_list.view().contains(addr)]
            self.perms.view().dom().contains(addr) == self.addr_list.view().contains(addr)
    }

    /// `value_list` has `length` entries, each the value of the node at the same position of `addr_list`.
    #[verifier::opaque]
    pub open spec fn wf_value_list(&self) -> bool {
        &&& self.len() == self.length
        &&& self.value_list.view().len() == self.length
        &&& forall|i: int|
            #![trigger self.value_list.view().spec_index(i)]
            #![trigger self.perms.view().spec_index(self.addr_list.view().spec_index(i)).value().view()]
            0 <= i < self.length
                ==>
                self.value_list.view().spec_index(i) == self.perms.view().spec_index(self.addr_list.view().spec_index(i)).value().view()
    }

    /// No value appears at two positions of the list.
    #[verifier::opaque]
    pub open spec fn value_list_unique(&self) -> bool {
        &&& forall|i: int, j: int|
            #![trigger self.value_list.view().spec_index(i), self.value_list.view().spec_index(j)]
            0 <= i < self.length
                && 0 <= j < self.length
                && i != j
                ==>
                self.value_list.view().spec_index(i) != self.value_list.view().spec_index(j)
    }

    /// `addr_list` has `length` distinct node addresses.
    #[verifier::opaque]
    pub open spec fn wf_addr_list(&self) -> bool {
        &&& self.addr_list.view().len() == self.length
        &&& self.addr_list.view().no_duplicates()
    }

    /// `head` is the first node, which has no predecessor, and is absent exactly for an empty list.
    #[verifier::opaque]
    pub open spec fn wf_head(&self) -> bool {
        &&& self.length == 0 <==> self.head is None
        &&& self.head is Some
            ==>
            self.addr_list.view().spec_index(0) == self.head.unwrap()
            && self.perms.view().spec_index(self.head.unwrap()).value().prev is None
    }

    /// `tail` is the last node, which has no successor, and is absent exactly for an empty list.
    #[verifier::opaque]
    pub open spec fn wf_tail(&self) -> bool {
        &&& self.length == 0 <==> self.tail is None
        &&& self.tail is Some
            ==>
            self.addr_list.view().spec_index(self.length - 1) == self.tail.unwrap()
            && self.perms.view().spec_index(self.tail.unwrap()).value().next is None
    }

    /// Every node after the first links back to its predecessor in `addr_list`.
    #[verifier::opaque]
    pub open spec fn wf_prev(&self) -> bool {
        &&& forall|i: int|
            #![trigger self.perms.view().spec_index(self.addr_list.view().spec_index(i)).value().prev]
            1 <= i < self.length
                ==>
                self.perms.view().spec_index(self.addr_list.view().spec_index(i)).value().prev is Some
                && self.perms.view().spec_index(self.addr_list.view().spec_index(i)).value().prev.unwrap() == self.addr_list.view().spec_index(i - 1)
    }

    /// Every node before the last links forward to its successor in `addr_list`.
    #[verifier::opaque]
    pub open spec fn wf_next(&self) -> bool {
        &&& forall|i: int|
            #![trigger self.perms.view().spec_index(self.addr_list.view().spec_index(i)).value().next]
            0 <= i < self.length - 1
                ==>
                self.perms.view().spec_index(self.addr_list.view().spec_index(i)).value().next is Some
                && self.perms.view().spec_index(self.addr_list.view().spec_index(i)).value().next.unwrap() == self.addr_list.view().spec_index(i + 1)
    }

    /// `map` sends each node address to that node's value, and no two nodes share a value.
    #[verifier::opaque]
    pub open spec fn wf_map(&self) -> bool {
        &&& self.map().dom() == self.perms.view().dom()
        &&& forall|addr: usize|
            #![trigger self.map().spec_index(addr)]
            #![trigger self.perms.view().spec_index(addr)]
            self.map().dom().contains(addr)
                ==>
                self.map().spec_index(addr) == self.perms.view().spec_index(addr).value().view()
        &&& forall|addr_i: usize, addr_j: usize|
            #![trigger self.map().spec_index(addr_i), self.map().spec_index(addr_j)]
            self.map().dom().contains(addr_i)
                && self.map().dom().contains(addr_j)
                && addr_i != addr_j
                ==>
                self.map().spec_index(addr_i) != self.map().spec_index(addr_j)
    }

    /// The list is well formed: every leaf above holds.
    pub open spec fn wf(&self) -> bool {
        &&& self.wf_perms()
        &&& self.wf_addr_list()
        &&& self.wf_value_list()
        &&& self.wf_head()
        &&& self.wf_tail()
        &&& self.wf_prev()
        &&& self.wf_next()
        &&& self.wf_map()
        &&& self.value_list_unique()
    }
}

// exec
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR> {
    pub fn new(container_depth: Option<usize>, minor: Option<usize>) -> (ret: Self)
        ensures
            ret.wf(),
            ret.view() == Seq::<T>::empty(),
            ret.dom() == Set::<usize>::empty(),
            ret.map() == Map::<usize, T>::empty(),
            ret.length == 0,
            ret.container_depth.view() == container_depth,
            ret.minor.view() == minor,
    {
        let ret = Self {
            perms: Tracked(Map::<usize, PointsTo<Node<T>>>::tracked_empty()), addr_list: Ghost(Seq::empty()), value_list: Ghost(Seq::empty()),
            length: 0, head: None, tail: None, map: Ghost(Map::empty()), container_depth: Ghost(container_depth), minor: Ghost(minor),
        };
        assert(ret.wf()) by {
            reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_head); reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_prev); reveal(LinkedList::wf_next); reveal(LinkedList::wf_map); reveal(LinkedList::value_list_unique);
        };
        ret
    }

    pub fn push_tail(&mut self, addr: usize, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).wf(),
            old(self).length != usize::MAX,
            perm.view().is_init(),
            perm.view().addr() == addr,
            old(self).view().contains(perm.view().value().view()) == false,
        ensures
            final(self).wf(),
            final(self).length == old(self).length + 1,
            final(self).view() == old(self).view().push(perm.view().value().view()),
            final(self).dom() == old(self).dom().insert(addr),
            final(self).map() == old(self).map().insert(addr, perm.view().value().view()),
            forall|value: T| #![trigger final(self).view().contains(value)] old(self).view().contains(value) ==> final(self).view().contains(value),
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
            old(self).dom().contains(addr) == false,
            old(self).map().dom().contains(addr) == false,
    {
        proof { reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_tail); reveal(LinkedList::wf_map); }
        let mut perm = perm;
        if self.length == 0 {
            self.length = self.length + 1;
            self.addr_list = Ghost(self.addr_list.view().push(addr));
            self.value_list = Ghost(self.value_list.view().push(perm.view().value().view()));
            node_update_prev(addr, &mut perm, None);
            node_update_next(addr, &mut perm, None);
            self.tail = Some(addr);
            self.head = Some(addr);
            self.map = Ghost(self.map.view().insert(addr, perm.view().value().view()));
            proof { self.perms.borrow_mut().tracked_insert(addr, perm.get()); }

            proof { seq_push_implies_contains::<usize>(); }
            assert(self.wf()) by { reveal(LinkedList::wf_head); reveal(LinkedList::wf_prev); reveal(LinkedList::wf_next); reveal(LinkedList::value_list_unique); };
        } else {
            proof { node_perm_disjoint(perm.borrow_mut(), self.perms.borrow_mut()); }
            self.length = self.length + 1;
            self.addr_list = Ghost(self.addr_list.view().push(addr));
            self.value_list = Ghost(self.value_list.view().push(perm.view().value().view()));
            node_update_prev(addr, &mut perm, self.tail);
            node_update_next(addr, &mut perm, None);

            let old_tail_addr = self.tail.unwrap();
            let mut old_tail_perm = Tracked(self.perms.borrow_mut().tracked_remove(old_tail_addr));
            node_update_next::<T>(old_tail_addr, &mut old_tail_perm, Some(addr));
            proof { self.perms.borrow_mut().tracked_insert(old_tail_addr, old_tail_perm.get()); }

            self.tail = Some(addr);
            self.map = Ghost(self.map.view().insert(addr, perm.view().value().view()));
            proof { self.perms.borrow_mut().tracked_insert(addr, perm.get()); }

            proof { seq_push_implies_contains::<usize>(); seq_push_implies_contains::<T>(); seq_push_absent_implies_no_duplicates_and_index_of::<usize>(); }

            assert(self.wf_head() && self.wf_tail()) by { reveal(LinkedList::wf_head); reveal(LinkedList::wf_prev); reveal(LinkedList::wf_next); reveal(LinkedList::value_list_unique); };
            assert(self.wf()) by { reveal(LinkedList::wf_head); reveal(LinkedList::wf_prev); reveal(LinkedList::wf_next); reveal(LinkedList::value_list_unique); };
        }
    }

    pub fn push_head(&mut self, addr: usize, perm: Tracked<PointsTo<Node<T>>>)
        requires
            old(self).wf(),
            old(self).length != usize::MAX,
            perm.view().is_init(),
            perm.view().addr() == addr,
            old(self).view().contains(perm.view().value().view()) == false,
        ensures
            final(self).wf(),
            final(self).length == old(self).length + 1,
            final(self).view() == old(self).view().insert(0, perm.view().value().view()),
            final(self).dom() == old(self).dom().insert(addr),
            final(self).map() == old(self).map().insert(addr, perm.view().value().view()),
            final(self).container_depth == old(self).container_depth,
            final(self).minor == old(self).minor,
            old(self).dom().contains(addr) == false,
            old(self).map().dom().contains(addr) == false,
    {
        proof { reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_head); reveal(LinkedList::wf_map); }
        let mut perm = perm;
        if self.length == 0 {
            self.length = self.length + 1;
            self.addr_list = Ghost(self.addr_list.view().push(addr));
            self.value_list = Ghost(self.value_list.view().push(perm.view().value().view()));
            node_update_prev(addr, &mut perm, None);
            node_update_next(addr, &mut perm, None);
            self.tail = Some(addr);
            self.head = Some(addr);
            self.map = Ghost(self.map.view().insert(addr, perm.view().value().view()));
            proof { self.perms.borrow_mut().tracked_insert(addr, perm.get()); }

            proof { seq_push_implies_contains::<usize>(); }
            assert(self.wf()) by { reveal(LinkedList::wf_tail); reveal(LinkedList::wf_prev); reveal(LinkedList::wf_next); reveal(LinkedList::value_list_unique); };
        } else {
            proof { node_perm_disjoint(perm.borrow_mut(), self.perms.borrow_mut()); }
            self.length = self.length + 1;
            self.addr_list = Ghost(self.addr_list.view().insert(0, addr));
            self.value_list = Ghost(self.value_list.view().insert(0, perm.view().value().view()));
            node_update_prev(addr, &mut perm, None);
            node_update_next(addr, &mut perm, self.head);

            let old_head_addr = self.head.unwrap();
            let mut old_head_perm = Tracked(self.perms.borrow_mut().tracked_remove(old_head_addr));
            node_update_prev::<T>(old_head_addr, &mut old_head_perm, Some(addr));
            proof { self.perms.borrow_mut().tracked_insert(old_head_addr, old_head_perm.get()); }

            self.head = Some(addr);
            self.map = Ghost(self.map.view().insert(addr, perm.view().value().view()));
            proof { self.perms.borrow_mut().tracked_insert(addr, perm.get()); }

            proof { Self::push_head_eof_wf(*old(self), *self, addr, old_head_addr); }
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
            ret.0 == self.head.unwrap(),
            // address is the head, exposed only through the logical map.
            self.dom().contains(ret.0),
            self.map().dom().contains(ret.0),
            // value is the head element, == map[head].
            ret.1 == self.view().spec_index(0),
            self.view().contains(ret.1),
            ret.1 == self.map().spec_index(ret.0),
    {
        proof { reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_head); reveal(LinkedList::wf_map); }
        let head_addr = self.head.unwrap();
        let tracked head_perm = self.perms.borrow().tracked_borrow(head_addr);
        let node: &Node<T> = PPtr::<Node<T>>::from_usize(head_addr).borrow(Tracked(head_perm));
        (head_addr, node.value)
    }

    pub fn get(&self, index: usize) -> (ret: T)
        where T: Copy
        requires
            self.wf(),
            index < self.len(),
        ensures
            ret == self.view().spec_index(index as int),
            self.view().contains(ret),
    {
        proof { reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_head); }
        let mut current = self.head.unwrap();
        let mut i = 0usize;
        while i < index
            invariant
                self.wf(),
                index < self.length,
                i <= index,
                current == self.addr_list.view().spec_index(i as int),
            decreases index - i,
        {
            proof { reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_next); }
            let tracked node_perm = self.perms.borrow().tracked_borrow(current);
            let node = PPtr::<Node<T>>::from_usize(current).borrow(Tracked(node_perm));
            current = node.next.unwrap();
            i = i + 1;
        }
        proof { reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); }
        let tracked node_perm = self.perms.borrow().tracked_borrow(current);
        let node = PPtr::<Node<T>>::from_usize(current).borrow(Tracked(node_perm));
        node.value
    }

    pub fn pop_head(&mut self) -> (ret: (usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).wf(),
            old(self).len() != 0,
        ensures
            ret.0 == old(self).head.unwrap(),
            final(self).wf(),
            final(self).dom() == old(self).dom().remove(ret.0),
            final(self).view() == old(self).view().skip(1),
            final(self).length == old(self).length - 1,
            final(self).map() == old(self).map().remove(ret.0),
            forall|value: T| #![trigger final(self).view().contains(value)] old(self).view().contains(value) && value != ret.1.view().value().view() ==> final(self).view().contains(value),
            forall|value: T| #![trigger final(self).view().contains(value)] final(self).view().contains(value) ==> old(self).view().contains(value),
            !final(self).view().contains(ret.1.view().value().view()),
            forall|old_addr: usize|
                #![trigger final(self).map().dom().contains(old_addr)]
                old(self).map().dom().contains(old_addr) && old_addr != ret.0 ==> {
                    &&& final(self).map().dom().contains(old_addr)
                    &&& final(self).map().spec_index(old_addr) == old(self).map().spec_index(old_addr)
                },
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).view().spec_index(0),
            ret.1.view().value().view() == old(self).map().spec_index(ret.0),
            // The popped node was the head — hence in the pre-pop domain. (Used
            // by callers that need map[ret.0] to be a live entry.)
            old(self).dom().contains(ret.0),
            old(self).map().dom().contains(ret.0),
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
    {
        proof { reveal(LinkedList::wf_perms); reveal(LinkedList::wf_addr_list); reveal(LinkedList::wf_value_list); reveal(LinkedList::wf_head); reveal(LinkedList::wf_next); reveal(LinkedList::wf_map); }
        if self.length != 1 {
            proof { seq_skip_one_implies_contains_and_index_shift::<usize>(); seq_skip_one_implies_contains_and_index_shift::<T>(); seq_skip_one_implies_index_of_minus_one::<usize>(); seq_skip_one_implies_index_of_minus_one::<T>(); }
            let old_head_addr = self.head.unwrap();
            let tracked old_head_perm = self.perms.borrow_mut().tracked_remove(old_head_addr);
            let old_head: &Node<T> = PPtr::<Node<T>>::from_usize(old_head_addr).borrow(Tracked(&old_head_perm));
            let new_head_addr = old_head.next.unwrap();
            self.head = Some(new_head_addr);
            self.length = self.length - 1;
            let mut new_head_perm = Tracked(self.perms.borrow_mut().tracked_remove(new_head_addr));
            node_update_prev::<T>(new_head_addr, &mut new_head_perm, None);
            proof { self.perms.borrow_mut().tracked_insert(new_head_addr, new_head_perm.get()); }
            self.addr_list = Ghost(self.addr_list.view().skip(1));
            self.value_list = Ghost(self.value_list.view().skip(1));
            self.map = Ghost(self.map.view().remove(old_head_addr));

            proof { Self::pop_head_eof_wf(*old(self), *self, old_head_addr, new_head_addr); }

            (old_head_addr, Tracked(old_head_perm))
        } else {
            let old_head_addr = self.head.unwrap();
            let tracked old_head_perm = self.perms.borrow_mut().tracked_remove(old_head_addr);
            self.addr_list = Ghost(Seq::empty());
            self.value_list = Ghost(Seq::empty());
            self.length = 0;
            self.head = None;
            self.tail = None;
            self.map = Ghost(self.map.view().remove(old_head_addr));

            assert(self.wf()) by { reveal(LinkedList::wf_tail); reveal(LinkedList::wf_prev); reveal(LinkedList::value_list_unique); };

            (old_head_addr, Tracked(old_head_perm))
        }
    }
}
} // verus!

mod remove_impl;
mod unlink_interior_node_eof;
mod push_pop_eof;
