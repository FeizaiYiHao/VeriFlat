use super::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {

impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR>{

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

            final(self).wf(),
            final(self).dom() == old(self).dom().remove(addr),
            final(self).map() == old(self).map().remove(addr),
            final(self).length == old(self).length - 1,
            old(self)@.no_duplicates() ==> final(self)@ == old(self)@.remove_value(old(self).map()[addr]),
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
            self.reverse_map = Ghost(self.reverse_map@.remove(self.map@[addr]));
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
            assert(self.value_list_unique());
            assert(self.wf_reverse_map());
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

            final(self).wf(),
            final(self).dom() == old(self).dom().remove(addr),
            final(self).map() == old(self).map().remove(addr),
            final(self).length == old(self).length - 1,
            old(self)@.no_duplicates() ==> final(self)@ == old(self)@.remove_value(old(self).map()[addr]),
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
            self.reverse_map = Ghost(self.reverse_map@.remove(self.map@[old_tail_addr]));
            self.map = Ghost(self.map@.remove(old_tail_addr));
            self.length = self.length - 1;

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

            return (addr, Tracked(old_tail_perm));
        }else{
            return self.remove_helper(addr);
        }
    }
}
} // verus!
