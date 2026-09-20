use super::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {

impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR>{

    pub fn remove_helper(&mut self, addr: usize) -> (ret: (usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).wf(),
            old(self).dom().contains(addr),
            old(self).length != 0,
            old(self).head.unwrap() != addr,
            old(self).tail.unwrap() != addr,
        ensures
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).map().spec_index(addr),

            final(self).wf(),
            final(self).dom() == old(self).dom().remove(addr),
            final(self).map() == old(self).map().remove(addr),
            final(self).length == old(self).length - 1,
            old(self).view().no_duplicates() ==> final(self).view() == old(self).view().remove_value(old(self).map().spec_index(addr)),
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
    {
        assert({
            &&& self.addr_list.view().contains(addr)
            &&& self.perms.view().spec_index(addr).is_init()
            &&& self.perms.view().spec_index(addr).addr() == addr
        }) by {
            reveal(LinkedList::wf_perms);
        };
        let ghost_index = Ghost(self.addr_list.view().index_of(addr));
        assert(
            self.addr_list.view().len() == self.length
            && 0 <= ghost_index.view() < self.length
            && self.addr_list.view().spec_index(ghost_index.view()) == addr
        ) by {
            reveal(LinkedList::wf_addr_list);
        };
        assert(0 < ghost_index.view()) by {
            reveal(LinkedList::wf_head);
        };
        assert(ghost_index.view() + 1 < self.length) by {
            reveal(LinkedList::wf_tail);
        };
        assert(
            self.map().dom() == self.perms.view().dom()
            && self.map().spec_index(addr)
                == self.perms.view().spec_index(addr).value().view()
        ) by {
            reveal(LinkedList::wf_map);
        };
        assert(
            self.value_list.view().len() == self.length
            && self.value_list.view().spec_index(ghost_index.view())
                == self.map().spec_index(addr)
        ) by {
            reveal(LinkedList::wf_value_list);
        };
        assert(
            self.perms.view().spec_index(addr).value().prev is Some
            && self.perms.view().spec_index(addr).value().prev.unwrap()
                == self.addr_list.view().spec_index(ghost_index.view() - 1)
        ) by {
            reveal(LinkedList::wf_prev);
        };
        assert(
            self.perms.view().spec_index(addr).value().next is Some
            && self.perms.view().spec_index(addr).value().next.unwrap()
                == self.addr_list.view().spec_index(ghost_index.view() + 1)
        ) by {
            reveal(LinkedList::wf_next);
        };
        assert(
            self.addr_list.view().spec_index(ghost_index.view() - 1) != addr
            && self.addr_list.view().spec_index(ghost_index.view() + 1) != addr
            && self.addr_list.view().spec_index(ghost_index.view() - 1)
                != self.addr_list.view().spec_index(ghost_index.view() + 1)
        ) by {
            reveal(LinkedList::wf_addr_list);
        };
        assert(
            self.perms.view().dom().contains(
                self.addr_list.view().spec_index(ghost_index.view() - 1),
            )
            && self.perms.view().dom().contains(
                self.addr_list.view().spec_index(ghost_index.view() + 1),
            )
            && self.perms.view().spec_index(
                self.addr_list.view().spec_index(ghost_index.view() - 1),
            ).is_init()
            && self.perms.view().spec_index(
                self.addr_list.view().spec_index(ghost_index.view() - 1),
            ).addr() == self.addr_list.view().spec_index(ghost_index.view() - 1)
            && self.perms.view().spec_index(
                self.addr_list.view().spec_index(ghost_index.view() + 1),
            ).is_init()
            && self.perms.view().spec_index(
                self.addr_list.view().spec_index(ghost_index.view() + 1),
            ).addr() == self.addr_list.view().spec_index(ghost_index.view() + 1)
        ) by {
            reveal(LinkedList::wf_perms);
        };

        let tracked old_perm = self.perms.borrow_mut().tracked_remove(addr);
        let old_node: &Node<T> = PPtr::<Node<T>>::from_usize(addr).borrow(Tracked(&old_perm));
        let prev = old_node.prev.unwrap();
        let next = old_node.next.unwrap();

        let mut prev_perm = Tracked(self.perms.borrow_mut().tracked_remove(prev));
        let mut next_perm = Tracked(self.perms.borrow_mut().tracked_remove(next));
        node_update_next::<T>(prev, &mut prev_perm, Some(next));
        node_update_prev::<T>(next, &mut next_perm, Some(prev));

        proof {
            self.perms.borrow_mut().tracked_insert(prev, prev_perm.get());
            self.perms.borrow_mut().tracked_insert(next, next_perm.get());
        }
        self.addr_list = Ghost(self.addr_list.view().subrange(0, ghost_index.view()).add(self.addr_list.view().subrange(ghost_index.view() + 1, self.length as int)));
        self.value_list = Ghost(self.value_list.view().subrange(0, ghost_index.view()).add(self.value_list.view().subrange(ghost_index.view() + 1, self.length as int)));
        self.map = Ghost(self.map.view().remove(addr));
        self.length = self.length - 1;

        assert(self.wf_perms()) by {
            seq_remove_lemma::<usize>();
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
        };
        assert(self.wf_addr_list()) by { reveal(LinkedList::wf_addr_list); };
        assert(self.wf_value_list()) by {
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
        };
        assert(self.wf_head()) by {
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_head);
        };
        assert(self.wf_tail()) by {
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_tail);
        };
        assert(self.wf_prev()) by {
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_prev);
        };
        assert(self.wf_next()) by {
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_next);
        };
        assert({
            &&& self.map().dom() == self.perms.view().dom()
            &&& self.wf_map()
        }) by {
            reveal(LinkedList::wf_map);
        };
        assert(self.value_list_unique()) by {
            reveal(LinkedList::value_list_unique);
            old(self).value_list.view().remove_ensures(ghost_index.view());
        };
        assert(
            old(self).view().no_duplicates()
            ==> self.view()
                == old(self).view().remove_value(old(self).map().spec_index(addr))
        ) by {
            seq_remove_lemma::<T>();
        };

        (addr, Tracked(old_perm))
    }

    pub fn remove(&mut self, addr: usize) -> (ret: (usize, Tracked<PointsTo<Node<T>>>))
        requires
            old(self).wf(),
            old(self).dom().contains(addr),

        ensures
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).map().spec_index(addr),

            final(self).wf(),
            final(self).dom() == old(self).dom().remove(addr),
            final(self).map() == old(self).map().remove(addr),
            final(self).length == old(self).length - 1,
            old(self).view().no_duplicates() ==> final(self).view() == old(self).view().remove_value(old(self).map().spec_index(addr)),
            final(self).container_depth == old(self).container_depth,
            final(self).lock_minor() == old(self).lock_minor(),
    {
        assert({
            &&& self.length != 0
            &&& self.head is Some
            &&& self.tail is Some
            &&& self.addr_list.view().len() == self.length
            &&& self.addr_list.view().no_duplicates()
            &&& self.view().len() == self.length
            &&& self.perms.view().dom().contains(addr)
            &&& self.perms.view().spec_index(addr).is_init()
            &&& self.perms.view().spec_index(addr).addr() == addr
            &&& self.map().dom().contains(addr)
            &&& self.map().spec_index(addr)
                == self.perms.view().spec_index(addr).value().view()
        }) by {
            reveal(LinkedList::wf_perms);
            reveal(LinkedList::wf_addr_list);
            reveal(LinkedList::wf_value_list);
            reveal(LinkedList::wf_head);
            reveal(LinkedList::wf_tail);
            reveal(LinkedList::wf_map);
        };
        if self.length == 1 {
            assert({
                &&& self.head.unwrap() == addr
                &&& self.view().spec_index(0) == self.map().spec_index(addr)
            }) by {
                reveal(LinkedList::wf_perms);
                reveal(LinkedList::wf_value_list);
                reveal(LinkedList::wf_head);
                reveal(LinkedList::wf_map);
            };
            let ret = self.pop_head();
            assert(
                old(self).view().no_duplicates()
                ==> self.view()
                    == old(self).view().remove_value(old(self).map().spec_index(addr))
            ) by {
                seq_skip_lemma::<T>();
            };
            return ret;
        } else if self.head.unwrap() == addr {
            assert(self.view().spec_index(0) == self.map().spec_index(addr)) by {
                reveal(LinkedList::wf_value_list);
                reveal(LinkedList::wf_head);
                reveal(LinkedList::wf_map);
            };
            let ret = self.pop_head();
            assert(
                old(self).view().no_duplicates()
                ==> self.view()
                    == old(self).view().remove_value(old(self).map().spec_index(addr))
            ) by {
                seq_skip_lemma::<T>();
            };
            return ret;
        } else if self.tail.unwrap() == addr {
            assert({
                &&& self.addr_list.view().spec_index(self.length - 1) == addr
                &&& self.perms.view().spec_index(addr).value().prev is Some
                &&& self.perms.view().spec_index(addr).value().prev.unwrap()
                    == self.addr_list.view().spec_index(self.length - 2)
                &&& self.perms.view().dom().contains(
                    self.addr_list.view().spec_index(self.length - 2),
                )
                &&& self.perms.view().spec_index(
                    self.addr_list.view().spec_index(self.length - 2),
                ).is_init()
                &&& self.perms.view().spec_index(
                    self.addr_list.view().spec_index(self.length - 2),
                ).addr() == self.addr_list.view().spec_index(self.length - 2)
                &&& self.value_list.view().len() == self.length
                &&& self.value_list.view().spec_index(self.length - 1)
                    == self.map().spec_index(addr)
            }) by {
                reveal(LinkedList::wf_perms);
                reveal(LinkedList::wf_value_list);
                reveal(LinkedList::wf_tail);
                reveal(LinkedList::wf_prev);
                reveal(LinkedList::wf_map);
            };

            let old_tail_addr = addr;
            let tracked old_tail_perm = self.perms.borrow_mut().tracked_remove(old_tail_addr);
            let old_tail: &Node<T> = PPtr::<Node<T>>::from_usize(old_tail_addr).borrow(Tracked(&old_tail_perm));
            let new_tail_addr = old_tail.prev.unwrap();
            self.tail = Some(new_tail_addr);
            let mut new_tail_perm = Tracked(self.perms.borrow_mut().tracked_remove(new_tail_addr));
            node_update_next::<T>(new_tail_addr, &mut new_tail_perm, None);
            proof {
                self.perms.borrow_mut().tracked_insert(new_tail_addr, new_tail_perm.get());
            }
            self.addr_list = Ghost(self.addr_list.view().subrange(0, self.length as int - 1).add(self.addr_list.view().subrange(self.length as int, self.length as int)));
            self.value_list = Ghost(self.value_list.view().subrange(0, self.length as int - 1).add(self.value_list.view().subrange(self.length as int, self.length as int)));
            self.map = Ghost(self.map.view().remove(old_tail_addr));
            self.length = self.length - 1;

            assert(self.wf()) by {
                seq_remove_lemma::<usize>();
                reveal(LinkedList::wf_perms);
                reveal(LinkedList::wf_addr_list);
                reveal(LinkedList::wf_value_list);
                reveal(LinkedList::wf_head);
                reveal(LinkedList::wf_tail);
                reveal(LinkedList::wf_prev);
                reveal(LinkedList::wf_next);
                reveal(LinkedList::wf_map);
                reveal(LinkedList::value_list_unique);
            };
            assert(
                old(self).view().no_duplicates()
                ==> self.view()
                    == old(self).view().remove_value(old(self).map().spec_index(addr))
            ) by {
                seq_remove_lemma::<T>();
            };
            return (addr, Tracked(old_tail_perm));
        } else {
            return self.remove_helper(addr);
        }
    }
}
} // verus!
