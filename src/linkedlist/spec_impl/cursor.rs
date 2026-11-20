use super::*;

verus! {
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR> {
    pub fn cursor_head(&self) -> (ret: Option<usize>)
        requires
            self.wf(),
        ensures
            ret == self.head,
            ret is None <==> self.length == 0,
            ret is Some ==> self.dom().contains(ret.unwrap()),
            ret is Some ==> self.addr_list.view().spec_index(0) == ret.unwrap(),
            ret is Some ==> self.addr_list.view().index_of(ret.unwrap()) == 0,
    {
        proof {
            self.wf_implies_view_len_eq_len();
            if self.head is Some { self.wf_perms_at(self.head.unwrap()); }
            assert(self.head is Some ==> self.addr_list.view().index_of(self.head.unwrap()) == 0) by { seq_no_duplicates_implies_index_of_roundtrip::<usize>(); };
        }
        self.head
    }

    pub fn cursor_read(&self, addr: usize) -> (ret: (T, Option<usize>))
        where T: Copy
        requires
            self.wf(),
            self.dom().contains(addr),
        ensures
            ret.0 == self.map().spec_index(addr),
            self.view().contains(ret.0),
            self.view().to_set().contains(ret.0),
            self.view().skip(self.addr_list.view().index_of(addr)).to_set().contains(ret.0),
            0 <= self.addr_list.view().index_of(addr) < self.length,
            self.view().spec_index(self.addr_list.view().index_of(addr)) == ret.0,
            self.view().index_of(ret.0) == self.addr_list.view().index_of(addr),
            ret.1 == self.perms.view().spec_index(addr).value().next,
            ret.1 is Some ==> self.dom().contains(ret.1.unwrap()),
            ret.1 is None <==> self.addr_list.view().index_of(addr) + 1 == self.length,
            ret.1 is Some ==> ret.1.unwrap() == self.addr_list.view().spec_index(self.addr_list.view().index_of(addr) + 1),
            ret.1 is Some ==> self.view().spec_index(self.addr_list.view().index_of(addr) + 1) == self.map().spec_index(ret.1.unwrap()),
    {
        proof {
            self.view().to_set_ensures(); self.wf_implies_view_len_eq_len();
            self.wf_perms_at(addr);
            let index = self.addr_list.view().index_of(addr);
            self.wf_value_list_at(index);
            self.wf_map_at(addr);
            self.view().skip(index).to_set_ensures(); vstd::seq_lib::lemma_seq_skip_index(self.view(), index, 0);
            if index + 1 < self.length {
                self.wf_next_at(index);
                self.wf_perms_at(self.addr_list.view().spec_index(index + 1));
                self.wf_value_list_at(index + 1);
                self.wf_map_at(self.addr_list.view().spec_index(index + 1));
            }
        }
        let tracked perm = self.perms.borrow().tracked_borrow(addr);
        let node = PPtr::<Node<T>>::from_usize(addr).borrow(Tracked(perm));
        assert(self.view().index_of(node.value) == self.addr_list.view().index_of(addr)) by { seq_no_duplicates_implies_index_of_roundtrip::<T>(); };
        (node.value, node.next)
    }
}
}
