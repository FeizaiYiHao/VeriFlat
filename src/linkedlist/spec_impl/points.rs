use super::*;

verus! {
impl<T, const MAJOR: LockMajorId> LinkedList<T, MAJOR> {
    pub proof fn wf_perms_at(&self, addr: usize)
        requires
            self.wf_perms(),
        ensures
            self.dom().contains(addr) == self.addr_list.view().contains(addr),
            self.dom().contains(addr) ==> self.perms.view().spec_index(addr).is_init(),
            self.dom().contains(addr) ==> self.perms.view().spec_index(addr).addr() == addr,
    { reveal(LinkedList::wf_perms); }

    pub proof fn wf_value_list_at(&self, index: int)
        requires
            self.wf_value_list(),
            0 <= index < self.length,
        ensures
            self.view().spec_index(index) == self.perms.view().spec_index(self.addr_list.view().spec_index(index)).value().view(),
    { reveal(LinkedList::wf_value_list); }

    pub proof fn wf_next_at(&self, index: int)
        requires
            self.wf_next(),
            0 <= index < self.length - 1,
        ensures
            self.perms.view().spec_index(self.addr_list.view().spec_index(index)).value().next is Some,
            self.perms.view().spec_index(self.addr_list.view().spec_index(index)).value().next.unwrap() == self.addr_list.view().spec_index(index + 1),
    { reveal(LinkedList::wf_next); }
}
}
