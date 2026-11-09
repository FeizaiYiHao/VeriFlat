#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;

verus! {
/// A complete candidate retains just the source list for each of its 512 pages.
pub struct Merge2mCandidate {
    pub head: PageIndex,
    pub sources: ArrayVec<u8, 512>,
}

impl Merge2mCandidate {
    pub open spec fn wf(&self) -> bool {
        &&& self.sources.wf()
        &&& self.sources.len() <= 512
        &&& self.sources.len() > 0 ==> page_index_2m_valid(self.head)
        &&& forall|i: int| #![trigger self.sources.view().spec_index(i)] 0 <= i < self.sources.len() ==> self.sources.view().spec_index(i) as usize <= NUM_CPUS
    }

    pub fn new() -> (ret: Self)
        ensures
            ret.wf(),
            ret.sources.len() == 0,
    {
        Merge2mCandidate { head: 0, sources: ArrayVec::new_with_init_value(0u8) }
    }

    /// Feeds the next page of the ascending merge; a gap discards the incomplete prefix, and only an aligned page can begin the next candidate.
    pub fn feed(&mut self, page: PageIndex, source: usize) -> (complete: bool)
        requires
            old(self).wf(),
            old(self).sources.len() < 512,
            index_valid(NUM_PAGES, page),
            source <= NUM_CPUS,
            NUM_CPUS <= u8::MAX as usize,
        ensures
            final(self).wf(),
            complete == (final(self).sources.len() == 512),
            final(self).sources.len() > 0 ==> page == final(self).head + final(self).sources.len() - 1,
            final(self).sources.len() > 0 ==> final(self).sources.view().last() == source as u8,
            page % 512 == 0 ==> final(self).head == page && final(self).sources.view() == seq![source as u8],
            page % 512 != 0 && old(self).sources.len() > 0 && page == old(self).head + old(self).sources.len() ==> {
                &&& final(self).head == old(self).head
                &&& final(self).sources.view() == old(self).sources.view().push(source as u8)
            },
            page % 512 != 0 && !(old(self).sources.len() > 0 && page == old(self).head + old(self).sources.len()) ==> final(self).sources.len() == 0,
    {
        if page % 512 == 0 {
            self.head = page;
            self.sources.clear();
            self.sources.push(source as u8);
        } else if self.sources.len > 0 && page == self.head + self.sources.len {
            self.sources.push(source as u8);
        } else {
            self.sources.clear();
        }
        self.sources.len == 512
    }

    pub fn clear(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).sources.len() == 0,
            final(self).head == old(self).head,
    {
        self.sources.clear();
    }
}
}
