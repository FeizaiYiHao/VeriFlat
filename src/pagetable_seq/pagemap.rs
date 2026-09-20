use vstd::prelude::*;
verus! {
use crate::*;
use super::entry::*;

/// Concrete page-table page.
///
/// Verus requires these representation fields to remain public because public
/// open specs mention them; making even one field private makes the whole type
/// opaque in public contracts. Public field visibility is therefore proof-model
/// visibility, not mutation authorization. Executable code must treat
/// `page_map_set_published` as the only writer after publication. Enforcing that
/// rule as Rust privacy/typestate requires a future opaque-view refactor.
pub struct PageMap {
    pub ar: Array<usize, 512>,
    pub spec_seq: Ghost<Seq<PageEntry>>,  // pub level: Ghost<usize>,
    // not used for now.
}

impl PageMap {
    pub open spec fn wf(&self) -> bool {
        &&& self.ar.wf()
        &&& self.spec_seq.view().len() == 512
        &&& forall|i: usize|
            #![trigger usize2page_entry(self.ar.view().spec_index(i as int))]
            pei_valid(i)
            ==>
            (usize2page_entry(self.ar.view().spec_index(i as int))
                =~= self.spec_seq.view().spec_index(i as int))
        &&&
        forall|i: usize|
            #![trigger self.spec_seq.view().spec_index(i as int).perm.kernel_present]
            pei_valid(i) && self.spec_seq.view().spec_index(i as int).perm.kernel_present
            ==> mem_valid(self.spec_seq.view().spec_index(i as int).addr)

    }

    pub open spec fn view(&self) -> Seq<PageEntry> {
        self.spec_seq.view()
    }

    pub open spec fn spec_index(&self, index: usize) -> PageEntry
        recommends
            pei_valid(index),
    {
        self.view().spec_index(index as int)
    }

    pub open spec fn is_empty(&self) -> bool
        recommends
            self.wf(),
    {
        forall|x: u16| #![auto] pei_valid(x as usize) ==> self.spec_seq.view().spec_index(x as int).perm.present == false
    }

    pub(super) fn set_unpublished(&mut self, index: usize, value: PageEntry)
        requires
            old(self).wf(),
            pei_valid(index),
            value.perm.present ==> value.perm.kernel_present,
            value.perm.kernel_present ==> mem_valid(value.addr),
            value.perm.kernel_present == false ==> value.is_empty(),
        ensures
            final(self).wf(),
            final(self).view() =~= old(self).view().update(index as int, value),
    {
        if value.perm.kernel_present == false {
            self.ar.set(index, 0usize);
            proof {
                zero_leads_is_empty_page_entry();
                self.spec_seq = Ghost(self.spec_seq.view().update(index as int, usize2page_entry(0usize)));
            }
            return;
        } else {
            let u = page_entry2usize(&value);
            self.ar.set(index, u);

            proof {
                self.spec_seq = Ghost(self.spec_seq.view().update(index as int, value));
            }

            return ;
        }
    }

    /// Internal exact writer used by the PointsTo-level offline/published gates.
    /// For an already-published page, callers must go through
    /// `page_map_set_published`, which carries the LocalContext phase contract;
    /// offline construction instead goes through `set_unpublished`.
    pub(super) fn set_internal(&mut self, index: usize, value: PageEntry)
        requires
            old(self).wf(),
            pei_valid(index),
            mem_valid(value.addr),
        ensures
            final(self).wf(),
            final(self).view() =~= old(self).view().update(index as int, value),
    {
        let u = page_entry2usize(&value);
        self.ar.set(index, u);
        proof {
            self.spec_seq = Ghost(self.spec_seq.view().update(index as int, value));
        }
    }

    pub fn index(&self, index: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            pei_valid(index),
        ensures
            ret =~= self.spec_index(index),
    {
        return usize2page_entry(*self.ar.get(index));
    }

    pub fn get(&self, index: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            pei_valid(index),
        ensures
            ret =~= self.spec_index(index),
    {
        return self.index(index);
    }
}

} // verus!
