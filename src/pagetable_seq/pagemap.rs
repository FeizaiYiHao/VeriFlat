use vstd::prelude::*;
verus! {
use crate::primitive::array::*;
use crate::util::page_ptr_util_u::*;
use super::entry::*;

pub struct PageMap {
    pub ar: Array<usize, 512>,
    pub spec_seq: Ghost<Seq<PageEntry>>,  // pub level: Ghost<usize>,
    // not used for now.
}

impl PageMap {
    pub fn init(&mut self)
        requires
            old(self).ar.wf(),
            old(self).spec_seq.view().len() == 512,
        ensures
            final(self).wf(),
            forall|i: int| #![trigger final(self).view().spec_index(i).is_empty()] 0 <= i < 512 ==> final(self).view().spec_index(i).is_empty(),
    {
        for i in 0..512
            invariant
                0 <= i <= 512,
                self.ar.wf(),
                self.spec_seq.view().len() == 512,
                forall|j: int|
                    #![trigger usize2page_entry(self.ar.view().spec_index(j))]
                    0 <= j < i ==> (usize2page_entry(self.ar.view().spec_index(j)) =~= self.spec_seq.view().spec_index(j)),
                forall|j: int|
                    #![trigger self.ar.view().spec_index(j)]
                    0 <= j < i ==> (usize2page_entry(self.ar.view().spec_index(j)).is_empty() <==> self.ar.view().spec_index(j) == 0),
                forall|j: int|
                    #![trigger self.ar.view().spec_index(j)]
                    0 <= j < i ==> usize2page_entry(self.ar.view().spec_index(j)).is_empty(),
                forall|j: int| #![trigger self.view().spec_index(j).is_empty()] 0 <= j < i ==> self.view().spec_index(j).is_empty(),
                forall|j: int| #![trigger self.spec_seq.view().spec_index(j)] 0 <= j < i ==> self.spec_seq.view().spec_index(j).perm.kernel_present == false,
        {
            let ghost_view = Ghost(self.view());
            self.ar.set(i, 0usize);
            assert(self.view() == ghost_view);
            proof {
                zero_leads_is_empty_page_entry();
                assert(usize2page_entry(0usize).is_empty());
                self.spec_seq = Ghost(self.spec_seq.view().update(i as int, usize2page_entry(0usize)));
            }
        }
        assert(forall|j: int| #![trigger self.view().spec_index(j)] 0 <= j < 512 ==> self.spec_seq.view().spec_index(j).perm.kernel_present == false);
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.ar.wf()
        &&& self.spec_seq.view().len() == 512
        &&& forall|i: int|
            #![trigger usize2page_entry(self.ar.view().spec_index(i))]
            0 <= i < 512 
            ==> 
            (usize2page_entry(self.ar.view().spec_index(i)) =~= self.spec_seq.view().spec_index(i))
        &&&
        forall|i:int|
            #![trigger self.spec_seq.view().spec_index(i).addr]
            0<=i<512 && self.spec_seq.view().spec_index(i).perm.kernel_present
            ==> mem_valid(self.spec_seq.view().spec_index(i).addr)

    }

    pub open spec fn view(&self) -> Seq<PageEntry> {
        self.spec_seq.view()
    }

    pub open spec fn spec_index(&self, index: usize) -> PageEntry
        recommends
            0 <= index < 512,
    {
        self.view().spec_index(index as int)
    }

    pub open spec fn is_empty(&self) -> bool
        recommends
            self.wf(),
    {
        forall|x: u16| #![auto] 0 <= x < 512 ==> self.spec_seq.view().spec_index(x as int).perm.present == false
    }

    pub fn set(&mut self, index: usize, value: PageEntry)
        requires
            old(self).wf(),
            0 <= index < 512,
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

            assert(usize2present(u) == value.perm.present);
            assert(usize2kernel_present(u) == true);
            assert(u != 0) by (bit_vector)
                requires
                    (u & 0x1usize << 52u64 as usize) != 0 == true,
            ;

            proof {
                self.spec_seq = Ghost(self.spec_seq.view().update(index as int, value));
            }

            return ;
        }
    }

    /// Same as `set` but with weaker preconditions: only requires that `value.addr` is a
    /// valid physical address (so the bit-encoding round-trips). Always stores `value`
    /// exactly, including when `value.perm.kernel_present == false` and the entry has
    /// non-zero data — useful for callers that pass user-only mappings or partial entries.
    pub fn set_unsanitized(&mut self, index: usize, value: PageEntry)
        requires
            old(self).wf(),
            0 <= index < 512,
            mem_valid(value.addr),
        ensures
            final(self).wf(),
            final(self).view() =~= old(self).view().update(index as int, value),
    {
        let u = page_entry2usize(&value);
        self.ar.set(index, u);
        proof {
            // page_entry2usize ensures bits round-trip. Hence usize2page_entry(u) =~= value.
            assert(usize2page_entry_perm(u) =~= value.perm);
            assert(usize2pa(u) == value.addr);
            assert(usize2page_entry(u) =~= value);
            self.spec_seq = Ghost(self.spec_seq.view().update(index as int, value));
        }
    }

    pub fn index(&self, index: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            0 <= index < 512,
        ensures
            ret =~= self.spec_index(index),
    {
        return usize2page_entry(*self.ar.get(index));
    }

    pub fn get(&self, index: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            0 <= index < 512,
        ensures
            ret =~= self.spec_index(index),
    {
        return self.index(index);
    }
}

} // verus!
