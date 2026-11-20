use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::set_lib::lemma_len_subset;

verus! {
use crate::*;

/// Most PCI functions one process owns.
pub const PCI_FUNCTIONS_PER_PROCESS: usize = 8;

/// One entry of a process's PCI function array: whether it is used, the function it holds, and how many of that
/// function's BAR mappings the process has.
#[derive(Clone, Copy)]
pub struct PciFunctionEntry {
    pub used: bool,
    pub bdf: PciBdf,
    pub count: usize,
}

/// One BAR mapping: its virtual address and its size, 4K or 2M.
pub type PciBarMapping = (VAddr, PageSize);

/// The PCI functions a process owns, held in its page table under the page-table big lock. The ghost map gives each owned
/// function its entry index and the set of its BAR mappings.
pub struct PciFunctionArray {
    entries: Array<PciFunctionEntry, PCI_FUNCTIONS_PER_PROCESS>,
    len: usize,
    owned: Ghost<Map<PciBdf, (int, Set<PciBarMapping>)>>,
}

impl PciFunctionArray {
    /// The entries.
    pub closed spec fn entries_view(&self) -> Seq<PciFunctionEntry> { self.entries.view() }

    /// Each owned function with its entry index and its BAR mappings.
    pub closed spec fn owned_view(&self) -> Map<PciBdf, (int, Set<PciBarMapping>)> { self.owned.view() }

    /// Each owned function with its BAR mappings.
    pub open spec fn view(&self) -> Map<PciBdf, Set<PciBarMapping>> { Map::new(self.owned_view().dom(), |f: PciBdf| self.owned_view()[f].1) }

    /// Each owned function with its number of BAR mappings.
    pub open spec fn mapping_counts(&self) -> Map<PciBdf, nat> { Map::new(self.view().dom(), |f: PciBdf| self.view()[f].len()) }

    /// Entry `i`.
    pub open spec fn spec_entry(&self, i: int) -> PciFunctionEntry { self.entries_view()[i] }

    /// The entry index of the owned function `f`.
    pub open spec fn index_of(&self, f: PciBdf) -> int { self.owned_view()[f].0 }

    /// The entry array has `PCI_FUNCTIONS_PER_PROCESS` entries, and `len` counts the owned functions.
    pub closed spec fn entries_wf(&self) -> bool { self.entries.wf() && self.len as nat == self.owned.view().dom().len() }

    /// Each owned function is a valid B/D/F and sits in the used entry its index names, with its mapping count; each used
    /// entry holds an owned function whose index is that entry.
    #[verifier::opaque]
    pub open spec fn wf(&self) -> bool {
        &&& self.entries_wf()
        &&& forall|f: PciBdf| #![trigger self.view().dom().contains(f)] self.view().dom().contains(f) ==> {
            &&& pci_bdf_valid(f.0, f.1, f.2)
            &&& 0 <= self.index_of(f) < PCI_FUNCTIONS_PER_PROCESS
            &&& self.spec_entry(self.index_of(f)).used
            &&& self.spec_entry(self.index_of(f)).bdf == f
            &&& self.spec_entry(self.index_of(f)).count as nat == self.view()[f].len()
        }
        &&& forall|i: int| #![trigger self.entries_view()[i]] 0 <= i < PCI_FUNCTIONS_PER_PROCESS && self.spec_entry(i).used ==> {
            &&& self.view().dom().contains(self.spec_entry(i).bdf)
            &&& self.index_of(self.spec_entry(i).bdf) == i
        }
    }

    /// `wf` at the owned function `f`: a valid B/D/F in the used entry its index names, with its mapping count.
    pub broadcast proof fn wf_function_at(&self, f: PciBdf)
        requires
            self.wf(),
            #[trigger] self.view().dom().contains(f),
        ensures
            pci_bdf_valid(f.0, f.1, f.2),
            0 <= self.index_of(f) < PCI_FUNCTIONS_PER_PROCESS,
            self.spec_entry(self.index_of(f)).used,
            self.spec_entry(self.index_of(f)).bdf == f,
            self.spec_entry(self.index_of(f)).count as nat == self.view()[f].len(),
    { reveal(PciFunctionArray::wf); }

    /// `wf` at the used entry `i`: it holds an owned function whose index is `i`.
    pub broadcast proof fn wf_entry_at(&self, i: int)
        requires
            self.wf(),
            0 <= i < PCI_FUNCTIONS_PER_PROCESS,
            #[trigger] self.spec_entry(i).used,
        ensures
            self.view().dom().contains(self.spec_entry(i).bdf),
            self.index_of(self.spec_entry(i).bdf) == i,
    { reveal(PciFunctionArray::wf); }

    /// An array that owns no function.
    pub fn new_empty() -> (ret: Self)
        ensures
            ret.wf(),
            ret.view() == Map::<PciBdf, Set<PciBarMapping>>::empty(),
    {
        proof { reveal(PciFunctionArray::wf); }
        let ret = Self { entries: Array::new_with_init_value(PciFunctionEntry { used: false, bdf: (0, 0, 0), count: 0 }), len: 0, owned: Ghost(Map::empty()) };
        assert(ret.owned.view().dom().len() == 0) by { broadcast use vstd::set::lemma_set_empty_len; };
        ret
    }

    /// Entry `i`.
    pub fn entry(&self, i: usize) -> (ret: PciFunctionEntry)
        requires
            self.wf(),
            i < PCI_FUNCTIONS_PER_PROCESS,
        ensures
            ret == self.spec_entry(i as int),
    {
        proof { reveal(PciFunctionArray::wf); }
        *self.entries.get(i)
    }

    /// The number of BAR mappings of the function in the used entry `i`.
    pub fn count(&self, i: usize) -> (ret: usize)
        requires
            self.wf(),
            i < PCI_FUNCTIONS_PER_PROCESS,
            self.spec_entry(i as int).used,
        ensures
            ret == self.spec_entry(i as int).count,
            ret as nat == self.view()[self.spec_entry(i as int).bdf].len(),
    {
        proof { self.wf_entry_at(i as int); self.wf_function_at(self.spec_entry(i as int).bdf); }
        self.entries.get(i).count
    }

    /// The entry of `(bus, device, function)`, if the array owns it.
    pub fn find(&self, bus: usize, device: usize, function: usize) -> (ret: Option<usize>)
        requires
            self.wf(),
        ensures
            (ret is Some) == self.view().dom().contains((bus, device, function)),
            ret matches Some(i) ==> i < PCI_FUNCTIONS_PER_PROCESS && i as int == self.index_of((bus, device, function)),
    {
        let mut i: usize = 0;
        while i < PCI_FUNCTIONS_PER_PROCESS
            invariant
                self.wf(),
                i <= PCI_FUNCTIONS_PER_PROCESS,
                forall|j: int| #![trigger self.entries_view()[j]] 0 <= j < i ==> !(self.spec_entry(j).used && self.spec_entry(j).bdf == (bus, device, function)),
            decreases PCI_FUNCTIONS_PER_PROCESS - i,
        {
            let e = self.entry(i);
            if e.used && e.bdf.0 == bus && e.bdf.1 == device && e.bdf.2 == function {
                proof { self.wf_entry_at(i as int); }
                return Some(i);
            }
            i = i + 1;
        }
        proof { if self.view().dom().contains((bus, device, function)) { self.wf_function_at((bus, device, function)); } }
        None
    }

    /// Whether the array owns no function.
    pub fn is_empty(&self) -> (ret: bool)
        requires
            self.wf(),
        ensures
            ret == (self.view().dom() == Set::<PciBdf>::empty()),
    {
        let ret = self.len == 0;
        assert(ret == (self.view().dom() == Set::<PciBdf>::empty())) by {
            reveal(PciFunctionArray::wf);
            broadcast use vstd::set_lib::lemma_set_empty_equivalency_len;
        };
        ret
    }

    /// An unused entry, if any; there is none exactly when the array owns `PCI_FUNCTIONS_PER_PROCESS` functions.
    pub fn free_entry(&self) -> (ret: Option<usize>)
        requires
            self.wf(),
        ensures
            ret matches Some(i) ==> i < PCI_FUNCTIONS_PER_PROCESS && !self.spec_entry(i as int).used,
            (ret is None) == (self.view().dom().len() >= PCI_FUNCTIONS_PER_PROCESS),
    {
        proof { reveal(PciFunctionArray::wf); }
        if self.len >= PCI_FUNCTIONS_PER_PROCESS { return None; }
        let mut i: usize = 0;
        while i < PCI_FUNCTIONS_PER_PROCESS
            invariant
                self.wf(),
                self.view().dom() == self.owned.view().dom(),
                self.view().dom().len() < PCI_FUNCTIONS_PER_PROCESS,
                i <= PCI_FUNCTIONS_PER_PROCESS,
                forall|j: int| #![trigger self.entries_view()[j]] 0 <= j < i ==> self.spec_entry(j).used,
            decreases PCI_FUNCTIONS_PER_PROCESS - i,
        {
            if !self.entry(i).used { return Some(i); }
            i = i + 1;
        }
        proof {
            reveal(PciFunctionArray::wf);
            let dom = self.owned.view().dom();
            let bdfs = Seq::new(PCI_FUNCTIONS_PER_PROCESS as nat, |j: int| self.spec_entry(j).bdf);
            bdfs.unique_seq_to_set();
            bdfs.to_set_ensures();
            lemma_len_subset(bdfs.to_set(), dom);
        }
        None
    }

    /// The unused entry `i` takes `(bus, device, function)` with no BAR mapping.
    pub fn insert(&mut self, i: usize, bus: usize, device: usize, function: usize)
        requires
            old(self).wf(),
            i < PCI_FUNCTIONS_PER_PROCESS,
            pci_bdf_valid(bus, device, function),
            !old(self).spec_entry(i as int).used,
            !old(self).view().dom().contains((bus, device, function)),
            old(self).view().dom().len() < PCI_FUNCTIONS_PER_PROCESS,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().insert((bus, device, function), Set::<PciBarMapping>::empty()),
            final(self).spec_entry(i as int) == (PciFunctionEntry { used: true, bdf: (bus, device, function), count: 0 }),
            final(self).index_of((bus, device, function)) == i,
            forall|j: int| #![trigger final(self).spec_entry(j)] j != i ==> final(self).spec_entry(j) == old(self).spec_entry(j),
            forall|f: PciBdf| #![trigger final(self).index_of(f)] old(self).view().dom().contains(f) ==> final(self).index_of(f) == old(self).index_of(f),
    {
        proof { reveal(PciFunctionArray::wf); }
        let f = (bus, device, function);
        self.entries.set(i, PciFunctionEntry { used: true, bdf: f, count: 0 });
        self.len = self.len + 1;
        self.owned = Ghost(self.owned.view().insert(f, (i as int, Set::<PciBarMapping>::empty())));
        proof { broadcast use vstd::set::lemma_set_insert_len, vstd::set::lemma_set_empty_len; }
    }

    /// The function of the used entry `i` gains the BAR mapping `m`; its count grows by one.
    pub fn add_mapping(&mut self, i: usize, Ghost(m): Ghost<PciBarMapping>)
        requires
            old(self).wf(),
            i < PCI_FUNCTIONS_PER_PROCESS,
            old(self).spec_entry(i as int).used,
            !old(self).view()[old(self).spec_entry(i as int).bdf].contains(m),
            old(self).view()[old(self).spec_entry(i as int).bdf].len() < usize::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().insert(old(self).spec_entry(i as int).bdf, old(self).view()[old(self).spec_entry(i as int).bdf].insert(m)),
            final(self).view().dom() == old(self).view().dom(),
            final(self).mapping_counts()
                == old(self).mapping_counts().insert(old(self).spec_entry(i as int).bdf, (old(self).mapping_counts()[old(self).spec_entry(i as int).bdf] + 1) as nat),
            final(self).spec_entry(i as int) == (PciFunctionEntry { count: (old(self).spec_entry(i as int).count + 1) as usize, ..old(self).spec_entry(i as int) }),
            forall|j: int| #![trigger final(self).spec_entry(j)] j != i ==> final(self).spec_entry(j) == old(self).spec_entry(j),
            forall|f: PciBdf| #![trigger final(self).index_of(f)] final(self).index_of(f) == old(self).index_of(f),
    {
        proof { reveal(PciFunctionArray::wf); }
        let e = *self.entries.get(i);
        let ghost f = e.bdf;
        proof { broadcast use vstd::set::lemma_set_insert_len; }
        self.entries.set(i, PciFunctionEntry { count: e.count + 1, ..e });
        self.owned = Ghost(self.owned.view().insert(f, (i as int, self.owned.view()[f].1.insert(m))));
    }

    /// The function of the used entry `i` loses its BAR mapping `m`; its count drops by one.
    pub fn remove_mapping(&mut self, i: usize, Ghost(m): Ghost<PciBarMapping>)
        requires
            old(self).wf(),
            i < PCI_FUNCTIONS_PER_PROCESS,
            old(self).spec_entry(i as int).used,
            old(self).view()[old(self).spec_entry(i as int).bdf].contains(m),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().insert(old(self).spec_entry(i as int).bdf, old(self).view()[old(self).spec_entry(i as int).bdf].remove(m)),
            final(self).view().dom() == old(self).view().dom(),
            final(self).mapping_counts()
                == old(self).mapping_counts().insert(old(self).spec_entry(i as int).bdf, (old(self).mapping_counts()[old(self).spec_entry(i as int).bdf] - 1) as nat),
            final(self).spec_entry(i as int) == (PciFunctionEntry { count: (old(self).spec_entry(i as int).count - 1) as usize, ..old(self).spec_entry(i as int) }),
            forall|j: int| #![trigger final(self).spec_entry(j)] j != i ==> final(self).spec_entry(j) == old(self).spec_entry(j),
            forall|f: PciBdf| #![trigger final(self).index_of(f)] final(self).index_of(f) == old(self).index_of(f),
    {
        proof { reveal(PciFunctionArray::wf); }
        let e = *self.entries.get(i);
        let ghost f = e.bdf;
        proof { broadcast use vstd::set::lemma_set_remove_len, vstd::set::lemma_set_contains_len; }
        self.entries.set(i, PciFunctionEntry { count: e.count - 1, ..e });
        self.owned = Ghost(self.owned.view().insert(f, (i as int, self.owned.view()[f].1.remove(m))));
    }

    /// The used entry `i` becomes unused; its function and that function's BAR mappings leave the array.
    pub fn remove(&mut self, i: usize)
        requires
            old(self).wf(),
            i < PCI_FUNCTIONS_PER_PROCESS,
            old(self).spec_entry(i as int).used,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view().remove(old(self).spec_entry(i as int).bdf),
            !final(self).spec_entry(i as int).used,
            forall|j: int| #![trigger final(self).spec_entry(j)] j != i ==> final(self).spec_entry(j) == old(self).spec_entry(j),
            forall|f: PciBdf| #![trigger final(self).index_of(f)] final(self).view().dom().contains(f) ==> final(self).index_of(f) == old(self).index_of(f),
    {
        proof { reveal(PciFunctionArray::wf); }
        let f = self.entry(i).bdf;
        self.entries.set(i, PciFunctionEntry { used: false, bdf: f, count: 0 });
        proof { broadcast use vstd::set::lemma_set_remove_len, vstd::set::lemma_set_contains_len; }
        self.len = self.len - 1;
        self.owned = Ghost(self.owned.view().remove(f));
    }
}
} // verus!
