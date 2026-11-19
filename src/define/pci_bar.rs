use vstd::prelude::*;
use crate::*;

verus! {
/// One memory BAR of one PCI function: the function's bus/device/function, the BAR index (0 to 5; a 64-bit BAR is keyed
/// by its low register), and the BAR's exact byte range `[base, base + size)`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct PciBarEntry {
    pub bdf: PciBdf,
    pub bar: usize,
    pub base: PAddr,
    pub size: usize,
}

impl PciBarEntry {
    /// A valid PCI function, a BAR index below 6, and a nonempty byte range ending at or below `MEM_4K_MASK + 4K`.
    pub open spec fn wf(&self) -> bool {
        &&& pci_bdf_valid(self.bdf.0, self.bdf.1, self.bdf.2)
        &&& self.bar < 6
        &&& self.size > 0
        &&& self.base as int + self.size as int <= MEM_4K_MASK as int + PAGE_SZ_4K as int
    }

    /// The 4K page base `p` lies in the BAR's outward-rounded page envelope: from the 4K page holding `base` up to the
    /// range's end.
    pub open spec fn envelope_contains(&self, p: PAddr) -> bool {
        &&& p % PAGE_SZ_4K == 0
        &&& self.base as int / PAGE_SZ_4K as int * PAGE_SZ_4K as int <= p as int
        &&& (p as int) < self.base as int + self.size as int
    }

    /// The `page_index`-th 4K page of the BAR's page envelope, counted from the 4K page holding `base`, if the envelope
    /// reaches it.
    pub open spec fn spec_page_4k(&self, page_index: usize) -> Option<PAddr> {
        let p = self.base as int / PAGE_SZ_4K as int * PAGE_SZ_4K as int + page_index as int * PAGE_SZ_4K as int;
        if p < self.base as int + self.size as int { Some(p as PAddr) } else { None }
    }

    /// The `index`-th 2M chunk lying wholly in the BAR's byte range, counted from the first 2M-aligned address at or above
    /// `base`, if the range holds it.
    pub open spec fn spec_chunk_2m(&self, index: usize) -> Option<PAddr> {
        let p = (self.base as int + PAGE_SZ_2M as int - 1) / PAGE_SZ_2M as int * PAGE_SZ_2M as int + index as int * PAGE_SZ_2M as int;
        if p + PAGE_SZ_2M as int <= self.base as int + self.size as int { Some(p as PAddr) } else { None }
    }
}

pub const PCI_BAR_TABLE_CAPACITY: usize = 1024;

/// The memory BARs of every PCI function, filled once at boot and read-only afterwards. Sealed: verified code reads them
/// through `view` and can neither build nor change one.
pub struct PciBarTable {
    entries: Array<PciBarEntry, PCI_BAR_TABLE_CAPACITY>,
    len: usize,
}

impl PciBarTable {
    /// The used length fits the storage.
    #[verifier::type_invariant]
    closed spec fn len_wf(&self) -> bool { self.len <= PCI_BAR_TABLE_CAPACITY }

    /// The table's entries: the first `len` of its storage.
    pub closed spec fn view(&self) -> Seq<PciBarEntry> { self.entries.view().take(self.len as int) }

    /// Callable only from the unverified boot glue; `requires false` keeps verified code out.
    pub fn new(entries: Array<PciBarEntry, PCI_BAR_TABLE_CAPACITY>, len: usize) -> (ret: Self)
        requires false,
        ensures ret.view() == entries.view().take(len as int),
    {
        Self { entries, len }
    }

    /// The number of entries.
    pub fn len(&self) -> (ret: usize)
        ensures ret as int == self.view().len(),
    {
        proof { use_type_invariant(self); }
        self.len
    }

    /// Entry `i`.
    pub fn get(&self, i: usize) -> (ret: PciBarEntry)
        requires i < self.view().len(),
        ensures ret == self.view()[i as int],
    {
        proof { use_type_invariant(self); }
        *self.entries.get(i)
    }

    /// The PCI function whose BAR envelope contains the 4K page base `p`, if any: the first entry whose envelope contains it.
    pub fn function_of_page(&self, p: PAddr) -> (ret: Option<PciBdf>)
        requires pci_bar_table_wf(self.view()),
        ensures ret == pci_bar_function_of_page(self.view(), p),
    {
        proof { assert(PAGE_SZ_4K == 4096) by (compute); }
        let len = self.len();
        let mut i: usize = 0;
        while i < len
            invariant
                pci_bar_table_wf(self.view()),
                len as int == self.view().len(),
                i <= len,
                forall|j: int| #![trigger self.view()[j]] 0 <= j < i ==> !self.view()[j].envelope_contains(p),
                PAGE_SZ_4K == 4096,
            decreases len - i,
        {
            let e = self.get(i);
            proof { pci_bar_table_wf_at(self.view(), i as int, i as int, p); assert(MEM_4K_MASK == 0x0000_ffff_ffff_f000) by (compute); }
            if p % PAGE_SZ_4K == 0 && e.base / PAGE_SZ_4K * PAGE_SZ_4K <= p && p < e.base + e.size {
                proof {
                    let b = self.view();
                    let k = pci_bar_entry_of_page(b, p)->0;
                    assert(b[i as int].envelope_contains(p) && pci_bar_entry_of_page(b, p) is Some && b[k].bdf == e.bdf) by { pci_bar_table_wf_at(b, i as int, pci_bar_entry_of_page(b, p)->0, p); };
                }
                return Some(e.bdf);
            }
            i = i + 1;
        }
        None
    }

    /// The `page_index`-th 4K page of entry `i`'s page envelope; its function is entry `i`'s and it is a valid 4K IO target.
    pub fn page_4k(&self, i: usize, page_index: usize) -> (ret: Option<PAddr>)
        requires
            pci_bar_table_wf(self.view()),
            i < self.view().len(),
        ensures
            ret == self.view()[i as int].spec_page_4k(page_index),
            ret matches Some(p) ==> pci_bar_function_of_page(self.view(), p) == Some(self.view()[i as int].bdf) && io_page_range_valid(p, PAGE_SZ_4K),
    {
        let e = self.get(i);
        proof { pci_bar_table_wf_at(self.view(), i as int, i as int, 0); assert(PAGE_SZ_4K == 4096 && MEM_4K_MASK == 0x0000_ffff_ffff_f000) by (compute); }
        let start = e.base / PAGE_SZ_4K * PAGE_SZ_4K;
        let end = e.base + e.size;
        assert(start <= e.base) by (nonlinear_arith) requires start == e.base / 4096 * 4096;
        if page_index > (end - start) / PAGE_SZ_4K { return None; }
        assert(page_index * 4096 <= end - start) by (nonlinear_arith) requires page_index <= (end - start) / 4096, start <= end;
        let p = start + page_index * PAGE_SZ_4K;
        if p >= end { return None; }
        proof {
            let b = self.view();
            assert(p % 4096 == 0) by (nonlinear_arith) requires p == e.base / 4096 * 4096 + page_index * 4096;
            assert(b[i as int].envelope_contains(p));
            assert(pci_bar_entry_of_page(b, p) is Some && b[pci_bar_entry_of_page(b, p)->0].bdf == e.bdf) by { pci_bar_table_wf_at(b, i as int, pci_bar_entry_of_page(b, p)->0, p); };
            assert(io_page_range_valid(p, PAGE_SZ_4K)) by {
                reveal(io_page_range_valid);
                assert(p & (!MEM_MASK) as usize == 0) by (bit_vector) requires p % 4096 == 0, p < 0x0001_0000_0000_0000usize;
            };
        }
        Some(p)
    }

    /// The `index`-th 2M chunk lying wholly in entry `i`'s byte range; it is a 2M chunk of entry `i`'s function and a valid 2M IO
    /// target.
    pub fn chunk_2m(&self, i: usize, index: usize) -> (ret: Option<PAddr>)
        requires
            pci_bar_table_wf(self.view()),
            i < self.view().len(),
        ensures
            ret == self.view()[i as int].spec_chunk_2m(index),
            ret matches Some(p) ==> pci_bar_2m_chunk_of(self.view(), p, self.view()[i as int].bdf) && io_page_range_valid(p, PAGE_SZ_2M),
    {
        let e = self.get(i);
        proof { pci_bar_table_wf_at(self.view(), i as int, i as int, 0); assert(PAGE_SZ_4K == 4096 && PAGE_SZ_2M == 0x200000 && MEM_4K_MASK == 0x0000_ffff_ffff_f000) by (compute); }
        let end = e.base + e.size;
        let start = (e.base + (PAGE_SZ_2M - 1)) / PAGE_SZ_2M * PAGE_SZ_2M;
        assert(e.base <= start && start < e.base + 0x200000) by (nonlinear_arith) requires start == (e.base + 0x1fffff) / 0x200000 * 0x200000;
        if start >= end || index > (end - start) / PAGE_SZ_2M { return None; }
        assert(index * 0x200000 <= end - start) by (nonlinear_arith) requires index <= (end - start) / 0x200000, start <= end;
        let p = start + index * PAGE_SZ_2M;
        if p > end || end - p < PAGE_SZ_2M { return None; }
        proof {
            let b = self.view();
            assert(p % 0x200000 == 0 && p % 4096 == 0) by (nonlinear_arith) requires p == (e.base + 0x1fffff) / 0x200000 * 0x200000 + index * 0x200000;
            assert(e.base / 4096 * 4096 <= p) by (nonlinear_arith) requires e.base <= p;
            assert(b[i as int].envelope_contains(p));
            let k = pci_bar_entry_of_page(b, p)->0;
            assert(pci_bar_entry_of_page(b, p) is Some && k == i) by {
                pci_bar_table_wf_at(b, i as int, k, p);
                pci_bar_table_wf_at(b, k, i as int, p);
                assert(b[k].base / 4096 * 4096 <= p ==> b[k].base < p + 4096) by (nonlinear_arith);
            };
            assert(io_page_range_valid(p, PAGE_SZ_2M)) by {
                reveal(io_page_range_valid);
                assert(p & (!MEM_MASK) as usize == 0) by (bit_vector) requires p % 0x200000 == 0, p < 0x0001_0000_0000_0000usize;
            };
        }
        Some(p)
    }
}
}
