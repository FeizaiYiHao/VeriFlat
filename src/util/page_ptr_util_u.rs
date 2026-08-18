use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::lemma::lemma_t::*;
use crate::locks::index_valid;

/// Page Entry Index valid
pub open spec fn pei_valid(index: usize) -> bool {
    0 <= index < 512
}

pub open spec fn spec_page_index_merge_2m_valid(i: usize, j: usize) -> bool
    recommends
        page_index_2m_valid(i),
{
    i < j < i + 0x200
}

pub open spec fn spec_page_index_merge_1g_valid(i: usize, j: usize) -> bool
    recommends
        page_index_1g_valid(i),
{
    i < j < i + 0x40000
}

pub open spec fn spec_page_ptr2page_index(ptr: usize) -> usize
    recommends
        page_ptr_valid(ptr),
{
    (ptr / 4096usize) as usize
}

pub open spec fn spec_page_index2page_ptr(i: usize) -> usize
    recommends
        index_valid(NUM_PAGES, i),
{
    (i * 4096) as usize
}

#[verifier(when_used_as_spec(spec_page_ptr2page_index))]
pub fn page_ptr2page_index(ptr: usize) -> (ret: usize)
    requires
        ptr % 0x1000 == 0,
    ensures
        ret == spec_page_ptr2page_index(ptr),
{
    return ptr / 4096usize;
}

#[verifier(when_used_as_spec(spec_page_index2page_ptr))]
pub fn page_index2page_ptr(i: usize) -> (ret: usize)
    requires
        index_valid(NUM_PAGES, i),
    ensures
        ret == spec_page_index2page_ptr(i),
{
    proof {
        lemma_usize_u64(MAX_USIZE);
    }
    i * 4096usize
}

pub open spec fn page_index_2m_valid(i: usize) -> bool {
    &&& i % 512 == 0
    &&& index_valid(NUM_PAGES, i)
}

pub open spec fn page_index_1g_valid(i: usize) -> bool {
    &&& i % 262144 == 0
    &&& index_valid(NUM_PAGES, i)
}

pub open spec fn mem_valid(v: PAddr) -> bool {
    v & (!MEM_MASK) as usize == 0
}

pub open spec fn page_ptr_valid(ptr: usize) -> bool {
    &&& ptr % 0x1000 == 0
    &&& ptr / 0x1000 < NUM_PAGES
}

pub open spec fn spec_page_index_truncate_2m(index: usize) -> usize {
    (index / 512usize * 512usize) as usize
}

pub open spec fn spec_page_index_truncate_1g(index: usize) -> usize {
    (index / 512usize / 512usize * 512usize * 512usize) as usize
}

pub open spec fn page_ptr_2m_valid(ptr: usize) -> bool {
    ((ptr % (0x200000)) == 0) && ((ptr / 4096) < NUM_PAGES)
}

pub open spec fn page_ptr_1g_valid(ptr: usize) -> bool {
    ((ptr % (0x40000000)) == 0) && ((ptr / 4096) < NUM_PAGES)
}

#[verifier(when_used_as_spec(spec_va_4k_valid))]
pub fn va_4k_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_4k_valid(va),
{
    (va & (!MEM_4K_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_4k_range_valid(va: usize, len: usize) -> bool {
    forall|i: usize|
        #![trigger spec_va_add_range(va, i)]
        0 <= i < len ==> spec_va_4k_valid(spec_va_add_range(va, i))
}

#[verifier(when_used_as_spec(spec_va_4k_range_valid))]
pub fn va_4k_range_valid(va: usize, len: usize) -> (ret: bool)
    requires
        va_4k_valid(va),
    ensures
        spec_va_4k_range_valid(va, len) == ret,
{
    for idx in iter: 0..len
        invariant
            va_4k_valid(va),
            forall|i: usize|
                #![trigger spec_va_add_range(va, i)]
                0 <= i < idx ==> spec_va_4k_valid(spec_va_add_range(va, i)),
    {
        if va_4k_valid(va_add_range(va, idx)) == false {
            return false;
        }
    }
    true
}

pub open spec fn spec_va_4k_valid(va: usize) -> bool {
    (va & (!MEM_4K_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier(when_used_as_spec(spec_va_2m_valid))]
pub fn va_2m_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_2m_valid(va),
{
    (va & (!MEM_2M_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_2m_valid(va: usize) -> bool {
    (va & (!MEM_2M_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

#[verifier(when_used_as_spec(spec_va_1g_valid))]
pub fn va_1g_valid(va: usize) -> (ret: bool)
    ensures
        ret == spec_va_1g_valid(va),
{
    (va & (!MEM_1G_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_va_1g_valid(va: usize) -> bool {
    (va & (!MEM_1G_MASK) as usize == 0) && (va as u64 >> 39u64 & 0x1ffu64)
        >= KERNEL_MEM_END_L4INDEX as u64
}

pub open spec fn spec_v2l1index(va: usize) -> L1Index {
    (va >> 12 & 0x1ff) as usize
}

pub open spec fn spec_v2l2index(va: usize) -> L2Index {
    (va >> 21 & 0x1ff) as usize
}

pub open spec fn spec_v2l3index(va: usize) -> L3Index {
    (va >> 30 & 0x1ff) as usize
}

pub open spec fn spec_v2l4index(va: usize) -> L4Index {
    (va >> 39 & 0x1ff) as usize
}

pub open spec fn spec_va2index(va: usize) -> (L4Index, L3Index, L2Index, L1Index) {
    (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), spec_v2l1index(va))
}

pub open spec fn spec_va22mindex(va: usize) -> (L4Index, L3Index, L2Index) {
    (spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va))
}

pub open spec fn spec_va21gindex(va: usize) -> (L4Index, L3Index) {
    (spec_v2l4index(va), spec_v2l3index(va))
}

pub open spec fn spec_index2va(i: (L4Index, L3Index, L2Index, L1Index)) -> usize
    recommends
        i.0 <= 0x1ff,
        i.1 <= 0x1ff,
        i.2 <= 0x1ff,
        i.3 <= 0x1ff,
{
    // x86_64 VA encoding: L4 in bits 39..48, L3 in bits 30..39, L2 in bits 21..30, L1 in bits 12..21.
    // Combine via bitwise OR (was bitwise AND, which is a typo and produces 0 for typical indices).
    (i.0 as usize) << 39 | (i.1 as usize) << 30 | (i.2 as usize) << 21 | (i.3 as usize) << 12
}

pub fn index2va(i: (L4Index, L3Index, L2Index, L1Index)) -> (ret: usize)
    ensures
        ret == spec_index2va(i),
{
    (i.0 as usize) << 39 | (i.1 as usize) << 30 | (i.2 as usize) << 21 | (i.3 as usize) << 12
}

#[verifier(when_used_as_spec(spec_v2l1index))]
pub fn v2l1index(va: usize) -> (ret: L1Index)
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_v2l1index(va),
        ret <= 0x1ff,
{
    assert((va as u64 >> 12u64 & 0x1ffu64) as usize <= 0x1ff) by (bit_vector);
    (va as u64 >> 12u64 & 0x1ffu64) as usize
}

#[verifier(when_used_as_spec(spec_v2l2index))]
pub fn v2l2index(va: usize) -> (ret: L2Index)
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_v2l2index(va),
        ret <= 0x1ff,
{
    assert((va as u64 >> 21u64 & 0x1ffu64) as usize <= 0x1ff) by (bit_vector);
    (va as u64 >> 21u64 & 0x1ffu64) as usize
}

#[verifier(when_used_as_spec(spec_v2l3index))]
pub fn v2l3index(va: usize) -> (ret: L3Index)
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_v2l3index(va),
        ret <= 0x1ff,
{
    assert((va as u64 >> 30u64 & 0x1ffu64) as usize <= 0x1ff) by (bit_vector);
    (va as u64 >> 30u64 & 0x1ffu64) as usize
}

#[verifier(when_used_as_spec(spec_v2l4index))]
pub fn v2l4index(va: usize) -> (ret: L4Index)
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_v2l4index(va),
        KERNEL_MEM_END_L4INDEX <= ret <= 0x1ff,
{
    assert((va as u64 >> 39u64 & 0x1ffu64) as usize <= 0x1ff) by (bit_vector);
    (va as u64 >> 39u64 & 0x1ffu64) as usize
}

pub fn va21gindex(va: usize) -> (ret: (L4Index, L3Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret.0 == spec_v2l4index(va) && KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 == spec_v2l3index(va) && ret.1 <= 0x1ff,
        ret == spec_va21gindex(va),
{
    (v2l4index(va), v2l3index(va))
}

pub fn va22mindex(va: usize) -> (ret: (L4Index, L3Index, L2Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret.0 == spec_v2l4index(va) && KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 == spec_v2l3index(va) && ret.1 <= 0x1ff,
        ret.2 == spec_v2l2index(va) && ret.2 <= 0x1ff,
        ret == spec_va22mindex(va),
{
    (v2l4index(va), v2l3index(va), v2l2index(va))
}

pub fn va2index(va: usize) -> (ret: (L4Index, L3Index, L2Index, L1Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret.0 == spec_v2l4index(va) && KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 == spec_v2l3index(va) && ret.1 <= 0x1ff,
        ret.2 == spec_v2l2index(va) && ret.2 <= 0x1ff,
        ret.3 == spec_v2l1index(va) && ret.3 <= 0x1ff,
        ret == spec_va2index(va),
{
    (v2l4index(va), v2l3index(va), v2l2index(va), v2l1index(va))
}

pub open spec fn spec_va_add_range(va: usize, i: usize) -> usize {
    (va + (i * 4096)) as usize
}

#[verifier(external_body)]
pub fn va_add_range(va: usize, i: usize) -> (ret: usize)
    ensures
        ret == spec_va_add_range(va, i),
{
    (va + (i * 4096)) as usize
}

// Arithmetic injectivity is only valid for a range whose byte span and end
// address do not wrap.  Keep those hypotheses on the quantified theorem so it
// cannot be used to manufacture distinct addresses from an overflowing range.
#[verifier(external_body)]
pub proof fn va_range_lemma()
    ensures
        forall|va: VAddr, len: usize, i: usize, j: usize|
            #![trigger spec_va_4k_range_valid(va,len), spec_va_add_range(va, i), spec_va_add_range(va, j)]
            va_4k_valid(va)
            && spec_va_4k_range_valid(va, len)
            && len <= usize::MAX / 4096
            && va < usize::MAX - len * 4096
            && 0 <= i < len
            && 0 <= j < len ==> (
            (i == j) == (spec_va_add_range(va, i) == spec_va_add_range(va, j))),
{
}

pub proof fn page_ptr_valid_imply_page_index_valid()
    ensures
        forall|pa: PagePtr|
            #![trigger page_ptr_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_valid(pa) ==> index_valid(NUM_PAGES, page_ptr2page_index(pa)),
{
}

pub proof fn page_index_valid_imply_page_ptr_valid()
    ensures
        forall|i: usize|
            #![trigger index_valid(NUM_PAGES, i)]
            #![trigger page_index2page_ptr(i)]
            index_valid(NUM_PAGES, i) ==> page_ptr_valid(page_index2page_ptr(i)),
{
    assert forall|i: usize| #[trigger] index_valid(NUM_PAGES, i)
        implies page_ptr_valid(page_index2page_ptr(i)) by {
        let ptr = (i * 4096) as usize;
        assert(ptr == i * 4096);
        assert(ptr % 4096 == 0) by (nonlinear_arith)
            requires ptr == i * 4096;
        assert(ptr / 4096 == i) by (nonlinear_arith)
            requires ptr == i * 4096;
    }
}

pub proof fn page_ptr_roundtrip()
    ensures
        forall|pa: PagePtr|
            #![trigger page_ptr_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_valid(pa) ==> pa == page_index2page_ptr(page_ptr2page_index(pa)),
{
    assert forall|pa: PagePtr| #[trigger] page_ptr_valid(pa) implies pa == page_index2page_ptr(page_ptr2page_index(pa)) by {
        let i = (pa / 4096usize) as usize;
        assert(i * 4096 == pa) by (nonlinear_arith)
            requires pa % 4096 == 0, i == pa / 4096;
    }
}

pub proof fn page_index_roundtrip()
    ensures
        forall|i: usize|
            #![trigger index_valid(NUM_PAGES, i)]
            #![trigger page_index2page_ptr(i)]
            index_valid(NUM_PAGES, i) ==> i == page_ptr2page_index(page_index2page_ptr(i)),
{
    assert forall|i: usize| #[trigger] index_valid(NUM_PAGES, i) implies i == page_ptr2page_index(page_index2page_ptr(i)) by {
        let p = (i * 4096usize) as usize;
        assert(p / 4096 == i) by (nonlinear_arith)
            requires p == i * 4096;
    }
}

pub proof fn page_ptr2page_index_injective()
    ensures
        forall|pi: usize, pj: usize|
            #![trigger page_ptr_valid(pi), page_ptr_valid(pj), page_ptr2page_index(pi), page_ptr2page_index(pj)]
            page_ptr_valid(pi) && page_ptr_valid(pj) && pi != pj ==> page_ptr2page_index(pi)
                != page_ptr2page_index(pj),
{
    assert forall|pi: usize, pj: usize|
        page_ptr_valid(pi) && page_ptr_valid(pj) && pi != pj implies
        #[trigger] page_ptr2page_index(pi) != #[trigger] page_ptr2page_index(pj) by {
        let i = (pi / 4096usize) as usize;
        let j = (pj / 4096usize) as usize;
        assert(i * 4096 == pi) by (nonlinear_arith)
            requires pi % 4096 == 0, i == pi / 4096;
        assert(j * 4096 == pj) by (nonlinear_arith)
            requires pj % 4096 == 0, j == pj / 4096;
    }
}

pub proof fn page_index2page_ptr_injective()
    ensures
        forall|i: usize, j: usize|
            #![trigger page_index2page_ptr(i), page_index2page_ptr(j)]
            index_valid(NUM_PAGES, i) && index_valid(NUM_PAGES, j) && i != j
                ==> page_index2page_ptr(i) != page_index2page_ptr(j),
{
    assert forall|i: usize, j: usize|
        index_valid(NUM_PAGES, i) && index_valid(NUM_PAGES, j) && i != j implies
        #[trigger] page_index2page_ptr(i) != #[trigger] page_index2page_ptr(j) by {
        let pi = (i * 4096usize) as usize;
        let pj = (j * 4096usize) as usize;
        assert(pi / 4096 == i) by (nonlinear_arith)
            requires pi == i * 4096;
        assert(pj / 4096 == j) by (nonlinear_arith)
            requires pj == j * 4096;
    }
}

// Keep each trusted VA/index fact in its own lemma so callers import only the
// quantifier and trigger needed by the assertion currently being proved.
#[verifier(external_body)]
pub proof fn spec_va_4k_valid_imply_indices_valid()
    ensures
        forall|va: VAddr|
            #![trigger spec_va_4k_valid(va), spec_v2l4index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l3index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l2index(va)]
            #![trigger spec_va_4k_valid(va), spec_v2l1index(va)]
            spec_va_4k_valid(va) ==> pei_valid(spec_v2l4index(va)) && pei_valid(spec_v2l3index(va))
                && pei_valid(spec_v2l2index(va)) && pei_valid(spec_v2l1index(va)),
{
}

#[verifier(external_body)]
pub proof fn spec_index2va_injective()
    ensures
        forall|
            l4i: L4Index,
            l3i: L3Index,
            l2i: L2Index,
            l1i: L1Index,
            l4j: L4Index,
            l3j: L3Index,
            l2j: L2Index,
            l1j: L1Index,
        |
            #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_index2va((l4j,l3j,l2j,l1j))]
            pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i)
            &&
            pei_valid(l4j) && pei_valid(l3j) && pei_valid(l2j) && pei_valid(l1j)
            ==>
            (spec_index2va((l4i, l3i, l2i, l1i)) == spec_index2va((l4j, l3j, l2j, l1j)))
            ==
            ((l4i, l3i, l2i, l1i) =~= (l4j, l3j, l2j, l1j)),
{
}

#[verifier(external_body)]
pub proof fn spec_va_4k_index_roundtrip()
    ensures
        forall|va: VAddr, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index|
            #![trigger spec_index2va((l4i,l3i,l2i,l1i)), spec_va2index(va)]
            va_4k_valid(va) && spec_va2index(va) == (l4i, l3i, l2i, l1i) <==> KERNEL_MEM_END_L4INDEX <= l4i && pei_valid(l4i) && pei_valid(l3i) && pei_valid(l2i) && pei_valid(l1i) && spec_index2va(
                (l4i, l3i, l2i, l1i),
            ) == va,
{
}

} // verus!
