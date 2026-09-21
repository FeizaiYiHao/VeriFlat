use vstd::prelude::*;
use vstd::assert_sets_equal;
verus! {
use crate::*;

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
    proof { lemma_u64_to_usize_roundtrip(MAX_USIZE); }
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

pub open spec fn iova_4k_valid(iova: usize) -> bool {
    iova & (!MEM_4K_MASK) as usize == 0
}

pub open spec fn iova_2m_valid(iova: usize) -> bool {
    iova & (!MEM_2M_MASK) as usize == 0
}

pub open spec fn iova_1g_valid(iova: usize) -> bool {
    iova & (!MEM_1G_MASK) as usize == 0
}

pub open spec fn page_ptr_valid(ptr: usize) -> bool {
    &&& ptr % 0x1000 == 0
    &&& ptr / 0x1000 < NUM_PAGES
}

pub proof fn page_ptr_valid_imply_mem_valid(v: usize)
    requires
        page_ptr_valid(v),
    ensures
        mem_valid(v),
{
    assert(v & (!0x0000_ffff_ffff_f000u64) as usize == 0) by (bit_vector)
        requires
            ((v % 4096) == 0) && ((v / 4096) < 2 * 1024 * 1024),
    ;
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
        len <= usize::MAX / 4096,
        va < usize::MAX - len * 4096,
    ensures
        spec_va_4k_range_valid(va, len) == ret,
{
    for idx in iter: 0..len
        invariant
            va_4k_valid(va),
            len <= usize::MAX / 4096,
            va < usize::MAX - len * 4096,
            forall|i: usize|
                #![trigger spec_va_add_range(va, i)]
                0 <= i < idx ==> spec_va_4k_valid(spec_va_add_range(va, i)),
    {
        assert(idx <= usize::MAX / 4096) by (bit_vector)
            requires
                idx < len,
                len <= usize::MAX / 4096;
        assert(va <= usize::MAX - idx * 4096) by (bit_vector)
            requires
                idx < len,
                len <= usize::MAX / 4096,
                va < usize::MAX - len * 4096;
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

pub proof fn spec_v2l4index_monotonic(start: VAddr, end: VAddr)
    requires
        spec_va_4k_valid(start),
        spec_va_4k_valid(end),
        start <= end,
    ensures
        spec_v2l4index(start) <= spec_v2l4index(end),
{
    assert(spec_v2l4index(start) <= spec_v2l4index(end)) by (bit_vector)
        requires
            spec_va_4k_valid(start),
            spec_va_4k_valid(end),
            start <= end,
    ;
}

pub proof fn spec_index2va_le_implies_4k_indices_lex_le(
    start: (L4Index, L3Index, L2Index, L1Index),
    end: (L4Index, L3Index, L2Index, L1Index),
)
    requires
        pei_valid(start.0),
        pei_valid(start.1),
        pei_valid(start.2),
        pei_valid(start.3),
        pei_valid(end.0),
        pei_valid(end.1),
        pei_valid(end.2),
        pei_valid(end.3),
        spec_index2va(start) <= spec_index2va(end),
    ensures
        start.0 < end.0
            || (start.0 == end.0
                && (start.1 < end.1
                    || (start.1 == end.1
                        && (start.2 < end.2
                            || (start.2 == end.2 && start.3 <= end.3))))),
{
    let (start_l4i, start_l3i, start_l2i, start_l1i) = start;
    let (end_l4i, end_l3i, end_l2i, end_l1i) = end;
    assert(
        start_l4i < end_l4i
            || (start_l4i == end_l4i
                && (start_l3i < end_l3i
                    || (start_l3i == end_l3i
                        && (start_l2i < end_l2i
                            || (start_l2i == end_l2i && start_l1i <= end_l1i)))))
    ) by (bit_vector)
        requires
            pei_valid(start_l4i),
            pei_valid(start_l3i),
            pei_valid(start_l2i),
            pei_valid(start_l1i),
            pei_valid(end_l4i),
            pei_valid(end_l3i),
            pei_valid(end_l2i),
            pei_valid(end_l1i),
            spec_index2va((start_l4i, start_l3i, start_l2i, start_l1i))
                <= spec_index2va((end_l4i, end_l3i, end_l2i, end_l1i)),
    ;
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

pub proof fn mask_9_bits_le(value: u64)
    ensures
        value & 0x1ffu64 <= 0x1ffu64,
{
    assert(value & 0x1ffu64 <= 0x1ffu64) by (bit_vector);
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
    proof { mask_9_bits_le(va as u64 >> 12u64); }
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
    proof { mask_9_bits_le(va as u64 >> 21u64); }
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
    proof { mask_9_bits_le(va as u64 >> 30u64); }
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
    proof { mask_9_bits_le(va as u64 >> 39u64); }
    (va as u64 >> 39u64 & 0x1ffu64) as usize
}

pub fn va21gindex(va: usize) -> (ret: (L4Index, L3Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_va21gindex(va),
        KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 <= 0x1ff,
{
    (v2l4index(va), v2l3index(va))
}

pub fn va22mindex(va: usize) -> (ret: (L4Index, L3Index, L2Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_va22mindex(va),
        KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 <= 0x1ff,
        ret.2 <= 0x1ff,
{
    (v2l4index(va), v2l3index(va), v2l2index(va))
}

pub fn va2index(va: usize) -> (ret: (L4Index, L3Index, L2Index, L1Index))
    requires
        va_4k_valid(va) || va_2m_valid(va) || va_1g_valid(va),
    ensures
        ret == spec_va2index(va),
        KERNEL_MEM_END_L4INDEX <= ret.0 <= 0x1ff,
        ret.1 <= 0x1ff,
        ret.2 <= 0x1ff,
        ret.3 <= 0x1ff,
{
    (v2l4index(va), v2l3index(va), v2l2index(va), v2l1index(va))
}

pub open spec fn spec_va_add_range(va: usize, i: usize) -> usize {
    (va + (i * 4096)) as usize
}

pub fn va_add_range(va: usize, i: usize) -> (ret: usize)
    requires
        i <= usize::MAX / 4096,
        va <= usize::MAX - i * 4096,
    ensures
        ret == spec_va_add_range(va, i),
{
    (va + (i * 4096)) as usize
}

// Arithmetic injectivity is only valid while the byte span does not wrap.
pub proof fn va_range_lemma(va: VAddr, len: usize, i: usize, j: usize)
    requires
        len <= usize::MAX / 4096,
        va < usize::MAX - len * 4096,
        i < len,
        j < len,
    ensures
        (i == j) == (spec_va_add_range(va, i) == spec_va_add_range(va, j)),
{
    assert(spec_va_add_range(va, i) as int == va as int + i as int * 4096) by (bit_vector)
        requires
            i < len,
            len <= usize::MAX / 4096,
            va < usize::MAX - len * 4096;
    assert(spec_va_add_range(va, j) as int == va as int + j as int * 4096) by (bit_vector)
        requires
            j < len,
            len <= usize::MAX / 4096,
            va < usize::MAX - len * 4096;
    if spec_va_add_range(va, i) == spec_va_add_range(va, j) {
        vstd::arithmetic::mul::lemma_mul_is_commutative(i as int, 4096);
        vstd::arithmetic::mul::lemma_mul_is_commutative(j as int, 4096);
        vstd::arithmetic::mul::lemma_mul_equality_converse(4096, i as int, j as int);
    }
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
}

pub proof fn page_ptr_roundtrip()
    ensures
        forall|pa: PagePtr|
            #![trigger page_ptr_valid(pa)]
            #![trigger page_ptr2page_index(pa)]
            page_ptr_valid(pa) ==> pa == page_index2page_ptr(page_ptr2page_index(pa)),
{
}

pub proof fn page_index_roundtrip()
    ensures
        forall|i: usize|
            #![trigger index_valid(NUM_PAGES, i)]
            #![trigger page_index2page_ptr(i)]
            index_valid(NUM_PAGES, i) ==> i == page_ptr2page_index(page_index2page_ptr(i)),
{
}

pub proof fn page_ptr2page_index_injective()
    ensures
        forall|pi: usize, pj: usize|
            #![trigger page_ptr_valid(pi), page_ptr_valid(pj), page_ptr2page_index(pi), page_ptr2page_index(pj)]
            page_ptr_valid(pi) && page_ptr_valid(pj) && pi != pj ==> page_ptr2page_index(pi)
                != page_ptr2page_index(pj),
{
}

pub proof fn page_ptr2page_index_neq(left: PagePtr, right: PagePtr)
    requires
        page_ptr_valid(left),
        page_ptr_valid(right),
        left != right,
    ensures
        page_ptr2page_index(left) != page_ptr2page_index(right),
{
    page_ptr2page_index_injective();
}

pub proof fn page_ptr_seq_indices_no_duplicates(pages: Seq<PagePtr>)
    requires
        pages.no_duplicates(),
        forall|i: int|
            #![trigger page_ptr_valid(pages.spec_index(i))]
            0 <= i < pages.len() ==> page_ptr_valid(pages.spec_index(i)),
    ensures
        pages.map_values(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
        ).no_duplicates(),
{
    let indices = pages.map_values(
        |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
    );
    assert forall|i: int, j: int|
        0 <= i < j < indices.len()
        implies indices.spec_index(i) != indices.spec_index(j)
    by {
        page_ptr2page_index_neq(pages.spec_index(i), pages.spec_index(j));
    };
}

pub proof fn page_ptr_seq_indices_excludes_page(
    pages: Seq<PagePtr>,
    excluded_page: PagePtr,
)
    requires
        page_ptr_valid(excluded_page),
        forall|i: int|
            #![trigger page_ptr_valid(pages.spec_index(i))]
            0 <= i < pages.len()
                ==> page_ptr_valid(pages.spec_index(i)),
        !pages.to_set().contains(excluded_page),
    ensures
        !pages.map_values(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
        ).to_set().contains(page_ptr2page_index(excluded_page)),
{
    pages.to_set_ensures();
    let page_ptr_set = pages.to_set();
    let mapped = pages.map_values(
        |page_ptr: PagePtr| page_ptr2page_index(page_ptr),
    ).to_set();
    let mapped_by = page_ptr_set.map_by(
        |page_ptr: PagePtr| page_ptr2page_index(page_ptr), |index: PageIndex| spec_page_index2page_ptr(index),
    );
    assert(mapped =~= mapped_by) by {
        broadcast use Seq::lemma_to_set_map_commutes;
        page_ptr_roundtrip();
        assert_sets_equal!(mapped == mapped_by, index => {
            page_ptr_set.lemma_map_contains(|page_ptr: PagePtr| page_ptr2page_index(page_ptr), index);
            page_ptr_set.lemma_map_by_contains(
                |page_ptr: PagePtr| page_ptr2page_index(page_ptr), |index: PageIndex| spec_page_index2page_ptr(index), index,
            );
        });
    };
    if mapped.contains(page_ptr2page_index(excluded_page)) {
        page_ptr_set.lemma_map_by_contains(
            |page_ptr: PagePtr| page_ptr2page_index(page_ptr), |index: PageIndex| spec_page_index2page_ptr(index),
            page_ptr2page_index(excluded_page),
        );
        page_ptr_roundtrip();
    }
}

// Keep each trusted VA/index fact in its own lemma so callers import only the
// quantifier and trigger needed by the assertion currently being proved.
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
    assert forall|va: VAddr|
        #![trigger spec_va_4k_valid(va), spec_v2l4index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l3index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l2index(va)]
        #![trigger spec_va_4k_valid(va), spec_v2l1index(va)]
        spec_va_4k_valid(va) implies
            pei_valid(spec_v2l4index(va))
            && pei_valid(spec_v2l3index(va))
            && pei_valid(spec_v2l2index(va))
            && pei_valid(spec_v2l1index(va))
    by {
        assert(spec_v2l4index(va) < 512) by (bit_vector);
        assert(spec_v2l3index(va) < 512) by (bit_vector);
        assert(spec_v2l2index(va) < 512) by (bit_vector);
        assert(spec_v2l1index(va) < 512) by (bit_vector);
    };
}

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
    assert forall|
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
        implies
        (spec_index2va((l4i, l3i, l2i, l1i))
            == spec_index2va((l4j, l3j, l2j, l1j)))
        ==
        ((l4i, l3i, l2i, l1i) =~= (l4j, l3j, l2j, l1j))
    by {
        assert(
            ((l4i, l3i, l2i, l1i) =~= (l4j, l3j, l2j, l1j))
            ==
            (l4i == l4j && l3i == l3j && l2i == l2j && l1i == l1j)
        );
        assert(
            (spec_index2va((l4i, l3i, l2i, l1i))
                == spec_index2va((l4j, l3j, l2j, l1j)))
            ==
            (l4i == l4j && l3i == l3j && l2i == l2j && l1i == l1j)
        ) by (bit_vector)
            requires
                pei_valid(l4i),
                pei_valid(l3i),
                pei_valid(l2i),
                pei_valid(l1i),
                pei_valid(l4j),
                pei_valid(l3j),
                pei_valid(l2j),
                pei_valid(l1j);
        assert(
            (spec_index2va((l4i, l3i, l2i, l1i))
                == spec_index2va((l4j, l3j, l2j, l1j)))
            ==
            ((l4i, l3i, l2i, l1i) =~= (l4j, l3j, l2j, l1j))
        );
    };
}

pub broadcast proof fn spec_va_4k_index_roundtrip_at(
    va: VAddr,
    l4i: L4Index,
    l3i: L3Index,
    l2i: L2Index,
    l1i: L1Index,
)
    ensures
        va_4k_valid(va)
            && #[trigger] spec_va2index(va) == (l4i, l3i, l2i, l1i)
        <==>
        KERNEL_MEM_END_L4INDEX <= l4i
            && pei_valid(l4i)
            && pei_valid(l3i)
            && pei_valid(l2i)
            && pei_valid(l1i)
            && #[trigger] spec_index2va((l4i, l3i, l2i, l1i)) == va,
{
    assert(
        (spec_va2index(va) == (l4i, l3i, l2i, l1i))
        ==
        (spec_v2l4index(va) == l4i
            && spec_v2l3index(va) == l3i
            && spec_v2l2index(va) == l2i
            && spec_v2l1index(va) == l1i)
    );
    assert(
        spec_va_4k_valid(va)
            && spec_v2l4index(va) == l4i
            && spec_v2l3index(va) == l3i
            && spec_v2l2index(va) == l2i
            && spec_v2l1index(va) == l1i
        <==>
        KERNEL_MEM_END_L4INDEX <= l4i
            && pei_valid(l4i)
            && pei_valid(l3i)
            && pei_valid(l2i)
            && pei_valid(l1i)
            && spec_index2va((l4i, l3i, l2i, l1i)) == va
    ) by (bit_vector);
}
} // verus!
