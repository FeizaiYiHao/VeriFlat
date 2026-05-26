use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::util::page_ptr_util_u::*;

pub proof fn lemma_usize_u64(x: u64)
    ensures
        x as usize as u64 == x,
{
    assert(x as usize as u64 == x) by (bit_vector);
}

// SPEC FIX: x must be in usize range; otherwise x as usize wraps and the equality fails.
pub proof fn lemma_usize_int(x: int)
    requires
        0 <= x <= usize::MAX,
    ensures
        x as usize as int == x,
{
}

pub proof fn set_lemma<A>()
    ensures
        forall|s1: Set<A>, s2: Set<A>, e: A|
            (s1 + s2).insert(e) == s1 + (s2.insert(e)) && s1 + (s2.insert(e)) == s2 + (s1.insert(e))
                && (s1 + s2).insert(e) == s2 + (s1.insert(e)) && (!(s1 + s2).contains(e)
                <==> !s1.contains(e) && !s2.contains(
                e,
            )),
// forall|s1:Set<A>, s2:Set<A>, s3:Set<A>, s4:Set<A>, e:A|
//     (!(s1 + s2 + s3 + s4).contains(e)) <==> (!s1.contains(e) && !s2.contains(e) && !s3.contains(e) && !s4.contains(e))

{
    assert forall|s1: Set<A>, s2: Set<A>, e: A|
        (s1 + s2).insert(e) == s1 + (s2.insert(e))
            && s1 + (s2.insert(e)) == s2 + (s1.insert(e))
            && (s1 + s2).insert(e) == s2 + (s1.insert(e))
            && (!(s1 + s2).contains(e) <==> !s1.contains(e) && !s2.contains(e)) by {
        assert((s1 + s2).insert(e) =~= s1 + (s2.insert(e)));
        assert(s1 + (s2.insert(e)) =~= s2 + (s1.insert(e)));
        assert((s1 + s2).insert(e) =~= s2 + (s1.insert(e)));
    }
}

pub proof fn set_insert_lemma<A>()
    ensures
        forall|s1: Set<A>, x: A, y: A| x != y ==> (s1.insert(x).contains(y) == s1.contains(y)),
        forall|s1: Set<A>, x: A, y: A| s1.contains(y) ==> s1.insert(x).contains(y),
        forall|s1: Set<A>, x: A| s1.contains(x) ==> (s1.insert(x) == s1),
{
    broadcast use vstd::set::axiom_set_insert_same;
    broadcast use vstd::set::axiom_set_insert_different;
    assert forall|s1: Set<A>, x: A| s1.contains(x) implies s1.insert(x) == s1 by {
        assert(s1.insert(x) =~= s1);
    }
}

pub proof fn set_add_lemma<A>()
    ensures
        forall|s1: Set<A>|  s1 + Set::<A>::empty() == s1,
        forall|s1: Set<A>, s2: Set<A>, diff: Set<A>| 
            diff.subset_of(s1) ==> (s1 - diff) + (s2 + diff) == s1 + s2
{
    assert forall|s1: Set<A>| s1 + Set::<A>::empty() == s1 by {
        assert(s1 + Set::<A>::empty() =~= s1);
    }
    assert forall|s1: Set<A>, s2: Set<A>, diff: Set<A>|
        diff.subset_of(s1) implies (s1 - diff) + (s2 + diff) == s1 + s2 by {
        assert((s1 - diff) + (s2 + diff) =~= s1 + s2);
    }
}

// SPEC FIX: 5th-8th conjuncts originally used page_index_valid(ptr) on a PagePtr; that's a
// type confusion (a pointer 1..NUM_PAGES would satisfy page_index_valid but is not a valid
// page pointer because not 4096-aligned). Fixed to page_ptr_valid for the pointer ones.
pub proof fn page_ptr_lemma()
    ensures
        forall|ptr: PagePtr|
            #![auto]
            page_ptr_valid(ptr) ==> page_index_valid(page_ptr2page_index(ptr)),
        forall|index: usize|
            #![auto]
            page_index_valid(index) ==> page_ptr_valid(page_index2page_ptr(index)),
        forall|ptr: PagePtr|
            #![auto]
            page_ptr_valid(ptr) ==> page_index2page_ptr(page_ptr2page_index(ptr)) == ptr,
        forall|index: usize|
            #![auto]
            page_index_valid(index) ==> page_ptr2page_index(page_index2page_ptr(index)) == index,
        forall|ptr1: PagePtr, ptr2: PagePtr|
            #![auto]
            page_ptr_valid(ptr1) && page_ptr_valid(ptr2) && ptr1 == ptr2
                ==> page_ptr2page_index(ptr1) == page_ptr2page_index(ptr2),
        forall|ptr1: PagePtr, ptr2: PagePtr|
            #![auto]
            page_ptr_valid(ptr1) && page_ptr_valid(ptr2) && ptr1 != ptr2
                ==> page_ptr2page_index(ptr1) != page_ptr2page_index(ptr2),
        forall|index1: usize, index2: usize|
            #![auto]
            page_index_valid(index1) && page_index_valid(index2) && index1 == index2
                ==> page_index2page_ptr(index1) == page_index2page_ptr(index2),
        forall|index1: usize, index2: usize|
            #![auto]
            page_index_valid(index1) && page_index_valid(index2) && index1 != index2
                ==> page_index2page_ptr(index1) != page_index2page_ptr(index2),
{
    assert forall|index: usize| #[trigger] page_index_valid(index) implies page_ptr_valid(page_index2page_ptr(index)) by {
        let ptr = (index * 4096) as usize;
        assert(ptr == index * 4096);
        assert(ptr % 4096 == 0) by (nonlinear_arith)
            requires ptr == index * 4096;
        assert(ptr / 4096 == index) by (nonlinear_arith)
            requires ptr == index * 4096;
    }
    assert forall|ptr: PagePtr| #[trigger] page_ptr_valid(ptr) implies page_index2page_ptr(page_ptr2page_index(ptr)) == ptr by {
        let i = (ptr / 4096usize) as usize;
        assert(i * 4096 == ptr) by (nonlinear_arith)
            requires ptr % 4096 == 0, i == ptr / 4096;
    }
    assert forall|index: usize| #[trigger] page_index_valid(index) implies page_ptr2page_index(page_index2page_ptr(index)) == index by {
        let ptr = (index * 4096usize) as usize;
        assert(ptr / 4096 == index) by (nonlinear_arith)
            requires ptr == index * 4096;
    }
    assert forall|ptr1: PagePtr, ptr2: PagePtr|
        page_ptr_valid(ptr1) && page_ptr_valid(ptr2) && ptr1 != ptr2 implies
        page_ptr2page_index(ptr1) != page_ptr2page_index(ptr2) by {
        let i1 = (ptr1 / 4096usize) as usize;
        let i2 = (ptr2 / 4096usize) as usize;
        assert(i1 * 4096 == ptr1) by (nonlinear_arith)
            requires ptr1 % 4096 == 0, i1 == ptr1 / 4096;
        assert(i2 * 4096 == ptr2) by (nonlinear_arith)
            requires ptr2 % 4096 == 0, i2 == ptr2 / 4096;
    }
    assert forall|index1: usize, index2: usize|
        page_index_valid(index1) && page_index_valid(index2) && index1 != index2 implies
        page_index2page_ptr(index1) != page_index2page_ptr(index2) by {
        let p1 = (index1 * 4096usize) as usize;
        let p2 = (index2 * 4096usize) as usize;
        assert(p1 / 4096 == index1) by (nonlinear_arith)
            requires p1 == index1 * 4096;
        assert(p2 / 4096 == index2) by (nonlinear_arith)
            requires p2 == index2 * 4096;
    }
}

} // verus!
