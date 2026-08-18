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
        forall|s1: Set<A>, s2: Set<A>, e: A| #![auto]
            (s1 + s2).insert(e) == s1 + (s2.insert(e)) && s1 + (s2.insert(e)) == s2 + (s1.insert(e))
                && (s1 + s2).insert(e) == s2 + (s1.insert(e)) && (!(s1 + s2).contains(e)
                <==> !s1.contains(e) && !s2.contains(
                e,
            )),
// forall|s1:Set<A>, s2:Set<A>, s3:Set<A>, s4:Set<A>, e:A|
//     (!(s1 + s2 + s3 + s4).contains(e)) <==> (!s1.contains(e) && !s2.contains(e) && !s3.contains(e) && !s4.contains(e))

{
    assert forall|s1: Set<A>, s2: Set<A>, e: A| #![auto]
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
        forall|s1: Set<A>, x: A| #![auto] s1.contains(x) ==> (s1.insert(x) == s1),
{
    broadcast use vstd::set::lemma_set_insert_same;
    broadcast use vstd::set::lemma_set_insert_different;
    assert forall|s1: Set<A>, x: A| #![auto] s1.contains(x) implies s1.insert(x) == s1 by {
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

} // verus!
