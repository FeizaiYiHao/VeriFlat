use vstd::prelude::*;

use crate::*;

verus! {
pub proof fn lemma_cache_len_fold_congruence(
    s1: Seq<RwLock<AllocatorCache, (), (), NO_KILL_STATE>>,
    s2: Seq<RwLock<AllocatorCache, (), (), NO_KILL_STATE>>,
)
    requires
        s1.len() == s2.len(),
        forall|i: int| #![trigger s1.spec_index(i), s2.spec_index(i)]
            0 <= i < s1.len() ==>
            s1.spec_index(i).view().linked_list.len() == s2.spec_index(i).view().linked_list.len(),
    ensures
        s1.fold_left(0int, |sum: int, cpu_rw_lock: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + cpu_rw_lock.view().linked_list.len()})
            == s2.fold_left(0int, |sum: int, cpu_rw_lock: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + cpu_rw_lock.view().linked_list.len()}),
    decreases s1.len(),
{
    if s1.len() != 0 {
        lemma_cache_len_fold_congruence(s1.drop_last(), s2.drop_last());
    }
}

pub proof fn lemma_cache_len_fold_change_one(
    s1: Seq<RwLock<AllocatorCache, (), (), NO_KILL_STATE>>,
    s2: Seq<RwLock<AllocatorCache, (), (), NO_KILL_STATE>>,
    j: int,
)
    requires
        s1.len() == s2.len(),
        0 <= j < s1.len(),
        s1.spec_index(j).view().linked_list.len() == s2.spec_index(j).view().linked_list.len() + 1,
        forall|i: int| #![trigger s1.spec_index(i)] #![trigger s2.spec_index(i)]
            0 <= i < s1.len() && i != j ==>
            s1.spec_index(i).view().linked_list.len() == s2.spec_index(i).view().linked_list.len(),
    ensures
        s1.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()})
            == s2.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) + 1,
    decreases s1.len(),
{
    if j == s1.len() - 1 {
        lemma_cache_len_fold_congruence(s1.drop_last(), s2.drop_last());
    } else {
        lemma_cache_len_fold_change_one(s1.drop_last(), s2.drop_last(), j);
    }
}

pub proof fn lemma_cache_len_fold_change_one_array(
    old_arr: LockedArray<AllocatorCache, (), (), NUM_CPUS, NO_KILL_STATE>,
    new_arr: LockedArray<AllocatorCache, (), (), NUM_CPUS, NO_KILL_STATE>,
    j: usize,
)
    requires
        old_arr.inv(),
        new_arr.inv(),
        index_valid(NUM_CPUS, j),
        new_arr.entries_unchanged_except(&old_arr, j),
        old_arr.spec_index(j).view().view().linked_list.len()
            == new_arr.spec_index(j).view().view().linked_list.len() + 1,
    ensures
        old_arr.view().fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()})
            == new_arr.view().fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) + 1,
{
    let f = |sum: int, c: RwLock<AllocatorCache, (), (), NO_KILL_STATE>|
        sum + c.view().linked_list.len();
    assert(old_arr.view().fold_left(0int, f)
        == new_arr.view().fold_left(0int, f) + 1) by {
        assert forall|i: int|
            #![trigger old_arr.view().spec_index(i), new_arr.view().spec_index(i)]
            0 <= i < old_arr.view().len() && i != j as int
            implies old_arr.view().spec_index(i).view().linked_list.len()
                == new_arr.view().spec_index(i).view().linked_list.len()
        by {
            old_arr.lemma_view_index(i as usize);
            new_arr.lemma_view_index(i as usize);
        };
        lemma_cache_len_fold_change_one(old_arr.view(), new_arr.view(), j as int);
    };
}

pub proof fn lemma_cache_len_fold_nonneg(
    s: Seq<RwLock<AllocatorCache, (), (), NO_KILL_STATE>>,
)
    ensures
        s.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) >= 0,
    decreases s.len(),
{
    if s.len() != 0 {
        lemma_cache_len_fold_nonneg(s.drop_last());
    }
}

pub proof fn lemma_cache_len_fold_ge_elem(
    s: Seq<RwLock<AllocatorCache, (), (), NO_KILL_STATE>>,
    j: int,
)
    requires
        0 <= j < s.len(),
    ensures
        s.fold_left(0int, |sum: int, c: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + c.view().linked_list.len()}) >= s.spec_index(j).view().linked_list.len(),
    decreases s.len(),
{
    if j == s.len() - 1 {
        lemma_cache_len_fold_nonneg(s.drop_last());
    } else {
        lemma_cache_len_fold_ge_elem(s.drop_last(), j);
    }
}

pub proof fn lemma_cache_len_fold_all_zero(
    s: Seq<RwLock<AllocatorCache, (), (), NO_KILL_STATE>>,
)
    requires
        forall|j: int| #![trigger s.spec_index(j)]
            0 <= j < s.len() ==>
                s.spec_index(j).view().linked_list.view().len() == 0,
    ensures
        s.fold_left(
            0int,
            |sum: int, c: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {
                sum + c.view().linked_list.len()
            },
        ) == 0,
    decreases s.len(),
{
    if s.len() != 0 {
        lemma_cache_len_fold_all_zero(s.drop_last());
    }
}
}
