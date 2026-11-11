use vstd::prelude::*;

use crate::*;

verus! {
pub proof fn cache_inv_implies_cache_len_fold_bounded<const SIZE: usize>(caches: LockedArray<AllocatorCache<SIZE>, (), (), NUM_CPUS, NO_KILL_STATE>)
    requires
        caches.inv(),
        forall|cpu: CpuId| #![trigger caches.spec_index(cpu)] index_valid(NUM_CPUS, cpu) ==> caches.spec_index(cpu).inv(),
    ensures
        caches.view().fold_left(0int, |sum: int, cache: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| sum + cache.view().linked_list.len()) <= NUM_CPUS * ALLOCATOR_MAX_WATERMARK,
{
    caches.view_index_eq_element_value();
    seq_fold_upper_bound(caches.view(), |sum: int, cache: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| sum + cache.view().linked_list.len(), ALLOCATOR_MAX_WATERMARK as int);
}

pub proof fn equal_cache_lens_implies_cache_len_fold_eq<const SIZE: usize>(s1: Seq<LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>>, s2: Seq<LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>>)
    requires
        s1.len() == s2.len(),
        forall|i: int| #![trigger s1.spec_index(i), s2.spec_index(i)]
            0 <= i < s1.len() ==> s1.spec_index(i).view().linked_list.len() == s2.spec_index(i).view().linked_list.len(),
    ensures
        s1.fold_left(0int, |sum: int, cache_lock: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + cache_lock.view().linked_list.len() })
            == s2.fold_left(0int, |sum: int, cache_lock: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + cache_lock.view().linked_list.len() }),
    decreases s1.len(),
{
    if s1.len() != 0 {
        equal_cache_lens_implies_cache_len_fold_eq(s1.drop_last(), s2.drop_last());
    }
}

pub proof fn one_cache_one_longer_implies_cache_len_fold_one_larger<const SIZE: usize>(s1: Seq<LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>>, s2: Seq<LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>>, j: int)
    requires
        s1.len() == s2.len(),
        0 <= j < s1.len(),
        s1.spec_index(j).view().linked_list.len() == s2.spec_index(j).view().linked_list.len() + 1,
        forall|i: int| #![trigger s1.spec_index(i)] #![trigger s2.spec_index(i)]
            0 <= i < s1.len() && i != j ==> s1.spec_index(i).view().linked_list.len() == s2.spec_index(i).view().linked_list.len(),
    ensures
        s1.fold_left(0int, |sum: int, c: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + c.view().linked_list.len() })
            == s2.fold_left(0int, |sum: int, c: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + c.view().linked_list.len() }) + 1,
    decreases s1.len(),
{
    if j == s1.len() - 1 {
        equal_cache_lens_implies_cache_len_fold_eq(s1.drop_last(), s2.drop_last());
    } else {
        one_cache_one_longer_implies_cache_len_fold_one_larger(s1.drop_last(), s2.drop_last(), j);
    }
}

pub proof fn one_array_cache_one_longer_implies_cache_len_fold_one_larger<const SIZE: usize>(old_arr: LockedArray<AllocatorCache<SIZE>, (), (), NUM_CPUS, NO_KILL_STATE>, new_arr: LockedArray<AllocatorCache<SIZE>, (), (), NUM_CPUS, NO_KILL_STATE>, j: usize)
    requires
        old_arr.inv(),
        new_arr.inv(),
        index_valid(NUM_CPUS, j),
        new_arr.entries_unchanged_except(&old_arr, j),
        old_arr.spec_index(j).view().view().linked_list.len() == new_arr.spec_index(j).view().view().linked_list.len() + 1,
    ensures
        old_arr.view().fold_left(0int, |sum: int, c: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + c.view().linked_list.len() })
            == new_arr.view().fold_left(0int, |sum: int, c: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + c.view().linked_list.len() }) + 1,
{
    let f = |sum: int, c: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| sum + c.view().linked_list.len();
    assert(old_arr.view().fold_left(0int, f) == new_arr.view().fold_left(0int, f) + 1) by { old_arr.view_index_eq_element_value(); new_arr.view_index_eq_element_value(); one_cache_one_longer_implies_cache_len_fold_one_larger(old_arr.view(), new_arr.view(), j as int); };
}

pub proof fn cache_len_fold_implies_nonneg<const SIZE: usize>(s: Seq<LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>>)
    ensures
        s.fold_left(0int, |sum: int, c: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + c.view().linked_list.len() }) >= 0,
    decreases s.len(),
{
    if s.len() != 0 {
        cache_len_fold_implies_nonneg(s.drop_last());
    }
}

pub proof fn cache_len_fold_implies_ge_cache_len_at_index<const SIZE: usize>(s: Seq<LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>>, j: int)
    requires
        0 <= j < s.len(),
    ensures
        s.fold_left(0int, |sum: int, c: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + c.view().linked_list.len() }) >= s.spec_index(j).view().linked_list.len(),
    decreases s.len(),
{
    if j == s.len() - 1 {
        cache_len_fold_implies_nonneg(s.drop_last());
    } else {
        cache_len_fold_implies_ge_cache_len_at_index(s.drop_last(), j);
    }
}

pub proof fn empty_caches_implies_cache_len_fold_zero<const SIZE: usize>(s: Seq<LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>>)
    requires
        forall|j: int| #![trigger s.spec_index(j)] 0 <= j < s.len() ==> s.spec_index(j).view().linked_list.view().len() == 0,
    ensures
        s.fold_left(0int, |sum: int, c: LockCell<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + c.view().linked_list.len() }) == 0,
    decreases s.len(),
{
    if s.len() != 0 {
        empty_caches_implies_cache_len_fold_zero(s.drop_last());
    }
}
}
