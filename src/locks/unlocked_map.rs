use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
verus! {
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
pub struct UnLockedMap<K, T>{
    map: Tracked<Map<K, PointsTo<T>>>,
}

impl<T> UnLockedMap<usize, T>{
    pub fn new_empty() -> (ret: Self)
        ensures
            ret.perms_wf(),
            ret.dom() =~= Set::<usize>::empty(),
    {
        Self {
            map: Tracked(Map::<usize, PointsTo<T>>::tracked_empty()),
        }
    }

    pub closed spec fn view(&self) -> Map<usize, PointsTo<T>>{
        self.map.view()
    }
    // pub closed spec fn user_view(&self) -> Map<usize, >
    pub open spec fn dom(&self) -> Set<usize>{
        self.view().dom()
    }
    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|k:usize|
            // #![trigger self.view().spec_index(k).is_init()]
            // #![trigger self.view().spec_index(k).addr()]
            #![trigger self.view().dom().contains(k)]
            self.view().dom().contains(k)
            ==>
            {
                &&&
                self.view().spec_index(k).is_init()
                &&&
                self.view().spec_index(k).addr() == k
            }
    }
    pub open spec fn spec_index(&self, key: usize) -> T
        recommends
            self.view().dom().contains(key),
    {
        self.view().spec_index(key).value()
    }
    pub open spec fn unchanged_except(&self, old: &Self, key:usize) -> bool{
        &&&
        old.dom() == self.dom()
        &&&
        self.dom().contains(key)
        &&&
        forall|k:usize|
            #![trigger self.spec_index(k)]
            #![trigger old.spec_index(k)]
            old.dom().contains(k) && k != key
            ==>
            self.spec_index(k) == old.spec_index(k)
    }

    pub fn insert_with_perm(
        &mut self,
        key: usize,
        Tracked(perm): Tracked<PointsTo<T>>,
    )
        requires
            !old(self).dom().contains(key),
            perm.is_init(),
            perm.addr() == key,
        ensures
            old(self).perms_wf() ==> final(self).perms_wf(),
            final(self).dom() =~= old(self).dom().insert(key),
            final(self).dom().contains(key),
            final(self).spec_index(key) == perm.value(),
            forall|old_key: usize| #![auto]
                old(self).dom().contains(old_key)
                ==> final(self).spec_index(old_key)
                    == old(self).spec_index(old_key),
    {
        proof { self.map.borrow_mut().tracked_insert(key, perm); }
    }

    pub fn borrow<'a>(&'a self, key: usize) -> (ret: &'a T)
        requires
            self.perms_wf(),
            self.dom().contains(key),
        ensures
            *ret == self.spec_index(key),
    {
        let tracked perm = self.map.borrow().tracked_borrow(key);
        PPtr::<T>::from_usize(key).borrow(Tracked(perm))
    }

    pub fn borrow_mut<'a>(&'a mut self, key: usize) -> (ret: &'a mut T)
        requires
            old(self).dom().contains(key),
            old(self).view().spec_index(key).is_init(),
            old(self).view().spec_index(key).addr() == key,
        ensures
            old(self).perms_wf() ==> final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self).unchanged_except(old(self), key),
            *ret == old(self).spec_index(key),
            final(self).spec_index(key) == *final(ret),
    {
        let tracked perm = self.map.borrow_mut().tracked_borrow_mut(key);
        PPtr::<T>::from_usize(key).borrow_mut(Tracked(perm))
    }

    // pub fn take(&mut self, key:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret:T)
    //     requires
    //         // old(self).perms_wf(),
    //         old(self).dom().contains(key),
    //         old(self)[key].is_init(),
    //     ensures
    //         self.perms_wf(),
    //         self.unchanged_except(old(self), key),

    //         self[key].is_init() == false,
    //         ret == old(self)[key].value(),
    // {
    //     let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
    //     let ret = PPtr::<T>::from_usize(key).take(Tracked(&mut perm));
    //     proof{
    //         self.map.borrow_mut().tracked_insert(key, perm);
    //     }
    //     return ret;
    // }

    // pub fn put(&mut self, key:usize, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>, v:T)
    //     requires
    //         old(self).perms_wf(),
    //         old(self).dom().contains(key),
    //         old(self)[key].is_init() == false,
    //     ensures
    //         self.perms_wf(),
    //         self.unchanged_except(old(self), key),

    //         self[key].is_init(),
    //         v == self[key].value(),
    // {
    //     let tracked mut perm = self.map.borrow_mut().tracked_remove(key);
    //     PPtr::<T>::from_usize(key).put(Tracked(&mut perm), v);
    //     proof{
    //         self.map.borrow_mut().tracked_insert(key, perm);
    //     }
    // }
}
}
