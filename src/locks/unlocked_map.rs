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
        forall|k:usize|
            #![trigger self.spec_index(k)]
            #![trigger old.spec_index(k)]
            old.dom().contains(k) && k != key
            ==>
            self.spec_index(k) == old.spec_index(k)
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
            old(self).perms_wf(),
            old(self).dom().contains(key),
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self).unchanged_except(old(self), key),
            *ret == old(self).spec_index(key),
            final(self).spec_index(key) == *final(ret),
            forall|k:usize|
                #![trigger final(self).spec_index(k)]
                #![trigger old(self).spec_index(k)]
                old(self).dom().contains(k) && k != key
                ==>
                final(self).spec_index(k) == old(self).spec_index(k),
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


impl<T: LockRecursivelyLockedTrait + Step> Step for UnLockedMap<usize, T>{
    open spec fn random_step_spec(self, old:&Self, lctx: &LocalContext) -> bool{
        &&&
        forall|k:usize|
            #![auto]
            old.dom().contains(k) && old.spec_index(k).partial_locked_by(lctx)
            ==>
            self.dom().contains(k) && self.spec_index(k).random_step_spec(&old.spec_index(k), lctx)
    }
    proof fn random_step(&mut self, lctx: &LocalContext)
    {
        admit()
    }
}

}
