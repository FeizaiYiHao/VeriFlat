use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::define::*;
use super::*;
use crate::concurrency::*;
verus! {


#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(T)]
pub struct UnLockedMap<K, T>{
    map: Tracked<Map<K, PointsTo<T>>>,
}

impl<T,> UnLockedMap<usize, T>{
    pub closed spec fn view(&self) -> Map<usize, PointsTo<T>>{
        self.map@
    }
    // pub closed spec fn user_view(&self) -> Map<usize, >
    pub open spec fn dom(&self) -> Set<usize>{
        self@.dom()
    }
    pub open spec fn perms_wf(&self) -> bool {
        &&&
        forall|k:usize| 
            #![trigger self@[k].is_init()]
            #![trigger self@[k].addr()]
            self@.dom().contains(k)
            ==>
            { 
                &&&
                self@[k].is_init()
                &&&
                self@[k].addr() == k
            }
    }
    pub open spec fn spec_index(&self, key: usize) -> T
        recommends
            self@.dom().contains(key),
    {
        self@[key].value()
    }
    pub open spec fn unchanged_except(&self, old: &Self, key:usize) -> bool{
        &&&
        old.dom() == self.dom()
        &&&
        forall|k:usize|
            #![auto]
            old.dom().contains(k) && k != key
            ==>
            self[k] == old[k]
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

impl<T: LockRecursivelyLockedTrait> Step for UnLockedMap<usize, T>{
    open spec fn random_step_spec(self, old:&Self, lctx: &LocalContext) -> bool{
        &&&
        forall|k:usize|
            #![auto]
            old.dom().contains(k) && old[k].partial_locked_by(lctx)
            ==>
            self.dom().contains(k) && self[k] =~= old[k]
    }
    proof fn random_step(&mut self, lctx: &LocalContext)
    {
        admit()
    }
}

}