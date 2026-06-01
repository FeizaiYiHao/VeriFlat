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

impl<T> UnLockedMap<usize, T>{
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

    pub fn borrow<'a>(&'a self, key: usize) -> (ret: &'a T)
        requires
            self.perms_wf(),
            self.dom().contains(key),
        ensures
            *ret == self[key],
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
            *ret == old(self)[key],
            final(self)[key] == *final(ret),
            forall|k:usize|
                #![auto]
                old(self).dom().contains(k) && k != key
                ==>
                final(self)[k] == old(self)[k],
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

/// Allocator-specific helpers on the unlocked map of allocators. Quota-specific
/// `borrow` / `borrow_mut` give direct read/write access to the
/// `AllocatorQuota` value protected by the inner RwLock — the caller must hold
/// the appropriate `LockPerm`.
impl UnLockedMap<usize, crate::allocator::page_allocator::PageAllocator>{
    /// Shared borrow into the quota of the allocator at `alloc_ptr`. Caller
    /// holds either a read or a write lock on `quota`.
    pub fn borrow_quota<'a>(&'a self, alloc_ptr: usize, lp: Tracked<&'a LockPerm>) -> (ret: &'a crate::allocator::allocator_quota::AllocatorQuota)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            self[alloc_ptr].quota.is_init(),
            lp@.state() is WriteLock ==> self[alloc_ptr].quota.write_lock_perm_match(lp@),
            lp@.state() is ReadLock ==> self[alloc_ptr].quota.read_lock_perm_match(lp@),
        ensures
            *ret == self[alloc_ptr].quota.view(),
    {
        let alloc = self.borrow(alloc_ptr);
        alloc.quota.borrow(lp)
    }

    /// Mutably borrow the quota of the allocator at `alloc_ptr`. Caller must
    /// hold a write lock on `quota`. Mutations through the returned reference
    /// are reflected in the map's value when the borrow ends.
    pub fn borrow_mut_quota<'a>(&'a mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut crate::allocator::allocator_quota::AllocatorQuota)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self)[alloc_ptr].quota.wlocked_by(lctx),
            old(self)[alloc_ptr].quota.is_init(),

            lp@.state() is WriteLock,
            lp@.thread_id() == lctx.thread_id(),
            lp@.lock_id() == old(self)[alloc_ptr].quota.locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].quota.is_init(),
            // Quota's lock perm and rodata/ghost are unchanged.
            final(self)[alloc_ptr].quota.view_rodata() == old(self)[alloc_ptr].quota.view_rodata(),
            final(self)[alloc_ptr].quota.view_kernel_ghost() == old(self)[alloc_ptr].quota.view_kernel_ghost(),
            final(self)[alloc_ptr].quota.view_user_ghost() == old(self)[alloc_ptr].quota.view_user_ghost(),
            final(self)[alloc_ptr].quota.locking_thread() == old(self)[alloc_ptr].quota.locking_thread(),
            final(self)[alloc_ptr].quota.being_killed() == old(self)[alloc_ptr].quota.being_killed(),
            // Quota's other PageAllocator-side fields are unchanged.
            final(self)[alloc_ptr].cpu_caches == old(self)[alloc_ptr].cpu_caches,
            final(self)[alloc_ptr].global_poll == old(self)[alloc_ptr].global_poll,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            // The `&mut AllocatorQuota` ⇄ inner-value linkage.
            *ret == old(self)[alloc_ptr].quota.view(),
            final(self)[alloc_ptr].quota.view() == *final(ret),
            // Other map entries untouched.
            forall|k:usize|
                #![auto]
                old(self).dom().contains(k) && k != alloc_ptr
                ==>
                final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.quota.borrow_mut(Tracked(lctx), lp)
    }
}


impl<T: LockRecursivelyLockedTrait + Step> Step for UnLockedMap<usize, T>{
    open spec fn random_step_spec(self, old:&Self, lctx: &LocalContext) -> bool{
        &&&
        forall|k:usize|
            #![auto]
            old.dom().contains(k) && old[k].partial_locked_by(lctx)
            ==>
            self.dom().contains(k) && self[k].random_step_spec(&old[k], lctx)
    }
    proof fn random_step(&mut self, lctx: &LocalContext)
    {
        admit()
    }
}

}