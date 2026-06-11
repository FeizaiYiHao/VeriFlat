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

    // -------- global_poll borrows --------

    /// Shared borrow into the global pool of the allocator at `alloc_ptr`.
    /// Caller holds either a read or a write lock on `global_poll`.
    pub fn borrow_global_poll<'a>(&'a self, alloc_ptr: usize, lp: Tracked<&'a LockPerm>) -> (ret: &'a crate::linkedlist::spec_impl::LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            self[alloc_ptr].global_poll.is_init(),
            lp@.state() is WriteLock ==> self[alloc_ptr].global_poll.write_lock_perm_match(lp@),
            lp@.state() is ReadLock ==> self[alloc_ptr].global_poll.read_lock_perm_match(lp@),
        ensures
            *ret == self[alloc_ptr].global_poll.view(),
    {
        let alloc = self.borrow(alloc_ptr);
        alloc.global_poll.borrow(lp)
    }

    /// Mutably borrow the global pool of the allocator at `alloc_ptr`.
    /// Caller must hold a write lock on `global_poll`.
    pub fn borrow_mut_global_poll<'a>(&'a mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut crate::linkedlist::spec_impl::LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self)[alloc_ptr].global_poll.wlocked_by(lctx),
            old(self)[alloc_ptr].global_poll.is_init(),

            lp@.state() is WriteLock,
            lp@.thread_id() == lctx.thread_id(),
            lp@.lock_id() == old(self)[alloc_ptr].global_poll.locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].global_poll.is_init(),
            // global_poll's lock perm and rodata/ghost are unchanged.
            final(self)[alloc_ptr].global_poll.view_rodata() == old(self)[alloc_ptr].global_poll.view_rodata(),
            final(self)[alloc_ptr].global_poll.view_kernel_ghost() == old(self)[alloc_ptr].global_poll.view_kernel_ghost(),
            final(self)[alloc_ptr].global_poll.view_user_ghost() == old(self)[alloc_ptr].global_poll.view_user_ghost(),
            final(self)[alloc_ptr].global_poll.locking_thread() == old(self)[alloc_ptr].global_poll.locking_thread(),
            final(self)[alloc_ptr].global_poll.being_killed() == old(self)[alloc_ptr].global_poll.being_killed(),
            // Other PageAllocator-side fields unchanged.
            final(self)[alloc_ptr].cpu_caches == old(self)[alloc_ptr].cpu_caches,
            final(self)[alloc_ptr].quota == old(self)[alloc_ptr].quota,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            // The `&mut LinkedList` ⇄ inner-value linkage.
            *ret == old(self)[alloc_ptr].global_poll.view(),
            final(self)[alloc_ptr].global_poll.view() == *final(ret),
            // Other map entries untouched.
            forall|k:usize| #![auto] old(self).dom().contains(k) && k != alloc_ptr ==> final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.global_poll.borrow_mut(Tracked(lctx), lp)
    }

    // -------- per-cpu cache borrows --------

    /// Shared borrow into the per-cpu cache `cpu_caches[cpu_id]` of the
    /// allocator at `alloc_ptr`. Caller holds a read or write lock on it.
    pub fn borrow_cache<'a>(&'a self, alloc_ptr: usize, cpu_id: CpuId, lp: Tracked<&'a LockPerm>) -> (ret: &'a crate::allocator::pre_cpu_cache::AllocatorCache)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            cpu_id_valid(cpu_id),
            lp@.state() is WriteLock ==> self[alloc_ptr].cpu_caches[cpu_id]@.write_lock_perm_match(lp@),
            lp@.state() is ReadLock ==> self[alloc_ptr].cpu_caches[cpu_id]@.read_lock_perm_match(lp@),
            self[alloc_ptr].cpu_caches.inv(),
        ensures
            *ret == self[alloc_ptr].cpu_caches[cpu_id]@@,
    {
        let alloc = self.borrow(alloc_ptr);
        alloc.cpu_caches.borrow(cpu_id, lp)
    }

    /// Mutably borrow the per-cpu cache `cpu_caches[cpu_id]` of the allocator
    /// at `alloc_ptr`. Caller must hold a write lock on it.
    pub fn borrow_mut_cache<'a>(&'a mut self, alloc_ptr: usize, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut crate::allocator::pre_cpu_cache::AllocatorCache)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            cpu_id_valid(cpu_id),
            old(self)[alloc_ptr].cpu_caches.inv(),
            old(self)[alloc_ptr].cpu_caches[cpu_id]@.wlocked_by(lctx),
            old(self)[alloc_ptr].cpu_caches[cpu_id]@.is_init(),

            lp@.state() is WriteLock,
            lp@.thread_id() == lctx.thread_id(),
            lp@.lock_id() == old(self)[alloc_ptr].cpu_caches[cpu_id]@.locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].cpu_caches.inv(),
            // Touched cache's lock state is preserved.
            final(self)[alloc_ptr].cpu_caches[cpu_id]@.is_init(),
            final(self)[alloc_ptr].cpu_caches[cpu_id]@.view_rodata() == old(self)[alloc_ptr].cpu_caches[cpu_id]@.view_rodata(),
            final(self)[alloc_ptr].cpu_caches[cpu_id]@.view_kernel_ghost() == old(self)[alloc_ptr].cpu_caches[cpu_id]@.view_kernel_ghost(),
            final(self)[alloc_ptr].cpu_caches[cpu_id]@.view_user_ghost() == old(self)[alloc_ptr].cpu_caches[cpu_id]@.view_user_ghost(),
            final(self)[alloc_ptr].cpu_caches[cpu_id]@.locking_thread() == old(self)[alloc_ptr].cpu_caches[cpu_id]@.locking_thread(),
            final(self)[alloc_ptr].cpu_caches[cpu_id]@.being_killed() == old(self)[alloc_ptr].cpu_caches[cpu_id]@.being_killed(),
            // Other cache entries in this allocator unchanged.
            final(self)[alloc_ptr].cpu_caches.unchanged_except(&old(self)[alloc_ptr].cpu_caches, cpu_id),
            // Other PageAllocator-side fields unchanged.
            final(self)[alloc_ptr].global_poll == old(self)[alloc_ptr].global_poll,
            final(self)[alloc_ptr].quota == old(self)[alloc_ptr].quota,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            // The `&mut AllocatorCache` ⇄ inner-value linkage.
            *ret == old(self)[alloc_ptr].cpu_caches[cpu_id]@@,
            final(self)[alloc_ptr].cpu_caches[cpu_id]@@ == *final(ret),
            // Other map entries untouched.
            forall|k:usize| #![auto] old(self).dom().contains(k) && k != alloc_ptr ==> final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.cpu_caches.borrow_mut(cpu_id, Tracked(lctx), lp)
    }

    // ====================================================================
    // Field-level lock / unlock helpers at the map level.
    //
    // Each routes `borrow_mut(alloc_ptr)` into the corresponding
    // `PageAllocator` field lock helper and frames the rest of the map
    // (domain, other entries) plus this allocator's untouched fields.
    // The `lctx.lock_map` obligations (acyclic / fresh on acquire; matching
    // key on release) flow straight through from the `PageAllocator`
    // helpers.
    // ====================================================================

    /// Acquire the quota lock of the allocator at `alloc_ptr`.
    pub fn wlock_quota(&mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self)[alloc_ptr].wf(),
            wlock_requires(old(self)[alloc_ptr].quota, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self)[alloc_ptr].quota@.container_depth(),
                process: old(self)[alloc_ptr].quota@.process_depth(),
                major: old(self)[alloc_ptr].quota@.current_lock_major(),
                minor: old(self)[alloc_ptr].quota@.lock_minor(),
            }),
            old(lctx).obj_id_fresh(KernelObjId::AllocatorQuota(page_size@, alloc_ptr)),
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].wf(),
            wlock_ensures(old(self)[alloc_ptr].quota, final(self)[alloc_ptr].quota, LockId{
                container: old(self)[alloc_ptr].quota@.container_depth(),
                process: old(self)[alloc_ptr].quota@.process_depth(),
                major: old(self)[alloc_ptr].quota@.current_lock_major(),
                minor: old(self)[alloc_ptr].quota@.lock_minor(),
            }, final(lctx).thread_id(), ret@),
            lock_ensures(old(lctx), final(lctx), final(self)[alloc_ptr].quota.view(), LockId{
                container: old(self)[alloc_ptr].quota@.container_depth(),
                process: old(self)[alloc_ptr].quota@.process_depth(),
                major: old(self)[alloc_ptr].quota@.current_lock_major(),
                minor: old(self)[alloc_ptr].quota@.lock_minor(),
            }, KernelObjId::AllocatorQuota(page_size@, alloc_ptr)),
            // This allocator's other fields untouched.
            final(self)[alloc_ptr].cpu_caches == old(self)[alloc_ptr].cpu_caches,
            final(self)[alloc_ptr].global_poll == old(self)[alloc_ptr].global_poll,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            // Other map entries untouched.
            forall|k:usize| #![auto] old(self).dom().contains(k) && k != alloc_ptr ==> final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wlock_quota(Tracked(lctx), page_size, Ghost(alloc_ptr))
    }

    /// Release the quota lock of the allocator at `alloc_ptr`.
    pub fn wunlock_quota(&mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self)[alloc_ptr].wf(),
            old(self)[alloc_ptr].quota.wlocked_by(old(lctx)),
            old(self)[alloc_ptr].quota.inv(),
            unlock_requires::<crate::allocator::allocator_quota::AllocatorQuota>(old(lctx)),
            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[alloc_ptr].quota.locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorQuota(page_size@, alloc_ptr)),
            old(lctx).lock_map()[KernelObjId::AllocatorQuota(page_size@, alloc_ptr)] == lock_perm@.lock_id(),
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].wf(),
            wunlock_ensures(old(self)[alloc_ptr].quota, final(self)[alloc_ptr].quota),
            unlock_ensures(old(lctx), final(lctx), final(self)[alloc_ptr].quota.view(), lock_perm@.lock_id(), KernelObjId::AllocatorQuota(page_size@, alloc_ptr)),
            final(self)[alloc_ptr].cpu_caches == old(self)[alloc_ptr].cpu_caches,
            final(self)[alloc_ptr].global_poll == old(self)[alloc_ptr].global_poll,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            forall|k:usize| #![auto] old(self).dom().contains(k) && k != alloc_ptr ==> final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wunlock_quota(Tracked(lctx), lock_perm, page_size, Ghost(alloc_ptr))
    }

    /// Acquire the global-pool lock of the allocator at `alloc_ptr`.
    pub fn wlock_global_poll(&mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self)[alloc_ptr].wf(),
            wlock_requires(old(self)[alloc_ptr].global_poll, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self)[alloc_ptr].global_poll@.container_depth(),
                process: old(self)[alloc_ptr].global_poll@.process_depth(),
                major: old(self)[alloc_ptr].global_poll@.current_lock_major(),
                minor: old(self)[alloc_ptr].global_poll@.lock_minor(),
            }),
            old(lctx).obj_id_fresh(KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr)),
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].wf(),
            wlock_ensures(old(self)[alloc_ptr].global_poll, final(self)[alloc_ptr].global_poll, LockId{
                container: old(self)[alloc_ptr].global_poll@.container_depth(),
                process: old(self)[alloc_ptr].global_poll@.process_depth(),
                major: old(self)[alloc_ptr].global_poll@.current_lock_major(),
                minor: old(self)[alloc_ptr].global_poll@.lock_minor(),
            }, final(lctx).thread_id(), ret@),
            lock_ensures(old(lctx), final(lctx), final(self)[alloc_ptr].global_poll.view(), LockId{
                container: old(self)[alloc_ptr].global_poll@.container_depth(),
                process: old(self)[alloc_ptr].global_poll@.process_depth(),
                major: old(self)[alloc_ptr].global_poll@.current_lock_major(),
                minor: old(self)[alloc_ptr].global_poll@.lock_minor(),
            }, KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr)),
            final(self)[alloc_ptr].cpu_caches == old(self)[alloc_ptr].cpu_caches,
            final(self)[alloc_ptr].quota == old(self)[alloc_ptr].quota,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            forall|k:usize| #![auto] old(self).dom().contains(k) && k != alloc_ptr ==> final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wlock_global_poll(Tracked(lctx), page_size, Ghost(alloc_ptr))
    }

    /// Release the global-pool lock of the allocator at `alloc_ptr`.
    pub fn wunlock_global_poll(&mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self)[alloc_ptr].wf(),
            old(self)[alloc_ptr].global_poll.wlocked_by(old(lctx)),
            old(self)[alloc_ptr].global_poll.inv(),
            unlock_requires::<crate::linkedlist::spec_impl::LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>>(old(lctx)),
            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[alloc_ptr].global_poll.locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr)),
            old(lctx).lock_map()[KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr)] == lock_perm@.lock_id(),
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].wf(),
            wunlock_ensures(old(self)[alloc_ptr].global_poll, final(self)[alloc_ptr].global_poll),
            unlock_ensures(old(lctx), final(lctx), final(self)[alloc_ptr].global_poll.view(), lock_perm@.lock_id(), KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr)),
            final(self)[alloc_ptr].cpu_caches == old(self)[alloc_ptr].cpu_caches,
            final(self)[alloc_ptr].quota == old(self)[alloc_ptr].quota,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            forall|k:usize| #![auto] old(self).dom().contains(k) && k != alloc_ptr ==> final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wunlock_global_poll(Tracked(lctx), lock_perm, page_size, Ghost(alloc_ptr))
    }

    /// Acquire the per-cpu cache lock of the allocator at `alloc_ptr`.
    pub fn wlock_cache(&mut self, alloc_ptr: usize, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self)[alloc_ptr].wf(),
            cpu_id_valid(cpu_id),
            wlock_requires(old(self)[alloc_ptr].cpu_caches[cpu_id]@, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self)[alloc_ptr].cpu_caches[cpu_id].container_depth(),
                process: old(self)[alloc_ptr].cpu_caches[cpu_id].process_depth(),
                major: old(self)[alloc_ptr].cpu_caches[cpu_id]@@.current_lock_major(),
                minor: old(self)[alloc_ptr].cpu_caches[cpu_id].lock_minor(),
            }),
            old(lctx).obj_id_fresh(KernelObjId::AllocatorCache(page_size@, alloc_ptr, cpu_id)),
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].wf(),
            wlock_ensures(old(self)[alloc_ptr].cpu_caches[cpu_id]@, final(self)[alloc_ptr].cpu_caches[cpu_id]@, LockId{
                container: old(self)[alloc_ptr].cpu_caches[cpu_id].container_depth(),
                process: old(self)[alloc_ptr].cpu_caches[cpu_id].process_depth(),
                major: old(self)[alloc_ptr].cpu_caches[cpu_id]@@.current_lock_major(),
                minor: old(self)[alloc_ptr].cpu_caches[cpu_id].lock_minor(),
            }, final(lctx).thread_id(), ret@),
            lock_ensures(old(lctx), final(lctx), final(self)[alloc_ptr].cpu_caches[cpu_id]@@, LockId{
                container: old(self)[alloc_ptr].cpu_caches[cpu_id].container_depth(),
                process: old(self)[alloc_ptr].cpu_caches[cpu_id].process_depth(),
                major: old(self)[alloc_ptr].cpu_caches[cpu_id]@@.current_lock_major(),
                minor: old(self)[alloc_ptr].cpu_caches[cpu_id].lock_minor(),
            }, KernelObjId::AllocatorCache(page_size@, alloc_ptr, cpu_id)),
            final(self)[alloc_ptr].cpu_caches.unchanged_except(&old(self)[alloc_ptr].cpu_caches, cpu_id),
            final(self)[alloc_ptr].global_poll == old(self)[alloc_ptr].global_poll,
            final(self)[alloc_ptr].quota == old(self)[alloc_ptr].quota,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            forall|k:usize| #![auto] old(self).dom().contains(k) && k != alloc_ptr ==> final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wlock_cache(cpu_id, Tracked(lctx), page_size, Ghost(alloc_ptr))
    }

    /// Release the per-cpu cache lock of the allocator at `alloc_ptr`.
    /// Caller must have restored the cache's length to match the recorded
    /// `differential` entry (see `PageAllocator::wunlock_cache`).
    pub fn wunlock_cache(&mut self, alloc_ptr: usize, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self)[alloc_ptr].wf(),
            cpu_id_valid(cpu_id),
            old(self)[alloc_ptr].cpu_caches[cpu_id]@.wlocked_by(old(lctx)),
            old(self)[alloc_ptr].cpu_caches[cpu_id]@.being_killed() == false,
            old(self)[alloc_ptr].cpu_caches[cpu_id]@.view().linked_list.len()
                == old(self)[alloc_ptr].differential@[cpu_id as int],
            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self)[alloc_ptr].cpu_caches[cpu_id]@.locking_thread()->Write_lock_id,
            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorCache(page_size@, alloc_ptr, cpu_id)),
            old(lctx).lock_map()[KernelObjId::AllocatorCache(page_size@, alloc_ptr, cpu_id)] == lock_perm@.lock_id(),
        ensures
            final(self).perms_wf(),
            final(self).dom() == old(self).dom(),
            final(self)[alloc_ptr].wf(),
            wunlock_ensures(old(self)[alloc_ptr].cpu_caches[cpu_id]@, final(self)[alloc_ptr].cpu_caches[cpu_id]@),
            unlock_ensures(old(lctx), final(lctx), final(self)[alloc_ptr].cpu_caches[cpu_id]@@, lock_perm@.lock_id(), KernelObjId::AllocatorCache(page_size@, alloc_ptr, cpu_id)),
            final(self)[alloc_ptr].cpu_caches.unchanged_except(&old(self)[alloc_ptr].cpu_caches, cpu_id),
            final(self)[alloc_ptr].global_poll == old(self)[alloc_ptr].global_poll,
            final(self)[alloc_ptr].quota == old(self)[alloc_ptr].quota,
            final(self)[alloc_ptr].owning_container == old(self)[alloc_ptr].owning_container,
            final(self)[alloc_ptr].differential == old(self)[alloc_ptr].differential,
            final(self)[alloc_ptr].total_free_pages == old(self)[alloc_ptr].total_free_pages,
            forall|k:usize| #![auto] old(self).dom().contains(k) && k != alloc_ptr ==> final(self)[k] == old(self)[k],
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wunlock_cache(cpu_id, Tracked(lctx), lock_perm, page_size, Ghost(alloc_ptr))
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