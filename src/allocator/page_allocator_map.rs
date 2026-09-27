use vstd::prelude::*;
use vstd::simple_pptr::*;
use crate::*;

verus! {
/// Approved TCB boundary: consume one owned 4K page permission and initialize
/// that physical page as a `PageAllocator`. Keep the raw retype private; callers
/// use `retype_page_to_allocator_and_insert`.
#[verifier::external_body]
fn retype_4k_page_perm_to_allocator(
    page_ptr: PagePtr,
    allocator: PageAllocator,
    Tracked(page_perm): Tracked<PagePerm4k>,
) -> (ret: Tracked<PointsTo<PageAllocator>>)
    requires
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
        allocator.inv(),
    ensures
        ret.view().is_init(),
        ret.view().addr() == page_ptr,
        ret.view().value() == allocator,
{
    unsafe {
        (page_ptr as *mut PageAllocator).write(allocator);
    }
    Tracked::assume_new()
}

impl UnLockedMap<usize, PageAllocator> {
    pub fn retype_page_to_allocator_and_insert(
        &mut self,
        page_ptr: PagePtr,
        allocator: PageAllocator,
        Tracked(page_perm): Tracked<PagePerm4k>,
    )
        requires
            old(self).perms_wf(),
            !old(self).dom().contains(page_ptr),
            page_perm.is_init(),
            page_perm.addr() == page_ptr,
            allocator.inv(),
        ensures
            final(self).perms_wf(),
            final(self).dom() =~= old(self).dom().insert(page_ptr),
            final(self).dom().contains(page_ptr),
            final(self).spec_index(page_ptr) == allocator,
            forall|ptr: RwLockPageAllocatorPtr|
                #![trigger final(self).spec_index(ptr)]
                #![trigger old(self).spec_index(ptr)]
                #![trigger old(self).dom().contains(ptr)]
                #![trigger final(self).dom().contains(ptr)]
                old(self).dom().contains(ptr) ==> {
                    &&& final(self).dom().contains(ptr)
                    &&& final(self).spec_index(ptr) == old(self).spec_index(ptr)
                },
    {
        let Tracked(allocator_perm) = retype_4k_page_perm_to_allocator(page_ptr, allocator, Tracked(page_perm));
        self.insert_with_perm(page_ptr, Tracked(allocator_perm));
    }

    #[verifier::opaque]
    pub open spec fn typed_quota_lock_map_aligned(
        &self,
        held_locks: Map<RwLockPageAllocatorPtr, TypedHeldLock>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|ptr: RwLockPageAllocatorPtr|
            #![trigger held_locks.dom().contains(ptr)]
            #![trigger self.spec_index(ptr).quota.locked_by_thread(thread_id)]
            held_locks.dom().contains(ptr) == {
                &&& self.dom().contains(ptr)
                &&& self.spec_index(ptr).quota.locked_by_thread(thread_id)
            }
            && (held_locks.dom().contains(ptr) ==>
                held_locks.index(ptr).lock_id == self.spec_index(ptr).quota.lock_id()))
        &&& (forall|ptr: RwLockPageAllocatorPtr|
            #![trigger typed_lock_map_contains_mode(held_locks, ptr, TypedLockMode::Read)]
            #![trigger self.spec_index(ptr).quota.rlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, ptr, TypedLockMode::Read) == {
                &&& self.dom().contains(ptr)
                &&& self.spec_index(ptr).quota.rlocked_by_thread(thread_id)
            })
        &&& (forall|ptr: RwLockPageAllocatorPtr|
            #![trigger typed_lock_map_contains_mode(held_locks, ptr, TypedLockMode::Write)]
            #![trigger self.spec_index(ptr).quota.wlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, ptr, TypedLockMode::Write) == {
                &&& self.dom().contains(ptr)
                &&& self.spec_index(ptr).quota.wlocked_by_thread(thread_id)
            })
    }

    #[verifier::opaque]
    pub open spec fn typed_cache_lock_map_aligned(
        &self,
        held_locks: Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
            #![trigger held_locks.dom().contains((ptr, cpu_id))]
            #![trigger self.spec_index(ptr).cpu_caches.spec_index(cpu_id).view().locked_by_thread(thread_id)]
            held_locks.dom().contains((ptr, cpu_id)) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).cpu_caches.spec_index(cpu_id).view().locked_by_thread(thread_id)
            }
            && (held_locks.dom().contains((ptr, cpu_id)) ==>
                held_locks.index((ptr, cpu_id)).lock_id == self.spec_index(ptr).cpu_caches.lock_id_by_index(cpu_id)))
        &&& (forall|ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
            #![trigger typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Read)]
            #![trigger self.spec_index(ptr).cpu_caches.spec_index(cpu_id).view().rlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Read) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).cpu_caches.spec_index(cpu_id).view().rlocked_by_thread(thread_id)
            })
        &&& (forall|ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
            #![trigger typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Write)]
            #![trigger self.spec_index(ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, (ptr, cpu_id), TypedLockMode::Write) == {
                &&& self.dom().contains(ptr)
                &&& index_valid(NUM_CPUS, cpu_id)
                &&& self.spec_index(ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by_thread(thread_id)
            })
    }

    #[verifier::opaque]
    pub open spec fn typed_global_pool_lock_map_aligned(
        &self,
        held_locks: Map<RwLockPageAllocatorPtr, TypedHeldLock>,
        thread_id: LockThreadId,
    ) -> bool {
        &&& (forall|ptr: RwLockPageAllocatorPtr|
            #![trigger held_locks.dom().contains(ptr)]
            #![trigger self.spec_index(ptr).global_pool.locked_by_thread(thread_id)]
            held_locks.dom().contains(ptr) == {
                &&& self.dom().contains(ptr)
                &&& self.spec_index(ptr).global_pool.locked_by_thread(thread_id)
            }
            && (held_locks.dom().contains(ptr) ==>
                held_locks.index(ptr).lock_id == self.spec_index(ptr).global_pool.lock_id()))
        &&& (forall|ptr: RwLockPageAllocatorPtr|
            #![trigger typed_lock_map_contains_mode(held_locks, ptr, TypedLockMode::Read)]
            #![trigger self.spec_index(ptr).global_pool.rlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, ptr, TypedLockMode::Read) == {
                &&& self.dom().contains(ptr)
                &&& self.spec_index(ptr).global_pool.rlocked_by_thread(thread_id)
            })
        &&& (forall|ptr: RwLockPageAllocatorPtr|
            #![trigger typed_lock_map_contains_mode(held_locks, ptr, TypedLockMode::Write)]
            #![trigger self.spec_index(ptr).global_pool.wlocked_by_thread(thread_id)]
            typed_lock_map_contains_mode(held_locks, ptr, TypedLockMode::Write) == {
                &&& self.dom().contains(ptr)
                &&& self.spec_index(ptr).global_pool.wlocked_by_thread(thread_id)
            })
    }

    pub fn borrow_quota<'a>(&'a self, alloc_ptr: usize, lp: Tracked<&'a LockPerm>) -> (ret: &'a AllocatorQuota)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            self.spec_index(alloc_ptr).quota.is_init(),
            lp.view().state() is WriteLock ==> self.spec_index(alloc_ptr).quota.write_lock_perm_match(lp.view()),
            lp.view().state() is ReadLock ==> self.spec_index(alloc_ptr).quota.read_lock_perm_match(lp.view()),
        ensures
            *ret == self.spec_index(alloc_ptr).quota.view(),
    {
        let alloc = self.borrow(alloc_ptr);
        alloc.quota.borrow(lp)
    }

    pub fn borrow_quota_typed<'a>(
        &'a self, alloc_ptr: usize,
        Ghost(held_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lock_perm: Tracked<&'a LockPerm>,
    ) -> (ret: &'a AllocatorQuota)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            self.spec_index(alloc_ptr).quota.is_init(),
            self.typed_quota_lock_map_aligned(held_locks, lctx.thread_id()),
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().state() is WriteLock ==> typed_lock_map_contains_mode(held_locks, alloc_ptr, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock ==> lock_perm.view().lock_id() == self.spec_index(alloc_ptr).quota.locking_thread()->Write_lock_id,
            lock_perm.view().state() is ReadLock ==> typed_lock_map_contains_mode(held_locks, alloc_ptr, TypedLockMode::Read),
            lock_perm.view().state() is ReadLock ==> self.spec_index(alloc_ptr).quota.locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), lock_perm.view().lock_id()),
        ensures
            *ret == self.spec_index(alloc_ptr).quota.view(),
    {
        assert({
            &&& lock_perm.view().state() is WriteLock ==> self.spec_index(alloc_ptr).quota.write_lock_perm_match(lock_perm.view())
            &&& lock_perm.view().state() is ReadLock ==> self.spec_index(alloc_ptr).quota.read_lock_perm_match(lock_perm.view())
        }) by { reveal(UnLockedMap::typed_quota_lock_map_aligned); };
        self.borrow_quota(alloc_ptr, lock_perm)
    }

    pub fn borrow_mut_quota<'a>(&'a mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut AllocatorQuota)
        requires
            old(self).dom().contains(alloc_ptr),
            old(self).view().spec_index(alloc_ptr).is_init(),
            old(self).view().spec_index(alloc_ptr).addr() == alloc_ptr,
            old(self).spec_index(alloc_ptr).quota.wlocked_by(lctx),
            old(self).spec_index(alloc_ptr).quota.is_init(),

            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).spec_index(alloc_ptr).quota.locking_thread()->Write_lock_id,
        ensures
            old(self).perms_wf() ==> final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).quota.is_init(),
            final(self).spec_index(alloc_ptr).quota.wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).quota.write_lock_perm_match(lp.view()),
            // Quota's lock perm and rodata/ghost are unchanged.
            final(self).spec_index(alloc_ptr).quota.view_rodata() == old(self).spec_index(alloc_ptr).quota.view_rodata(),
            final(self).spec_index(alloc_ptr).quota.view_ghost() == old(self).spec_index(alloc_ptr).quota.view_ghost(),
            final(self).spec_index(alloc_ptr).quota.locking_thread() == old(self).spec_index(alloc_ptr).quota.locking_thread(),
            final(self).spec_index(alloc_ptr).quota.being_killed() == old(self).spec_index(alloc_ptr).quota.being_killed(),
            // Quota's other PageAllocator-side fields are unchanged.
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
            // The `&mut AllocatorQuota` ⇄ inner-value linkage.
            *ret == old(self).spec_index(alloc_ptr).quota.view(),
            final(self).spec_index(alloc_ptr).quota.view() == *final(ret),
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.quota.borrow_mut(Tracked(lctx), lp)
    }

    pub fn borrow_mut_quota_typed<'a>(
        &'a mut self,
        alloc_ptr: usize,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(global_pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lp: Tracked<&'a LockPerm>,
    ) -> (ret: &'a mut AllocatorQuota)
        requires
            old(self).perms_wf(),
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
            old(self).spec_index(alloc_ptr).quota.is_init(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(quota_locks, alloc_ptr, TypedLockMode::Write),
            lp.view().lock_id() == old(self).spec_index(alloc_ptr).quota.locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).quota.is_init(),
            final(self).spec_index(alloc_ptr).quota.wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).quota.write_lock_perm_match(lp.view()),
            final(self).spec_index(alloc_ptr).quota.view_rodata() == old(self).spec_index(alloc_ptr).quota.view_rodata(),
            final(self).spec_index(alloc_ptr).quota.view_ghost() == old(self).spec_index(alloc_ptr).quota.view_ghost(),
            final(self).spec_index(alloc_ptr).quota.locking_thread() == old(self).spec_index(alloc_ptr).quota.locking_thread(),
            final(self).spec_index(alloc_ptr).quota.being_killed() == old(self).spec_index(alloc_ptr).quota.being_killed(),
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
            *ret == old(self).spec_index(alloc_ptr).quota.view(),
            final(self).spec_index(alloc_ptr).quota.view() == *final(ret),
            final(self).typed_quota_lock_map_aligned(
                quota_locks.insert(alloc_ptr, TypedHeldLock {
                    lock_id: final(self).spec_index(alloc_ptr).quota.lock_id(),
                    mode: quota_locks.index(alloc_ptr).mode,
                }),
                lctx.thread_id(),
            ),
            final(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            final(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
            final(self).spec_index(alloc_ptr).quota.lock_id() == old(self).spec_index(alloc_ptr).quota.lock_id()
                ==> final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
    {
        proof {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        }
        self.borrow_mut_quota(alloc_ptr, Tracked(lctx), lp)
    }

    pub fn borrow_global_pool<'a>(&'a self, alloc_ptr: usize, lp: Tracked<&'a LockPerm>) -> (ret: &'a GlobalPool)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            self.spec_index(alloc_ptr).global_pool.is_init(),
            lp.view().state() is WriteLock ==> self.spec_index(alloc_ptr).global_pool.write_lock_perm_match(lp.view()),
            lp.view().state() is ReadLock ==> self.spec_index(alloc_ptr).global_pool.read_lock_perm_match(lp.view()),
        ensures
            *ret == self.spec_index(alloc_ptr).global_pool.view(),
    {
        let alloc = self.borrow(alloc_ptr);
        alloc.global_pool.borrow(lp)
    }

    pub fn borrow_global_pool_typed<'a>(
        &'a self, alloc_ptr: usize,
        Ghost(held_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lock_perm: Tracked<&'a LockPerm>,
    ) -> (ret: &'a GlobalPool)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            self.spec_index(alloc_ptr).global_pool.is_init(),
            self.typed_global_pool_lock_map_aligned(held_locks, lctx.thread_id()),
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().state() is WriteLock ==> typed_lock_map_contains_mode(held_locks, alloc_ptr, TypedLockMode::Write),
            lock_perm.view().state() is WriteLock ==> lock_perm.view().lock_id() == self.spec_index(alloc_ptr).global_pool.locking_thread()->Write_lock_id,
            lock_perm.view().state() is ReadLock ==> typed_lock_map_contains_mode(held_locks, alloc_ptr, TypedLockMode::Read),
            lock_perm.view().state() is ReadLock ==> self.spec_index(alloc_ptr).global_pool.locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), lock_perm.view().lock_id()),
        ensures
            *ret == self.spec_index(alloc_ptr).global_pool.view(),
    {
        assert({
            &&& lock_perm.view().state() is WriteLock ==> self.spec_index(alloc_ptr).global_pool.write_lock_perm_match(lock_perm.view())
            &&& lock_perm.view().state() is ReadLock ==> self.spec_index(alloc_ptr).global_pool.read_lock_perm_match(lock_perm.view())
        }) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
        self.borrow_global_pool(alloc_ptr, lock_perm)
    }

    pub fn borrow_mut_global_pool<'a>(&'a mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut GlobalPool)
        requires
            old(self).dom().contains(alloc_ptr),
            old(self).view().spec_index(alloc_ptr).is_init(),
            old(self).view().spec_index(alloc_ptr).addr() == alloc_ptr,
            old(self).spec_index(alloc_ptr).global_pool.wlocked_by(lctx),
            old(self).spec_index(alloc_ptr).global_pool.is_init(),

            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).spec_index(alloc_ptr).global_pool.locking_thread()->Write_lock_id,
        ensures
            old(self).perms_wf() ==> final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).global_pool.is_init(),
            final(self).spec_index(alloc_ptr).global_pool.wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).global_pool.write_lock_perm_match(lp.view()),
            // global_pool's lock perm and rodata/ghost are unchanged.
            final(self).spec_index(alloc_ptr).global_pool.view_rodata() == old(self).spec_index(alloc_ptr).global_pool.view_rodata(),
            final(self).spec_index(alloc_ptr).global_pool.view_ghost() == old(self).spec_index(alloc_ptr).global_pool.view_ghost(),
            final(self).spec_index(alloc_ptr).global_pool.locking_thread() == old(self).spec_index(alloc_ptr).global_pool.locking_thread(),
            final(self).spec_index(alloc_ptr).global_pool.being_killed() == old(self).spec_index(alloc_ptr).global_pool.being_killed(),
            // Other PageAllocator-side fields unchanged.
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
            // The `&mut LinkedList` ⇄ inner-value linkage.
            *ret == old(self).spec_index(alloc_ptr).global_pool.view(),
            final(self).spec_index(alloc_ptr).global_pool.view() == *final(ret),
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.global_pool.borrow_mut(Tracked(lctx), lp)
    }

    pub fn borrow_mut_global_pool_typed<'a>(
        &'a mut self,
        alloc_ptr: usize,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(global_pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lp: Tracked<&'a LockPerm>,
    ) -> (ret: &'a mut GlobalPool)
        requires
            old(self).perms_wf(),
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
            old(self).spec_index(alloc_ptr).global_pool.is_init(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(global_pool_locks, alloc_ptr, TypedLockMode::Write),
            lp.view().lock_id() == old(self).spec_index(alloc_ptr).global_pool.locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).global_pool.is_init(),
            final(self).spec_index(alloc_ptr).global_pool.wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).global_pool.write_lock_perm_match(lp.view()),
            final(self).spec_index(alloc_ptr).global_pool.view_rodata() == old(self).spec_index(alloc_ptr).global_pool.view_rodata(),
            final(self).spec_index(alloc_ptr).global_pool.view_ghost() == old(self).spec_index(alloc_ptr).global_pool.view_ghost(),
            final(self).spec_index(alloc_ptr).global_pool.locking_thread() == old(self).spec_index(alloc_ptr).global_pool.locking_thread(),
            final(self).spec_index(alloc_ptr).global_pool.being_killed() == old(self).spec_index(alloc_ptr).global_pool.being_killed(),
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
            *ret == old(self).spec_index(alloc_ptr).global_pool.view(),
            final(self).spec_index(alloc_ptr).global_pool.view() == *final(ret),
            final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            final(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            final(self).typed_global_pool_lock_map_aligned(
                global_pool_locks.insert(alloc_ptr, TypedHeldLock {
                    lock_id: final(self).spec_index(alloc_ptr).global_pool.lock_id(),
                    mode: global_pool_locks.index(alloc_ptr).mode,
                }),
                lctx.thread_id(),
            ),
    {
        proof {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        }
        self.borrow_mut_global_pool(alloc_ptr, Tracked(lctx), lp)
    }

    pub fn borrow_cache<'a>(&'a self, alloc_ptr: usize, cpu_id: CpuId, lp: Tracked<&'a LockPerm>) -> (ret: &'a AllocatorCache)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            index_valid(NUM_CPUS, cpu_id),
            self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().is_init(),
            lp.view().state() is WriteLock ==> self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().write_lock_perm_match(lp.view()),
            lp.view().state() is ReadLock ==> self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().read_lock_perm_match(lp.view()),
            self.spec_index(alloc_ptr).cpu_caches.inv(),
        ensures
            *ret == self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view(),
    {
        let alloc = self.borrow(alloc_ptr);
        alloc.cpu_caches.borrow(cpu_id, lp)
    }

    pub fn borrow_cache_typed<'a>(
        &'a self, alloc_ptr: usize, cpu_id: CpuId,
        Ghost(held_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lock_perm: Tracked<&'a LockPerm>,
    ) -> (ret: &'a AllocatorCache)
        requires
            self.perms_wf(),
            self.dom().contains(alloc_ptr),
            index_valid(NUM_CPUS, cpu_id),
            self.spec_index(alloc_ptr).cpu_caches.inv(),
            self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().is_init(),
            self.typed_cache_lock_map_aligned(held_locks, lctx.thread_id()),
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().state() is WriteLock ==> typed_lock_map_contains_mode(held_locks, (alloc_ptr, cpu_id), TypedLockMode::Write),
            lock_perm.view().state() is WriteLock ==> lock_perm.view().lock_id() == self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            lock_perm.view().state() is ReadLock ==> typed_lock_map_contains_mode(held_locks, (alloc_ptr, cpu_id), TypedLockMode::Read),
            lock_perm.view().state() is ReadLock ==> self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), lock_perm.view().lock_id()),
        ensures
            *ret == self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view(),
    {
        assert({
            &&& lock_perm.view().state() is WriteLock ==> self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().write_lock_perm_match(lock_perm.view())
            &&& lock_perm.view().state() is ReadLock ==> self.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().read_lock_perm_match(lock_perm.view())
        }) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        self.borrow_cache(alloc_ptr, cpu_id, lock_perm)
    }

    pub fn borrow_mut_cache<'a>(&'a mut self, alloc_ptr: usize, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>, lp: Tracked<&'a LockPerm>) -> (ret: &'a mut AllocatorCache)
        requires
            old(self).dom().contains(alloc_ptr),
            old(self).view().spec_index(alloc_ptr).is_init(),
            old(self).view().spec_index(alloc_ptr).addr() == alloc_ptr,
            index_valid(NUM_CPUS, cpu_id),
            old(self).spec_index(alloc_ptr).cpu_caches.inv(),
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().is_init(),

            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            lp.view().lock_id() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        ensures
            old(self).perms_wf() ==> final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).cpu_caches.inv(),
            // Touched cache's lock state is preserved.
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().is_init(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().write_lock_perm_match(lp.view()),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view_rodata() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view_ghost() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view_ghost(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed(),
            // Other cache entries in this allocator unchanged.
            final(self).spec_index(alloc_ptr).cpu_caches.entries_unchanged_except(&old(self).spec_index(alloc_ptr).cpu_caches, cpu_id),
            // Other PageAllocator-side fields unchanged.
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
            // The `&mut AllocatorCache` ⇄ inner-value linkage.
            *ret == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view() == *final(ret),
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.cpu_caches.borrow_mut(cpu_id, Tracked(lctx), lp)
    }

    pub fn borrow_mut_cache_typed<'a>(
        &'a mut self,
        alloc_ptr: usize,
        cpu_id: CpuId,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(global_pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lp: Tracked<&'a LockPerm>,
    ) -> (ret: &'a mut AllocatorCache)
        requires
            old(self).perms_wf(),
            old(self).spec_index(alloc_ptr).cpu_caches.inv(),
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().is_init(),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(cache_locks, (alloc_ptr, cpu_id), TypedLockMode::Write),
            lp.view().lock_id() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).cpu_caches.inv(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().is_init(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().write_lock_perm_match(lp.view()),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view_rodata() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view_rodata(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view_ghost() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view_ghost(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed(),
            final(self).spec_index(alloc_ptr).cpu_caches.entries_unchanged_except(&old(self).spec_index(alloc_ptr).cpu_caches, cpu_id),
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
            *ret == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view() == *final(ret),
            final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            final(self).typed_cache_lock_map_aligned(
                cache_locks.insert((alloc_ptr, cpu_id), TypedHeldLock {
                    lock_id: final(self).spec_index(alloc_ptr).cpu_caches.lock_id_by_index(cpu_id),
                    mode: cache_locks.index((alloc_ptr, cpu_id)).mode,
                }),
                lctx.thread_id(),
            ),
            final(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
    {
        proof {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        }
        self.borrow_mut_cache(alloc_ptr, cpu_id, Tracked(lctx), lp)
    }

    pub fn push_cache_page_typed(
        &mut self,
        alloc_ptr: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        node_addr: usize,
        node_perm: Tracked<PointsTo<Node<PagePtr>>>,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(global_pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(cache_locks, (alloc_ptr, cpu_id), TypedLockMode::Write),
            lock_perm.view().lock_id() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
            node_perm.view().is_init(),
            !old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(node_perm.view().value().view()),
            node_perm.view().addr() == node_addr,
            old(self).spec_index(alloc_ptr).total_free_pages.view() < usize::MAX,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().insert(0, node_perm.view().value().view()),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().map() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, node_perm.view().value().view()),
            !old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
            final(self).spec_index(alloc_ptr).total_free_pages.view() == old(self).spec_index(alloc_ptr).total_free_pages.view() + 1,
            final(self).spec_index(alloc_ptr).cpu_caches.entries_unchanged_except(&old(self).spec_index(alloc_ptr).cpu_caches, cpu_id),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().is_init(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().write_lock_perm_match(lock_perm.view()),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_id() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_id(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed(),
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            final(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            final(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
    {
        assert(old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        {
            let alloc_mut = self.borrow_mut(alloc_ptr);
            alloc_mut.push_cache_page(cpu_id, node_addr, node_perm, Tracked(lctx), lock_perm)
        };
        assert({
            &&& self.typed_quota_lock_map_aligned(quota_locks, lctx.thread_id())
            &&& self.typed_cache_lock_map_aligned(cache_locks, lctx.thread_id())
            &&& self.typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id())
        }) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
    }

    pub fn pop_cache_page_typed(
        &mut self,
        alloc_ptr: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(global_pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lock_perm: Tracked<&LockPerm>,
    ) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(cache_locks, (alloc_ptr, cpu_id), TypedLockMode::Write),
            lock_perm.view().lock_id() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().spec_index(0),
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(ret.0),
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(ret.0) == ret.1.view().value().view(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
            !final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().view().contains(ret.1.view().value().view()),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().map() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().map().remove(ret.0),
            final(self).spec_index(alloc_ptr).total_free_pages.view() == old(self).spec_index(alloc_ptr).total_free_pages.view() - 1,
            final(self).spec_index(alloc_ptr).cpu_caches.entries_unchanged_except(&old(self).spec_index(alloc_ptr).cpu_caches, cpu_id),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().is_init(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().write_lock_perm_match(lock_perm.view()),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_id() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_id(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed(),
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            final(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            final(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
    {
        assert(old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx)) by { reveal(UnLockedMap::typed_cache_lock_map_aligned); };
        let ret = {
            let alloc_mut = self.borrow_mut(alloc_ptr);
            alloc_mut.pop_cache_page(cpu_id, Tracked(lctx), lock_perm)
        };
        assert({
            &&& self.typed_quota_lock_map_aligned(quota_locks, lctx.thread_id())
            &&& self.typed_cache_lock_map_aligned(cache_locks, lctx.thread_id())
            &&& self.typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id())
        }) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
        ret
    }

    pub fn push_global_pool_page_typed(
        &mut self,
        alloc_ptr: RwLockPageAllocatorPtr,
        node_addr: usize,
        node_perm: Tracked<PointsTo<Node<PagePtr>>>,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(global_pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lock_perm: Tracked<&LockPerm>,
    )
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(global_pool_locks, alloc_ptr, TypedLockMode::Write),
            lock_perm.view().lock_id() == old(self).spec_index(alloc_ptr).global_pool.locking_thread()->Write_lock_id,
            node_perm.view().is_init(),
            node_perm.view().addr() == node_addr,
            !old(self).spec_index(alloc_ptr).global_pool.view().view().contains(node_perm.view().value().view()),
            old(self).spec_index(alloc_ptr).total_free_pages.view() < usize::MAX,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            final(self).spec_index(alloc_ptr).global_pool.view().view() == old(self).spec_index(alloc_ptr).global_pool.view().view().insert(0, node_perm.view().value().view()),
            final(self).spec_index(alloc_ptr).global_pool.view().map() == old(self).spec_index(alloc_ptr).global_pool.view().map().insert(node_addr, node_perm.view().value().view()),
            !old(self).spec_index(alloc_ptr).global_pool.view().map().dom().contains(node_addr),
            final(self).spec_index(alloc_ptr).total_free_pages.view() == old(self).spec_index(alloc_ptr).total_free_pages.view() + 1,
            final(self).spec_index(alloc_ptr).global_pool.is_init(),
            final(self).spec_index(alloc_ptr).global_pool.wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).global_pool.write_lock_perm_match(lock_perm.view()),
            final(self).spec_index(alloc_ptr).global_pool.lock_id() == old(self).spec_index(alloc_ptr).global_pool.lock_id(),
            final(self).spec_index(alloc_ptr).global_pool.locking_thread() == old(self).spec_index(alloc_ptr).global_pool.locking_thread(),
            final(self).spec_index(alloc_ptr).global_pool.being_killed() == old(self).spec_index(alloc_ptr).global_pool.being_killed(),
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            final(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            final(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
    {
        assert(old(self).spec_index(alloc_ptr).global_pool.wlocked_by(lctx)) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
        {
            let alloc_mut = self.borrow_mut(alloc_ptr);
            alloc_mut.push_global_pool_page(node_addr, node_perm, Tracked(lctx), lock_perm)
        };
        assert({
            &&& self.typed_quota_lock_map_aligned(quota_locks, lctx.thread_id())
            &&& self.typed_cache_lock_map_aligned(cache_locks, lctx.thread_id())
            &&& self.typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id())
        }) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
    }

    pub fn pop_global_pool_page_typed(
        &mut self,
        alloc_ptr: RwLockPageAllocatorPtr,
        Ghost(quota_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Ghost(cache_locks): Ghost<Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>>,
        Ghost(global_pool_locks): Ghost<Map<RwLockPageAllocatorPtr, TypedHeldLock>>,
        Tracked(lctx): Tracked<&LocalContext>,
        lock_perm: Tracked<&LockPerm>,
    ) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            old(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            old(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            old(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            typed_lock_map_contains_mode(global_pool_locks, alloc_ptr, TypedLockMode::Write),
            lock_perm.view().lock_id() == old(self).spec_index(alloc_ptr).global_pool.locking_thread()->Write_lock_id,
            old(self).spec_index(alloc_ptr).global_pool.view().len() > 0,
        ensures
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).spec_index(alloc_ptr).global_pool.view().view().spec_index(0),
            old(self).spec_index(alloc_ptr).global_pool.view().map().dom().contains(ret.0),
            old(self).spec_index(alloc_ptr).global_pool.view().map().spec_index(ret.0) == ret.1.view().value().view(),
            final(self).spec_index(alloc_ptr).global_pool.view().view() == old(self).spec_index(alloc_ptr).global_pool.view().view().skip(1),
            final(self).spec_index(alloc_ptr).global_pool.view().map() == old(self).spec_index(alloc_ptr).global_pool.view().map().remove(ret.0),
            final(self).spec_index(alloc_ptr).total_free_pages.view() == old(self).spec_index(alloc_ptr).total_free_pages.view() - 1,
            final(self).spec_index(alloc_ptr).global_pool.is_init(),
            final(self).spec_index(alloc_ptr).global_pool.wlocked_by(lctx),
            final(self).spec_index(alloc_ptr).global_pool.write_lock_perm_match(lock_perm.view()),
            final(self).spec_index(alloc_ptr).global_pool.lock_id() == old(self).spec_index(alloc_ptr).global_pool.lock_id(),
            final(self).spec_index(alloc_ptr).global_pool.locking_thread() == old(self).spec_index(alloc_ptr).global_pool.locking_thread(),
            final(self).spec_index(alloc_ptr).global_pool.being_killed() == old(self).spec_index(alloc_ptr).global_pool.being_killed(),
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).typed_quota_lock_map_aligned(quota_locks, lctx.thread_id()),
            final(self).typed_cache_lock_map_aligned(cache_locks, lctx.thread_id()),
            final(self).typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id()),
    {
        assert(old(self).spec_index(alloc_ptr).global_pool.wlocked_by(lctx)) by { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); };
        let ret = {
            let alloc_mut = self.borrow_mut(alloc_ptr);
            alloc_mut.pop_global_pool_page(Tracked(lctx), lock_perm)
        };
        assert({
            &&& self.typed_quota_lock_map_aligned(quota_locks, lctx.thread_id())
            &&& self.typed_cache_lock_map_aligned(cache_locks, lctx.thread_id())
            &&& self.typed_global_pool_lock_map_aligned(global_pool_locks, lctx.thread_id())
        }) by {
            reveal(UnLockedMap::typed_quota_lock_map_aligned);
            reveal(UnLockedMap::typed_cache_lock_map_aligned);
            reveal(UnLockedMap::typed_global_pool_lock_map_aligned);
        };
        ret
    }
}

impl UnLockedMap<usize, PageAllocator> {
    pub fn wlock_quota(&mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            wlock_requires(old(self).spec_index(alloc_ptr).quota, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).spec_index(alloc_ptr).quota.view().container_depth(),
                process: old(self).spec_index(alloc_ptr).quota.view().process_depth(),
                major: old(self).spec_index(alloc_ptr).quota.view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).quota.view().lock_minor(),
            }),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            wlock_ensures(old(self).spec_index(alloc_ptr).quota, final(self).spec_index(alloc_ptr).quota, LockId{
                container: old(self).spec_index(alloc_ptr).quota.view().container_depth(),
                process: old(self).spec_index(alloc_ptr).quota.view().process_depth(),
                major: old(self).spec_index(alloc_ptr).quota.view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).quota.view().lock_minor(),
            }, final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), LockId{
                container: old(self).spec_index(alloc_ptr).quota.view().container_depth(),
                process: old(self).spec_index(alloc_ptr).quota.view().process_depth(),
                major: old(self).spec_index(alloc_ptr).quota.view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).quota.view().lock_minor(),
            }, KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr)),
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wlock_quota(Tracked(lctx), page_size, Ghost(alloc_ptr))
    }
}

impl UnLockedMap<usize, PageAllocator> {
    pub fn wunlock_quota(&mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            old(self).spec_index(alloc_ptr).quota.wlocked_by(old(lctx)),
            old(self).spec_index(alloc_ptr).quota.inv(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(alloc_ptr).quota.locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(self).spec_index(alloc_ptr).quota.lock_id(), KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            final(self).spec_index(alloc_ptr).quota.lock_id()
                == old(self).spec_index(alloc_ptr).quota.lock_id(),
            wunlock_ensures(old(self).spec_index(alloc_ptr).quota, final(self).spec_index(alloc_ptr).quota),
            unlock_ensures(
                old(lctx), final(lctx), KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr),
                old(self).spec_index(alloc_ptr).quota.lock_id(),
            ),
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wunlock_quota(Tracked(lctx), lock_perm, page_size, Ghost(alloc_ptr))
    }
}

impl UnLockedMap<usize, PageAllocator> {
    pub fn wlock_cache(&mut self, alloc_ptr: usize, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            index_valid(NUM_CPUS, cpu_id),
            wlock_requires(old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view(), old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).container_depth(),
                process: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).process_depth(),
                major: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_minor(),
            }),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            wlock_ensures(old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view(), final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view(), LockId{
                container: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).container_depth(),
                process: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).process_depth(),
                major: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_minor(),
            }, final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), LockId{
                container: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).container_depth(),
                process: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).process_depth(),
                major: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_minor(),
            }, KernelObjId::AllocatorCache(page_size.view(), alloc_ptr, cpu_id)),
            final(self).spec_index(alloc_ptr).cpu_caches.unchanged_except(&old(self).spec_index(alloc_ptr).cpu_caches, cpu_id),
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wlock_cache(cpu_id, Tracked(lctx), page_size, Ghost(alloc_ptr))
    }

    pub fn wunlock_cache(&mut self, alloc_ptr: usize, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_id(), KernelObjId::AllocatorCache(page_size.view(), alloc_ptr, cpu_id)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_id()
                == old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_id(),
            wunlock_ensures(old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view(), final(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).view()),
            unlock_ensures(
                old(lctx), final(lctx), KernelObjId::AllocatorCache(page_size.view(), alloc_ptr, cpu_id),
                old(self).spec_index(alloc_ptr).cpu_caches.spec_index(cpu_id).lock_id(),
            ),
            final(self).spec_index(alloc_ptr).cpu_caches.unchanged_except(&old(self).spec_index(alloc_ptr).cpu_caches, cpu_id),
            final(self).spec_index(alloc_ptr).global_pool == old(self).spec_index(alloc_ptr).global_pool,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wunlock_cache(cpu_id, Tracked(lctx), lock_perm, page_size, Ghost(alloc_ptr))
    }

    pub fn wlock_global_pool(&mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            wlock_requires(old(self).spec_index(alloc_ptr).global_pool, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).spec_index(alloc_ptr).global_pool.view().container_depth(),
                process: old(self).spec_index(alloc_ptr).global_pool.view().process_depth(),
                major: old(self).spec_index(alloc_ptr).global_pool.view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).global_pool.view().lock_minor(),
            }),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            wlock_ensures(old(self).spec_index(alloc_ptr).global_pool, final(self).spec_index(alloc_ptr).global_pool, LockId{
                container: old(self).spec_index(alloc_ptr).global_pool.view().container_depth(),
                process: old(self).spec_index(alloc_ptr).global_pool.view().process_depth(),
                major: old(self).spec_index(alloc_ptr).global_pool.view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).global_pool.view().lock_minor(),
            }, final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), LockId{
                container: old(self).spec_index(alloc_ptr).global_pool.view().container_depth(),
                process: old(self).spec_index(alloc_ptr).global_pool.view().process_depth(),
                major: old(self).spec_index(alloc_ptr).global_pool.view().current_lock_major(),
                minor: old(self).spec_index(alloc_ptr).global_pool.view().lock_minor(),
            }, KernelObjId::AllocatorGlobalPool(page_size.view(), alloc_ptr)),
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wlock_global_pool(Tracked(lctx), page_size, Ghost(alloc_ptr))
    }

    pub fn wunlock_global_pool(&mut self, alloc_ptr: usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>)
        requires
            old(self).perms_wf(),
            old(self).dom().contains(alloc_ptr),
            old(self).spec_index(alloc_ptr).wf(),
            old(self).spec_index(alloc_ptr).global_pool.wlocked_by(old(lctx)),
            old(self).spec_index(alloc_ptr).global_pool.inv(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).spec_index(alloc_ptr).global_pool.locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(self).spec_index(alloc_ptr).global_pool.lock_id(), KernelObjId::AllocatorGlobalPool(page_size.view(), alloc_ptr)),
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(self).perms_wf(),
            final(self).unchanged_except(old(self), alloc_ptr),
            final(self).spec_index(alloc_ptr).wf(),
            final(self).spec_index(alloc_ptr).global_pool.lock_id()
                == old(self).spec_index(alloc_ptr).global_pool.lock_id(),
            wunlock_ensures(old(self).spec_index(alloc_ptr).global_pool, final(self).spec_index(alloc_ptr).global_pool),
            unlock_ensures(
                old(lctx), final(lctx), KernelObjId::AllocatorGlobalPool(page_size.view(), alloc_ptr),
                old(self).spec_index(alloc_ptr).global_pool.lock_id(),
            ),
            final(self).spec_index(alloc_ptr).cpu_caches == old(self).spec_index(alloc_ptr).cpu_caches,
            final(self).spec_index(alloc_ptr).quota == old(self).spec_index(alloc_ptr).quota,
            final(self).spec_index(alloc_ptr).owning_container == old(self).spec_index(alloc_ptr).owning_container,
            final(self).spec_index(alloc_ptr).total_free_pages == old(self).spec_index(alloc_ptr).total_free_pages,
    {
        let alloc = self.borrow_mut(alloc_ptr);
        alloc.wunlock_global_pool(Tracked(lctx), lock_perm, page_size, Ghost(alloc_ptr))
    }
}
} // verus!
