use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;

verus! {

pub struct PageAllocator{
    pub cpu_caches: LockedArray<AllocatorCache, (), (), (), NUM_CPUS, NO_KILL_STATE>,
    pub global_poll: RwLock<LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>, (), (), (), NO_KILL_STATE>,
    pub quota: RwLock<AllocatorQuota, (), (), (), NO_KILL_STATE>,
    pub differential: Ghost<Seq<int>>,
    pub total_free_pages: Ghost<usize>,

    pub owning_container: RwLockContainerPtr,
}

impl LockInvTrait for PageAllocator{
    open spec fn inv(&self) -> bool {
        &&&
        self.wf()
    }
}

impl PageAllocator{
    pub open spec fn wf(&self) -> bool{
        &&&
        self.cpu_caches.inv()
        &&&
        self.global_poll.inv()
        // &&&
        // self.quota.inv()
        &&&
        self.cpu_caches_wf()
        &&&
        self.quota_minor_wf()
        &&&
        self.global_poll_minor_wf()
        // &&&
        // self.internal_lock_id_wf()
        &&&
        self.differential_wf()
        &&&
        self.total_free_pages_wf()
        &&&
        self.differential@.len() == NUM_CPUS
    }

    pub open spec fn cpu_caches_wf(&self) -> bool {
        &&&
        forall|cpu_i:CpuId|
        #![trigger self.cpu_caches.spec_index(cpu_i).inv()]
        cpu_id_valid(cpu_i)
        ==>
        self.cpu_caches.spec_index(cpu_i).inv()
    }

    /// The quota's intrinsic minor lock id is the owning container pointer.
    /// `AllocatorQuota` sits in a bare `RwLock` (not in a wrapper that
    /// provides a minor), so it carries its own `Ghost<LockMinorId>` field;
    /// this invariant pins that minor to `owning_container`.
    pub open spec fn quota_minor_wf(&self) -> bool {
        self.quota.view().lock_minor() == self.owning_container
    }

    /// The global pool's intrinsic minor lock id is the owning container
    /// pointer. Same reasoning as `quota_minor_wf` — `LinkedList` carries
    /// its own minor.
    pub open spec fn global_poll_minor_wf(&self) -> bool {
        self.global_poll.view().lock_minor() == self.owning_container
    }

    pub open spec fn differential_wf(&self) -> bool{
        forall|cpu_i: CpuId|
        #![trigger self.cpu_caches.spec_index(cpu_i).value().view().linked_list.len()]
        #![trigger self.differential@[cpu_i as int]]
        cpu_id_valid(cpu_i)
        ==>
        {
            |||
            self.cpu_caches.spec_index(cpu_i).value().wlocked()
            |||
            self.cpu_caches.spec_index(cpu_i).value().view().linked_list.len()
            ==
            self.differential@[cpu_i as int]
        }
    }

    pub open spec fn total_free_pages_wf(&self) -> bool{
        self.global_poll.view().len() + self.differential@.fold_left(0int, |sum: int, i: int| {sum + i}) == self.total_free_pages.view()
    }

    pub open spec fn cpu_caches_unlocked(&self) -> bool {
        &&&
         forall|cpu_i: CpuId|
        #![auto]
        cpu_id_valid(cpu_i)
        ==>
        self.cpu_caches.spec_index(cpu_i).view().locked() == false
    }

    pub open spec fn global_poll_unlocked(&self) -> bool{
        self.global_poll.locked() == false
    }

    // pub open spec fn quota_unlocked(&self) -> bool{
    //     self.quota.locked() == false
    // }

    // pub open spec fn internal_lock_id_wf(&self) -> bool{
    //     &&&
    //     self.quota.view().container_depth() == self.global_poll.view().container_depth()
    //     &&&
    //     forall|cpu_i:CpuId|
    //         #![trigger self.cpu_caches.spec_index(cpu_i).container_depth()]
    //         #![trigger self.cpu_caches.spec_index(cpu_i).process_depth()]
    //         cpu_id_valid(cpu_i)
    //         ==>
    //         self.cpu_caches.spec_index(cpu_i).container_depth() == self.quota.view().container_depth()
    //         &&
    //         self.cpu_caches.spec_index(cpu_i).process_depth() == self.quota.view().process_depth()
    // }
}

impl PageAllocator{
    /// Acquire the inner `quota` write lock.
    ///
    /// The caller passes the allocator's `page_size` class and pointer
    /// (`alloc_ptr`) so the wrapper can build the right `KernelObjId`. The
    /// rest of the lock id (container/process/major/minor) is inferred by
    /// the underlying primitive from the quota's traits.
    ///
    /// Acyclic + freshness obligations on `lctx.lock_map` are passed through
    /// to the caller — same as a direct `RwLock::wlock`.
    pub fn wlock_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).wf(),
            wlock_requires(old(self).quota, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).quota@.container_depth(),
                process: old(self).quota@.process_depth(),
                major: old(self).quota@.current_lock_major(),
                minor: old(self).quota@.lock_minor(),
            }),
            old(lctx).obj_id_fresh(KernelObjId::AllocatorQuota(page_size@, alloc_ptr@)),
        ensures
            final(self).wf(),
            // Quota lock acquired.
            wlock_ensures(old(self).quota, final(self).quota, LockId{
                container: old(self).quota@.container_depth(),
                process: old(self).quota@.process_depth(),
                major: old(self).quota@.current_lock_major(),
                minor: old(self).quota@.lock_minor(),
            }, final(lctx).thread_id(), ret@),
            lock_ensures(old(lctx), final(lctx), final(self).quota.view(), LockId{
                container: old(self).quota@.container_depth(),
                process: old(self).quota@.process_depth(),
                major: old(self).quota@.current_lock_major(),
                minor: old(self).quota@.lock_minor(),
            }, KernelObjId::AllocatorQuota(page_size@, alloc_ptr@)),
            // Other fields untouched.
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).global_poll == old(self).global_poll,
            final(self).owning_container == old(self).owning_container,
            final(self).differential == old(self).differential,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let lock_id = Ghost(LockId{
            container: self.quota@.container_depth(),
            process: self.quota@.process_depth(),
            major: self.quota@.current_lock_major(),
            minor: self.quota@.lock_minor(),
        });
        self.quota.wlock(Tracked(lctx), lock_id, Ghost(KernelObjId::AllocatorQuota(page_size@, alloc_ptr@)))
    }

    /// Release the inner `quota` write lock.
    ///
    /// The caller passes `page_size` and `alloc_ptr` so the wrapper can
    /// remove the matching key from `lctx.lock_map`. The lock id stored on
    /// `lock_perm` must match the key currently in the map — same contract
    /// as `RwLock::wunlock`.
    pub fn wunlock_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            old(self).quota.wlocked_by(old(lctx)),
            old(self).quota.inv(),

            unlock_requires::<AllocatorQuota>(old(lctx)),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self).quota.locking_thread()->Write_lock_id,

            old(lctx).lock_map().dom().contains(KernelObjId::AllocatorQuota(page_size@, alloc_ptr@)),
            old(lctx).lock_map()[KernelObjId::AllocatorQuota(page_size@, alloc_ptr@)] == lock_perm@.lock_id(),
        ensures
            final(self).wf(),
            wunlock_ensures(old(self).quota, final(self).quota),
            unlock_ensures(old(lctx), final(lctx), final(self).quota.view(), lock_perm@.lock_id(), KernelObjId::AllocatorQuota(page_size@, alloc_ptr@)),
            // Other fields untouched.
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).global_poll == old(self).global_poll,
            final(self).owning_container == old(self).owning_container,
            final(self).differential == old(self).differential,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        self.quota.wunlock(Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorQuota(page_size@, alloc_ptr@)))
    }

    // pub fn try_allocate_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, quota: usize, cpu_id: CpuId) -> (ret :bool)
    //     requires
    //         old(self).wf(),
    //         old(self).cpu_caches_unlocked(),
    //         old(self).global_poll_unlocked(),
    //         // old(self).quota_unlocked(),
    //         old(self).local_quota_clean(cpu_id),
    //         cpu_id_valid(cpu_id),
    //         old(lctx).thread_id() == cpu_id,

    //         wlock_requires(old(self).cpu_caches.spec_index(cpu_id).view(), old(lctx)),
    //         // wlock_requires(old(self).quota, old(lctx)),
    //         wlock_requires(old(self).global_poll, old(lctx)),

    //         old(lctx).kernel_view_locking_state() is Acquire,

    //         old(lctx).lock_id_acyclic(LockId{
    //             container: old(self).quota.view().container_depth(),
    //             process: old(self).quota.view().process_depth(),
    //             major: old(self).quota.view().lock_major_1(),
    //             minor: old(self).quota.view().lock_minor(),
    //         }),
    //     ensures
    //         lctx.kernel_view_locking_state() is Release,
    //         ret == (old(self).quota.view().view() >= quota),
    //         ret == false ==> {
    //             &&&
    //             self.wf()
    //             &&&
    //             self.cpu_caches_unlocked()
    //             &&&
    //             self.global_poll_unlocked()
    //             &&&
    //             self.quota_unlocked()
    //             &&&
    //             self.cpu_caches == old(self).cpu_caches
    //             &&&
    //             self.global_poll == old(self).global_poll
    //             &&&
    //             self.quota.view() == old(self).quota.view()
    //         },

    // {
    //     let quota_lock_perm = self.quota.wlock(Tracked(lctx), Ghost(
    //         LockId{
    //             container: old(self).quota.view().container_depth(),
    //             process: old(self).quota.view().process_depth(),
    //             major: QUOTA_MAJOR,
    //             minor: old(self).quota.view().lock_minor(),
    //         }
    //     ));

    //     let mut old_quota = self.quota.take(Tracked(lctx), Tracked(&quota_lock_perm));
        
    //     let ret = old_quota.value >= quota;
    //     if !ret {
    //         self.quota.put(Tracked(lctx), Tracked(&quota_lock_perm), old_quota);
    //         self.quota.wunlock(Tracked(lctx), quota_lock_perm);
    //         return ret;
    //     }
    //     old_quota.value = old_quota.value - quota;

    //     let cpu_cache_perm = self.cpu_caches.wlock(cpu_id, Tracked(lctx), Ghost(LockId{
    //             container: old(self).quota.view().container_depth(),
    //             process: old(self).quota.view().process_depth(),
    //             major: ALLOCATOR_CACHE_MAJOR,
    //             minor: cpu_id,
    //         }));

    //     let mut cpu_cache = self.cpu_caches.take(cpu_id, Tracked(lctx), Tracked(&cpu_cache_perm));
    //     cpu_cache.local_quota = quota;
    //     proof {
    //         self.differential@ = self.differential@.update(cpu_id as int,cpu_cache.linked_list.len() - quota);
    //     }
    //     self.cpu_caches.put(cpu_id, Tracked(lctx), Tracked(&cpu_cache_perm), cpu_cache);
    //     self.cpu_caches.wunlock(cpu_id, Tracked(lctx), cpu_cache_perm);
    //     self.quota.put(Tracked(lctx), Tracked(&quota_lock_perm), old_quota);
        
    //     assert(self.wf()) by {
    //         assert(self.cpu_caches.inv());
    //         assert(self.global_poll.inv());
    //         assert(self.quota.inv());
    //         assert(self.cpu_caches_wf());
    //         assert(self.internal_lock_id_wf());
    //         assert(self.differential_wf());
    //         assert(self.total_free_pages_wf()) by {
    //             seq_fold_update_lemma()
    //         };
    //         assert(self.differential@.len() == NUM_CPUS);
    //     };
    //     self.quota.wunlock(Tracked(lctx), quota_lock_perm);
    //     assert(self.wf());
    //     true
    // }
}

}