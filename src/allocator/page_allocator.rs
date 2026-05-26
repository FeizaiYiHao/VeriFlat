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

    pub open spec fn differential_wf(&self) -> bool{
        forall|cpu_i: CpuId|
        #![trigger self.cpu_caches.spec_index(cpu_i).value().view().linked_list.len()]
        #![trigger self.cpu_caches.spec_index(cpu_i).value().view().local_quota]
        #![trigger self.differential@[cpu_i as int]]
        cpu_id_valid(cpu_i)
        ==>
        {
            |||
            self.cpu_caches.spec_index(cpu_i).value().wlocked()
            |||
            self.cpu_caches.spec_index(cpu_i).value().view().linked_list.len() - self.cpu_caches.spec_index(cpu_i).value().view().local_quota
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

    pub open spec fn local_quota_clean(&self) -> bool{
        &&&
        forall|cpu_i: CpuId|
        #![trigger self.cpu_caches.spec_index(cpu_i).view().view().local_quota]
        cpu_id_valid(cpu_i)
        ==>
        self.cpu_caches.spec_index(cpu_i).view().view().local_quota == 0
    } 

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