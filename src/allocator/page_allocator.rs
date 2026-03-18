use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;
verus! {

pub struct PageAllocator{
    pub cpu_caches: LockedArray<AllocatorCache, false, NUM_CPUS>,
    pub global_poll: RwLock<LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>, false>,
    pub quota: RwLock<AllocatorQuota, false>,
    pub differential: Ghost<Seq<int>>,
}

impl PageAllocator{
    pub open spec fn wf(&self) -> bool{
        &&&
        self.cpu_caches.inv()
        &&&
        self.global_poll.inv()
        &&&
        self.quota.inv()
        &&&
        self.differential@.len() == NUM_CPUS
    }

    pub open spec fn differential_wf(&self) -> bool{
        forall|cpu_i: CpuId|
        #![auto]
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

    pub open spec fn quota_wf(&self) -> bool{
        |||
        write_locked_by_same_thread(self.global_poll, self.quota)
        |||
        self.global_poll.view().len() + self.differential@.fold_left(0int, |sum: int, i: int| {sum + 1}) == self.quota.view().view()
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

    pub open spec fn quota_unlocked(&self) -> bool{
        self.quota.locked() == false
    }
}

impl PageAllocator{
    pub fn try_allocate_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, quota: usize, cpu_id: CpuId) -> (ret :bool)
        requires
            old(self).wf(),
            old(self).cpu_caches_unlocked(),
            old(self).global_poll_unlocked(),
            old(self).quota_unlocked(),
            cpu_id_valid(cpu_id),

            wlock_requires(old(self).cpu_caches.spec_index(cpu_id).view(), old(lctx)),
            wlock_requires(old(self).quota, old(lctx)),
            wlock_requires(old(self).global_poll, old(lctx)),

            old(lctx).lock_id_valid(LockId{
                container: old(self).quota.view().container_depth(),
                process: old(self).quota.view().process_depth(),
                major: old(self).quota.view().lock_major_1(),
                minor: old(self).quota.view().lock_minor(),
            }),

    {
        let quota_lock_perm = self.quota.wlock(Tracked(lctx), Ghost(
            LockId{
                container: old(self).quota.view().container_depth(),
                process: old(self).quota.view().process_depth(),
                major: old(self).quota.view().lock_major_1(),
                minor: old(self).quota.view().lock_minor(),
            }
        ));

        true
    }
}

}