use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;

verus! {

pub struct PageAllocator{
    pub cpu_caches: LockedArray<AllocatorCache, (), (), NUM_CPUS, NO_KILL_STATE>,
    pub global_pool: RwLock<GlobalPool, (), (), NO_KILL_STATE>,
    pub quota: RwLock<AllocatorQuota, (), (), NO_KILL_STATE>,
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
    pub fn new_with_global_pool(
        owning_container: RwLockContainerPtr,
        container_depth: usize,
        linked_list: LinkedList<PagePtr, ALLOCATOR_GLOBAL_POLL_MAJOR>,
        quota_value: usize,
    ) -> (ret: Self)
        requires
            linked_list.wf(),
            linked_list.view().no_duplicates(),
            linked_list.container_depth == Some(container_depth),
            linked_list.minor == Some(owning_container),
        ensures
            ret.inv(),
            ret.owning_container == owning_container,
            ret.total_free_pages.view() == linked_list.view().len(),
            ret.quota.view().view() == quota_value,
            ret.quota.view().container_depth == container_depth,
            ret.quota.view().lock_minor() == owning_container,
            !ret.quota.locked(),
            ret.global_pool.view().view() == linked_list.view(),
            ret.global_pool.view().map() == linked_list.map(),
            !ret.global_pool.locked(),
            forall|cpu_id: CpuId| #![auto]
                index_valid(NUM_CPUS, cpu_id)
                ==> {
                    &&& ret.cpu_caches.spec_index(cpu_id).view().view()
                        .linked_list.view() == Seq::<PagePtr>::empty()
                    &&& ret.cpu_caches.spec_index(cpu_id).view().view()
                        .linked_list.map() == Map::<usize, PagePtr>::empty()
                    &&& !ret.cpu_caches.spec_index(cpu_id).view().locked()
                },
    {
        proof {
            reveal(LinkedList::wf_value_list);
        }
        let mut cache_array:
            Array<RwLock<AllocatorCache, (), (), NO_KILL_STATE>, NUM_CPUS>
                = Array::new();
        let mut cpu_id = 0;
        while cpu_id < NUM_CPUS
            invariant
                cache_array.wf(),
                0 <= cpu_id <= NUM_CPUS,
                forall|i: CpuId| #![auto]
                    index_valid(NUM_CPUS, i) && i < cpu_id
                    ==> {
                        &&& cache_array.spec_index(i).inv()
                        &&& cache_array.spec_index(i).view().linked_list.view()
                            == Seq::<PagePtr>::empty()
                        &&& cache_array.spec_index(i).view().linked_list.map()
                            == Map::<usize, PagePtr>::empty()
                        &&& !cache_array.spec_index(i).locked()
                    },
                forall|i: int|
                    #![trigger cache_array.view().spec_index(i)]
                    0 <= i < cpu_id
                    ==> cache_array.view().spec_index(i).view()
                        .linked_list.view().len() == 0,
            decreases NUM_CPUS - cpu_id,
        {
            let cache = AllocatorCache {
                linked_list: LinkedList::new(
                    Some(container_depth),
                    Some(cpu_id),
                ),
            };
            cache_array.set(
                cpu_id,
                RwLock::new_unlocked(cache, (), Ghost(())),
            );
            cpu_id = cpu_id + 1;
        }
        let total_free_pages = linked_list.length;
        let cpu_caches = LockedArray::from_array(cache_array);
        let global_pool = RwLock::new_unlocked(
            GlobalPool { linked_list },
            (),
            Ghost(()),
        );
        let quota = RwLock::new_unlocked(
            AllocatorQuota {
                value: quota_value,
                minor: Ghost(owning_container),
                container_depth,
            },
            (),
            Ghost(()),
        );
        let ret = Self {
            cpu_caches,
            global_pool,
            quota,
            total_free_pages: Ghost(total_free_pages),
            owning_container,
        };
        proof {
            lemma_cache_len_fold_all_zero(ret.cpu_caches.view());
            ret.global_pool.view().lemma_len_view();
        }
        ret
    }

    pub fn new_empty(
        owning_container: RwLockContainerPtr,
        container_depth: usize,
    ) -> (ret: Self)
        ensures
            ret.inv(),
            ret.owning_container == owning_container,
            ret.total_free_pages.view() == 0,
            ret.quota.view().view() == 0,
            ret.quota.view().container_depth == container_depth,
            ret.quota.view().lock_minor() == owning_container,
            !ret.quota.locked(),
            ret.global_pool.view().view() == Seq::<PagePtr>::empty(),
            ret.global_pool.view().map() == Map::<usize, PagePtr>::empty(),
            !ret.global_pool.locked(),
            forall|cpu_id: CpuId| #![auto]
                index_valid(NUM_CPUS, cpu_id)
                ==> {
                    &&& ret.cpu_caches.spec_index(cpu_id).view().view()
                        .linked_list.view() == Seq::<PagePtr>::empty()
                    &&& ret.cpu_caches.spec_index(cpu_id).view().view()
                        .linked_list.map() == Map::<usize, PagePtr>::empty()
                    &&& !ret.cpu_caches.spec_index(cpu_id).view().locked()
                },
    {
        let mut cache_array:
            Array<RwLock<AllocatorCache, (), (), NO_KILL_STATE>, NUM_CPUS>
                = Array::new();
        let mut cpu_id = 0;
        while cpu_id < NUM_CPUS
            invariant
                cache_array.wf(),
                0 <= cpu_id <= NUM_CPUS,
                forall|i: CpuId| #![auto]
                    index_valid(NUM_CPUS, i) && i < cpu_id
                    ==> {
                        &&& cache_array.spec_index(i).inv()
                        &&& cache_array.spec_index(i).view().linked_list.view() == Seq::<PagePtr>::empty()
                        &&& cache_array.spec_index(i).view().linked_list.map() == Map::<usize, PagePtr>::empty()
                        &&& !cache_array.spec_index(i).locked()
                    },
                forall|i: int| #![trigger cache_array.view().spec_index(i)]
                    0 <= i < cpu_id
                    ==> cache_array.view().spec_index(i).view()
                        .linked_list.view().len() == 0,
            decreases NUM_CPUS - cpu_id,
        {
            let cache = AllocatorCache {
                linked_list: LinkedList::new(
                    Some(container_depth),
                    Some(cpu_id),
                ),
            };
            cache_array.set(
                cpu_id,
                RwLock::new_unlocked(cache, (), Ghost(())),
            );
            cpu_id = cpu_id + 1;
        }
        let cpu_caches = LockedArray::from_array(cache_array);
        let global_pool = RwLock::new_unlocked(
            GlobalPool {
                linked_list: LinkedList::new(
                    Some(container_depth),
                    Some(owning_container),
                ),
            },
            (),
            Ghost(()),
        );
        let quota = RwLock::new_unlocked(
            AllocatorQuota {
                value: 0,
                minor: Ghost(owning_container),
                container_depth,
            },
            (),
            Ghost(()),
        );
        let ret = Self {
            cpu_caches,
            global_pool,
            quota,
            total_free_pages: Ghost(0),
            owning_container,
        };
        proof {
            lemma_cache_len_fold_all_zero(ret.cpu_caches.view());
        }
        ret
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.cpu_caches.inv()
        &&& self.global_pool.inv()
        &&& self.cpu_caches_wf()
        &&& self.quota_minor_wf()
        &&& self.global_pool_minor_wf()
        &&& self.total_free_pages_wf()
    }

    pub open spec fn cpu_caches_wf(&self) -> bool {
        forall|cpu_i: CpuId| #![trigger index_valid(NUM_CPUS, cpu_i)]
            index_valid(NUM_CPUS, cpu_i) ==> self.cpu_caches.spec_index(cpu_i).inv()
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
    pub open spec fn global_pool_minor_wf(&self) -> bool {
        self.global_pool.view().lock_minor() == self.owning_container
    }

    pub open spec fn total_free_pages_wf(&self) -> bool {
        self.global_pool.view().len() + self.cpu_caches.view().fold_left(0int, |sum: int, cpu_rw_lock: RwLock<AllocatorCache, (), (), NO_KILL_STATE>| {sum + cpu_rw_lock.view().linked_list.len()}) == self.total_free_pages.view()
    }

}

impl PageAllocator{
    pub fn wlock_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).wf(),
            wlock_requires(old(self).quota, old(lctx)),
            old(lctx).lock_id_acyclic(old(self).quota.lock_id()),
        ensures
            final(self).wf(),
            wlock_ensures(old(self).quota, final(self).quota, old(self).quota.lock_id(), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), final(self).quota.view(),
                old(self).quota.lock_id(),
                KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())),
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).global_pool == old(self).global_pool,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let lock_id = Ghost(old(self).quota.lock_id());
        self.quota.wlock(Tracked(lctx), lock_id, Ghost(KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())))
    }
}

impl PageAllocator{
    pub fn wunlock_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            old(self).quota.wlocked_by(old(lctx)),
            old(self).quota.inv(),


            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).quota.locking_thread()->Write_lock_id,

            old(lctx).lock_id_set().contains((
                old(self).quota.lock_id(),
                KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view()))),
        ensures
            final(self).wf(),
            final(self).quota.lock_id() == old(self).quota.lock_id(),
            wunlock_ensures(old(self).quota, final(self).quota),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).quota.view(),
                lock_perm.view().lock_id(),
                KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view()),
                old(self).quota.lock_id(),
            ),
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).global_pool == old(self).global_pool,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        self.quota.wunlock(Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())))
    }
}

impl PageAllocator{
    pub fn wlock_cache(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).wf(),
            index_valid(NUM_CPUS, cpu_id),
            wlock_requires(old(self).cpu_caches.spec_index(cpu_id).view(), old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).cpu_caches.spec_index(cpu_id).container_depth(),
                process: old(self).cpu_caches.spec_index(cpu_id).process_depth(),
                major: old(self).cpu_caches.spec_index(cpu_id).view().view().current_lock_major(),
                minor: old(self).cpu_caches.spec_index(cpu_id).lock_minor(),
            }),
        ensures
            final(self).wf(),
            wlock_ensures(old(self).cpu_caches.spec_index(cpu_id).view(), final(self).cpu_caches.spec_index(cpu_id).view(), LockId{
                container: old(self).cpu_caches.spec_index(cpu_id).container_depth(),
                process: old(self).cpu_caches.spec_index(cpu_id).process_depth(),
                major: old(self).cpu_caches.spec_index(cpu_id).view().view().current_lock_major(),
                minor: old(self).cpu_caches.spec_index(cpu_id).lock_minor(),
            }, final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), final(self).cpu_caches.spec_index(cpu_id).view().view(), LockId{
                container: old(self).cpu_caches.spec_index(cpu_id).container_depth(),
                process: old(self).cpu_caches.spec_index(cpu_id).process_depth(),
                major: old(self).cpu_caches.spec_index(cpu_id).view().view().current_lock_major(),
                minor: old(self).cpu_caches.spec_index(cpu_id).lock_minor(),
            }, KernelObjId::AllocatorCache(
                page_size.view(), alloc_ptr.view(), cpu_id)),
            final(self).cpu_caches.unchanged_except(&old(self).cpu_caches, cpu_id),
            final(self).global_pool == old(self).global_pool,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let ghost old_caches = self.cpu_caches;
        let ret = self.cpu_caches.wlock(cpu_id, Tracked(lctx), Ghost(KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)));
        proof {
            assert(self.total_free_pages_wf()) by {
                assert forall|i: usize| index_valid(NUM_CPUS, i)
                    implies #[trigger] old_caches.view().spec_index(i as int).view().linked_list.len()
                        == self.cpu_caches.view().spec_index(i as int).view().linked_list.len()
                by {
                    old_caches.lemma_view_index(i);
                    self.cpu_caches.lemma_view_index(i);
                };
                lemma_cache_len_fold_congruence(old_caches.view(), self.cpu_caches.view());
            };
        }
        ret
    }

    pub fn wunlock_cache(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).cpu_caches.spec_index(cpu_id).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(lctx).lock_id_set().contains((
                old(self).cpu_caches.spec_index(cpu_id).lock_id(),
                KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id))),
        ensures
            final(self).wf(),
            final(self).cpu_caches.spec_index(cpu_id).lock_id()
                == old(self).cpu_caches.spec_index(cpu_id).lock_id(),
            wunlock_ensures(old(self).cpu_caches.spec_index(cpu_id).view(), final(self).cpu_caches.spec_index(cpu_id).view()),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).cpu_caches.spec_index(cpu_id).view().view(),
                lock_perm.view().lock_id(),
                KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id),
                old(self).cpu_caches.spec_index(cpu_id).lock_id(),
            ),
            final(self).cpu_caches.unchanged_except(&old(self).cpu_caches, cpu_id),
            final(self).global_pool == old(self).global_pool,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let ghost old_caches = self.cpu_caches;
        self.cpu_caches.wunlock(cpu_id, Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)));
        proof {
            assert(self.total_free_pages_wf()) by {
                assert forall|i: usize| index_valid(NUM_CPUS, i)
                    implies #[trigger] old_caches.view().spec_index(i as int).view().linked_list.len()
                        == self.cpu_caches.view().spec_index(i as int).view().linked_list.len()
                by {
                    old_caches.lemma_view_index(i);
                    self.cpu_caches.lemma_view_index(i);
                };
                lemma_cache_len_fold_congruence(old_caches.view(), self.cpu_caches.view());
            };
        }
    }

    pub fn wlock_global_pool(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).wf(),
            wlock_requires(old(self).global_pool, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).global_pool.view().container_depth(),
                process: old(self).global_pool.view().process_depth(),
                major: old(self).global_pool.view().current_lock_major(),
                minor: old(self).global_pool.view().lock_minor(),
            }),
        ensures
            final(self).wf(),
            wlock_ensures(old(self).global_pool, final(self).global_pool, LockId{
                container: old(self).global_pool.view().container_depth(),
                process: old(self).global_pool.view().process_depth(),
                major: old(self).global_pool.view().current_lock_major(),
                minor: old(self).global_pool.view().lock_minor(),
            }, final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), final(self).global_pool.view(), LockId{
                container: old(self).global_pool.view().container_depth(),
                process: old(self).global_pool.view().process_depth(),
                major: old(self).global_pool.view().current_lock_major(),
                minor: old(self).global_pool.view().lock_minor(),
            }, KernelObjId::AllocatorGlobalPoll(
                page_size.view(), alloc_ptr.view())),
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let lock_id = Ghost(LockId{
            container: self.global_pool.view().container_depth(),
            process: self.global_pool.view().process_depth(),
            major: self.global_pool.view().current_lock_major(),
            minor: self.global_pool.view().lock_minor(),
        });
        self.global_pool.wlock(Tracked(lctx), lock_id, Ghost(KernelObjId::AllocatorGlobalPoll(page_size.view(), alloc_ptr.view())))
    }

    pub fn wunlock_global_pool(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            old(self).global_pool.wlocked_by(old(lctx)),
            old(self).global_pool.inv(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).global_pool.locking_thread()->Write_lock_id,
            old(lctx).lock_id_set().contains((
                old(self).global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(page_size.view(), alloc_ptr.view()))),
        ensures
            final(self).wf(),
            final(self).global_pool.lock_id() == old(self).global_pool.lock_id(),
            wunlock_ensures(old(self).global_pool, final(self).global_pool),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).global_pool.view(),
                lock_perm.view().lock_id(),
                KernelObjId::AllocatorGlobalPoll(page_size.view(), alloc_ptr.view()),
                old(self).global_pool.lock_id(),
            ),
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        self.global_pool.wunlock(Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorGlobalPoll(page_size.view(), alloc_ptr.view())))
    }
}

impl PageAllocator{
    pub fn pop_cache_page(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
        requires
            old(self).wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            old(self).cpu_caches.spec_index(cpu_id).view().is_init(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(self).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(self).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
        ensures
            final(self).wf(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).cpu_caches.spec_index(cpu_id).view().view().view().spec_index(0),
            old(self).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(ret.0),
            old(self).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(ret.0) == ret.1.view().value().view(),
            final(self).cpu_caches.spec_index(cpu_id).view().view().view() == old(self).cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
            final(self).cpu_caches.spec_index(cpu_id).view().view().map() == old(self).cpu_caches.spec_index(cpu_id).view().view().map().remove(ret.0),
            final(self).total_free_pages.view() == old(self).total_free_pages.view() - 1,
            final(self).cpu_caches.entries_unchanged_except(&old(self).cpu_caches, cpu_id),
            final(self).cpu_caches.spec_index(cpu_id).view().is_init(),
            final(self).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            final(self).cpu_caches.spec_index(cpu_id).view()
                .write_lock_perm_match(lock_perm.view()),
            final(self).cpu_caches.spec_index(cpu_id).lock_id()
                == old(self).cpu_caches.spec_index(cpu_id).lock_id(),
            final(self).cpu_caches.spec_index(cpu_id).view().locking_thread() == old(self).cpu_caches.spec_index(cpu_id).view().locking_thread(),
            final(self).cpu_caches.spec_index(cpu_id).view().being_killed() == old(self).cpu_caches.spec_index(cpu_id).view().being_killed(),
            final(self).global_pool == old(self).global_pool,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
    {
        proof {
            lemma_cache_len_fold_ge_elem(old(self).cpu_caches.view(), cpu_id as int);
        }
        let (node_addr, node_perm) = {
            let cache_mut = self.cpu_caches.borrow_mut(cpu_id, Tracked(lctx), lock_perm);
            let (node_addr, Tracked(node_perm)) = cache_mut.linked_list.pop_head();
            assert(old(self).cpu_caches.spec_index(cpu_id).view().view().linked_list.map().dom().contains(node_addr)) by {
                reveal(LinkedList::wf_perms);
                reveal(LinkedList::wf_map);
            };
            (node_addr, Tracked(node_perm))
        };
        self.total_free_pages = Ghost((self.total_free_pages.view() - 1) as usize);
        proof {
            lemma_cache_len_fold_change_one_array(old(self).cpu_caches, self.cpu_caches, cpu_id);
        }
        (node_addr, node_perm)
    }

    pub fn pop_global_pool_page(&mut self, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
        requires
            old(self).wf(),
            old(self).global_pool.wlocked_by(lctx),
            old(self).global_pool.is_init(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(self).global_pool.locking_thread()->Write_lock_id,
            old(self).global_pool.view().len() > 0,
        ensures
            final(self).wf(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).global_pool.view().view().spec_index(0),
            old(self).global_pool.view().map().dom().contains(ret.0),
            old(self).global_pool.view().map().spec_index(ret.0) == ret.1.view().value().view(),
            final(self).global_pool.view().view() == old(self).global_pool.view().view().skip(1),
            final(self).global_pool.view().map() == old(self).global_pool.view().map().remove(ret.0),
            final(self).total_free_pages.view() == old(self).total_free_pages.view() - 1,
            final(self).global_pool.is_init(),
            final(self).global_pool.wlocked_by(lctx),
            final(self).global_pool.write_lock_perm_match(lock_perm.view()),
            final(self).global_pool.lock_id() == old(self).global_pool.lock_id(),
            final(self).global_pool.locking_thread() == old(self).global_pool.locking_thread(),
            final(self).global_pool.being_killed() == old(self).global_pool.being_killed(),
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
    {
        proof {
            lemma_cache_len_fold_nonneg(old(self).cpu_caches.view());
        }
        let (node_addr, node_perm) = {
            let poll_mut = self.global_pool.borrow_mut(Tracked(lctx), lock_perm);
            let (node_addr, Tracked(node_perm)) = poll_mut.linked_list.pop_head();
            assert(old(self).global_pool.view().map().dom().contains(node_addr)) by {
                reveal(LinkedList::wf_perms);
                reveal(LinkedList::wf_map);
            };
            (node_addr, Tracked(node_perm))
        };
        self.total_free_pages = Ghost((self.total_free_pages.view() - 1) as usize);
        proof {
            self.global_pool.view().lemma_len_view();
            old(self).global_pool.view().lemma_len_view();
            lemma_cache_len_fold_congruence(old(self).cpu_caches.view(), self.cpu_caches.view());
        }
        (node_addr, node_perm)
    }

    pub fn move_global_pool_head_to_cache(
        &mut self,
        cpu_id: CpuId,
        Tracked(lctx): Tracked<&LocalContext>,
        Tracked(cache_lock_perm): Tracked<&LockPerm>,
        Tracked(global_pool_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: (usize, PagePtr))
        requires
            old(self).wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            old(self).cpu_caches.spec_index(cpu_id).view().is_init(),
            cache_lock_perm.state() is WriteLock,
            cache_lock_perm.thread_id() == lctx.thread_id(),
            cache_lock_perm.lock_id()
                == old(self).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(self).global_pool.wlocked_by(lctx),
            old(self).global_pool.is_init(),
            global_pool_lock_perm.state() is WriteLock,
            global_pool_lock_perm.thread_id() == lctx.thread_id(),
            global_pool_lock_perm.lock_id()
                == old(self).global_pool.locking_thread()->Write_lock_id,
            old(self).global_pool.view().len() > 0,
            old(self).cpu_caches.spec_index(cpu_id).view().view().linked_list.len()
                < ALLOCATOR_MAX_WATERMARK,
            !old(self).cpu_caches.spec_index(cpu_id).view().view().view().contains(
                old(self).global_pool.view().view().spec_index(0)),
        ensures
            final(self).wf(),
            ret.1 == old(self).global_pool.view().view().spec_index(0),
            old(self).global_pool.view().map().dom().contains(ret.0),
            old(self).global_pool.view().map().spec_index(ret.0) == ret.1,
            final(self).global_pool.view().view()
                == old(self).global_pool.view().view().skip(1),
            final(self).global_pool.view().map()
                == old(self).global_pool.view().map().remove(ret.0),
            final(self).cpu_caches.spec_index(cpu_id).view().view().view()
                == old(self).cpu_caches.spec_index(cpu_id).view().view().view().insert(0, ret.1),
            final(self).cpu_caches.spec_index(cpu_id).view().view().map()
                == old(self).cpu_caches.spec_index(cpu_id).view().view().map().insert(ret.0, ret.1),
            !old(self).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(ret.0),
            final(self).total_free_pages == old(self).total_free_pages,
            final(self).cpu_caches.entries_unchanged_except(&old(self).cpu_caches, cpu_id),
            final(self).cpu_caches.spec_index(cpu_id).view().is_init(),
            final(self).cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            final(self).cpu_caches.spec_index(cpu_id).view()
                .write_lock_perm_match(cache_lock_perm),
            final(self).cpu_caches.spec_index(cpu_id).view().locking_thread()
                == old(self).cpu_caches.spec_index(cpu_id).view().locking_thread(),
            final(self).cpu_caches.spec_index(cpu_id).view().being_killed()
                == old(self).cpu_caches.spec_index(cpu_id).view().being_killed(),
            final(self).cpu_caches.spec_index(cpu_id).lock_id()
                == old(self).cpu_caches.spec_index(cpu_id).lock_id(),
            final(self).global_pool.is_init(),
            final(self).global_pool.wlocked_by(lctx),
            final(self).global_pool.write_lock_perm_match(global_pool_lock_perm),
            final(self).global_pool.locking_thread()
                == old(self).global_pool.locking_thread(),
            final(self).global_pool.being_killed()
                == old(self).global_pool.being_killed(),
            final(self).global_pool.lock_id()
                == old(self).global_pool.lock_id(),
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
    {
        let ghost old_caches = self.cpu_caches;
        let (node_addr, Tracked(node_perm), page_ptr) = {
            let pool_mut = self.global_pool.borrow_mut(
                Tracked(lctx), Tracked(global_pool_lock_perm),
            );
            let (_, page_ptr) = pool_mut.peek_head();
            let (node_addr, Tracked(node_perm)) = pool_mut.linked_list.pop_head();
            (node_addr, Tracked(node_perm), page_ptr)
        };
        {
            let cache_mut = self.cpu_caches.borrow_mut(
                cpu_id, Tracked(lctx), Tracked(cache_lock_perm),
            );
            assert(cache_mut.linked_list.length != usize::MAX) by { reveal(LinkedList::wf_value_list); };
            cache_mut.linked_list.push_head(node_addr, Tracked(node_perm));
        }
        proof {
            lemma_cache_len_fold_change_one_array(self.cpu_caches, old_caches, cpu_id);
            assert(
                old(self).global_pool.view().len()
                    == self.global_pool.view().len() + 1
            ) by {
                old(self).global_pool.view().lemma_len_view();
                self.global_pool.view().lemma_len_view();
            };
        }
        (node_addr, page_ptr)
    }
}

}
