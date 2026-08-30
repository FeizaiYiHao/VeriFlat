use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;

verus! {

pub struct PageAllocator{
    pub cpu_caches: LockedArray<AllocatorCache, (), (), (), NUM_CPUS, NO_KILL_STATE>,
    pub global_pool: RwLock<GlobalPool, (), (), (), NO_KILL_STATE>,
    pub quota: RwLock<AllocatorQuota, (), (), (), NO_KILL_STATE>,
    pub total_free_pages: Ghost<usize>,

    pub owning_container: RwLockContainerPtr,
}

// The allocator fold lemmas live alongside the allocator.

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
        self.global_pool.inv()
        &&&
        self.cpu_caches_wf()
        &&&
        self.quota_minor_wf()
        &&&
        self.global_pool_minor_wf()
        &&&
        self.total_free_pages_wf()
    }

    pub open spec fn cpu_caches_wf(&self) -> bool {
        &&&
        forall|cpu_i:CpuId|
        #![trigger index_valid(NUM_CPUS, cpu_i)]
        // #![trigger self.cpu_caches.spec_index(cpu_i).inv()]
        index_valid(NUM_CPUS, cpu_i)
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
    pub open spec fn global_pool_minor_wf(&self) -> bool {
        self.global_pool.view().lock_minor() == self.owning_container
    }

    pub open spec fn total_free_pages_wf(&self) -> bool{
        self.global_pool.view().len() + self.cpu_caches.view().fold_left(0int, |sum: int, cpu_rw_lock: RwLock<AllocatorCache, (), (), (), NO_KILL_STATE>| {sum + cpu_rw_lock.view().linked_list.len()}) == self.total_free_pages.view()
    }

    pub open spec fn cpu_caches_unlocked(&self) -> bool {
        &&&
         forall|cpu_i: CpuId|
        #![auto]
        index_valid(NUM_CPUS, cpu_i)
        ==>
        self.cpu_caches.spec_index(cpu_i).view().locked() == false
    }

    pub open spec fn global_pool_unlocked(&self) -> bool{
        self.global_pool.locked() == false
    }

    // pub open spec fn quota_unlocked(&self) -> bool{
    //     self.quota.locked() == false
    // }

    // pub open spec fn internal_lock_id_wf(&self) -> bool{
    //     &&&
    //     self.quota.view().container_depth() == self.global_pool.view().container_depth()
    //     &&&
    //     forall|cpu_i:CpuId|
    //         #![trigger self.cpu_caches.spec_index(cpu_i).container_depth()]
    //         #![trigger self.cpu_caches.spec_index(cpu_i).process_depth()]
    //         index_valid(NUM_CPUS, cpu_i)
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
    /// The acyclicity obligation is passed through to the caller, as for a
    /// direct `RwLock::wlock`.
    ///
    /// `wf()` re-establishes for free: only `quota`'s lock state moves
    /// (`wlock_ensures` preserves `quota.view()`), and the only fold conjunct
    /// `total_free_pages_wf` folds over `cpu_caches` + `global_pool` — both
    /// untouched here — so no fold lemma is needed.
    pub fn wlock_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).wf(),
            wlock_requires(old(self).quota, old(lctx)),
            old(lctx).lock_id_acyclic(old(self).quota.lock_id()),
        ensures
            final(self).wf(),
            // Quota lock acquired.
            wlock_ensures(old(self).quota, final(self).quota, old(self).quota.lock_id(), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), final(self).quota.view(),
                old(self).quota.lock_id(),
                KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())),
            // Other fields untouched.
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
    /// Release the inner `quota` write lock.
    ///
    /// The caller passes `page_size` and `alloc_ptr` so the wrapper can
    /// remove the matching pair from the LocalContext lock-entry set. The
    /// dynamic lock id must match the entry for this object — same contract
    /// as `RwLock::wunlock`.
    ///
    /// `wf()` re-establishes for free: only `quota`'s lock state moves
    /// (`wunlock_ensures` preserves `quota.view()`), and the only fold conjunct
    /// `total_free_pages_wf` folds over `cpu_caches` + `global_pool` — both
    /// untouched here — so no fold lemma is needed.
    pub fn wunlock_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            old(self).quota.wlocked_by(old(lctx)),
            old(self).quota.inv(),


            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).quota.locking_thread()->Write_lock_id,

            old(lctx).lock_entry_contains(
                old(self).quota.lock_id(),
                KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())),
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
            // Other fields untouched.
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).global_pool == old(self).global_pool,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        self.quota.wunlock(Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())))
    }
}

impl PageAllocator{
    /// Acquire the per-cpu `cpu_caches[cpu_id]` write lock. Mirrors `wlock_quota`
    /// but for the array element; builds `KernelObjId::AllocatorCache`. The lock
    /// id is inferred from the array element's traits.
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
            // Other fields untouched.
            final(self).cpu_caches.unchanged_except(&old(self).cpu_caches, cpu_id),
            final(self).global_pool == old(self).global_pool,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let ghost old_caches = self.cpu_caches;
        let ret = self.cpu_caches.wlock(cpu_id, Tracked(lctx), Ghost(KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)));
        proof {
            assert forall|i: usize| index_valid(NUM_CPUS, i)
                implies #[trigger] old_caches.view().spec_index(i as int).view().linked_list.len()
                    == self.cpu_caches.view().spec_index(i as int).view().linked_list.len()
            by {
                if i != cpu_id {
                    assert(self.cpu_caches.spec_index(i) === old_caches.spec_index(i));
                }
            };
            lemma_cache_len_fold_congruence(old_caches.view(), self.cpu_caches.view());
        }
        ret
    }

    /// Release the per-cpu `cpu_caches[cpu_id]` write lock.
    ///
    /// `total_free_pages_wf` folds over live cache lengths, and `wunlock`
    /// preserves the cache's payload `view()` (only lock state changes), so
    /// the fold — and thus `wf()` — is preserved across unlock with no
    /// caller-side length-consistency obligation.
    pub fn wunlock_cache(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(self).cpu_caches.spec_index(cpu_id).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(
                old(self).cpu_caches.spec_index(cpu_id).lock_id(),
                KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)),
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
            // Other fields untouched.
            final(self).cpu_caches.unchanged_except(&old(self).cpu_caches, cpu_id),
            final(self).global_pool == old(self).global_pool,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let ghost old_caches = self.cpu_caches;
        self.cpu_caches.wunlock(cpu_id, Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)));
        proof {
            assert forall|i: usize| index_valid(NUM_CPUS, i)
                implies #[trigger] old_caches.view().spec_index(i as int).view().linked_list.len()
                    == self.cpu_caches.view().spec_index(i as int).view().linked_list.len()
            by {
                if i != cpu_id {
                    assert(self.cpu_caches.spec_index(i) === old_caches.spec_index(i));
                }
            };
            lemma_cache_len_fold_congruence(old_caches.view(), self.cpu_caches.view());
        }
    }

    /// Acquire the inner `global_pool` write lock. Mirrors `wlock_quota`;
    /// builds `KernelObjId::AllocatorGlobalPoll`. The lock id is inferred
    /// from the global pool's traits.
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
            // Other fields untouched.
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

    /// Release the inner `global_pool` write lock. Mirrors `wunlock_quota`.
    pub fn wunlock_global_pool(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            old(self).global_pool.wlocked_by(old(lctx)),
            old(self).global_pool.inv(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(self).global_pool.locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(
                old(self).global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(page_size.view(), alloc_ptr.view())),
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
            // Other fields untouched.
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
            old(self).cpu_caches.spec_index(cpu_id).view().is_init(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            old(self).cpu_caches.spec_index(cpu_id).view()
                .write_lock_perm_match(lock_perm.view()),
            old(self).cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
        ensures
            final(self).wf(),
            // ---- popped node ----
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).cpu_caches.spec_index(cpu_id).view().view().view().spec_index(0),
            old(self).cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(ret.0),
            old(self).cpu_caches.spec_index(cpu_id).view().view().map().spec_index(ret.0) == ret.1.view().value().view(),
            // ---- cache shrank by the popped head, total rebalanced ----
            final(self).cpu_caches.spec_index(cpu_id).view().view().view() == old(self).cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
            final(self).cpu_caches.spec_index(cpu_id).view().view().map() == old(self).cpu_caches.spec_index(cpu_id).view().view().map().remove(ret.0),
            final(self).total_free_pages.view() == old(self).total_free_pages.view() - 1,
            // ---- lock state of the touched cache preserved, others untouched ----
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

    // Global-pool twin of `pop_cache_page`: pop the head off the write-locked
    // `global_pool` list and rebalance `total_free_pages`. Conservation is
    // simpler than the cache case -- `total_free_pages_wf` folds `global_pool.len()
    // + fold(cpu_caches)`, and here `global_pool.len()` drops by 1 while the whole
    // `cpu_caches` array is byte-unchanged (so its fold is congruent).
    pub fn pop_global_pool_page(&mut self, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
        requires
            old(self).wf(),
            old(self).global_pool.is_init(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            old(self).global_pool.write_lock_perm_match(lock_perm.view()),
            old(self).global_pool.view().len() > 0,
        ensures
            final(self).wf(),
            // ---- popped node ----
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(self).global_pool.view().view().spec_index(0),
            old(self).global_pool.view().map().dom().contains(ret.0),
            old(self).global_pool.view().map().spec_index(ret.0) == ret.1.view().value().view(),
            // ---- pool shrank by the popped head, total rebalanced ----
            final(self).global_pool.view().view() == old(self).global_pool.view().view().skip(1),
            final(self).global_pool.view().map() == old(self).global_pool.view().map().remove(ret.0),
            final(self).total_free_pages.view() == old(self).total_free_pages.view() - 1,
            // ---- lock state of global_pool preserved, others untouched ----
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

    /// Move the global-pool head into one write-locked CPU cache.  The total
    /// number of free pages is unchanged: the pool loses one entry and the
    /// selected cache gains that same entry.
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
            assert(cache_mut.linked_list.length != usize::MAX) by {
                reveal(LinkedList::wf_value_list);
            };
            cache_mut.linked_list.push_head(node_addr, Tracked(node_perm));
        }
        proof {
            lemma_cache_len_fold_change_one_array(
                self.cpu_caches, old_caches, cpu_id,
            );
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

/*
impl PageAllocator{
    /// Acquire the inner `global_pool` write lock. Mirrors `wlock_quota`;
    /// builds `KernelObjId::AllocatorGlobalPoll`. The lock id is inferred
    /// from the global pool's traits.
    pub fn wlock_global_pool(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).wf(),
            wlock_requires(old(self).global_pool, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).global_pool@.container_depth(),
                process: old(self).global_pool@.process_depth(),
                major: old(self).global_pool@.current_lock_major(),
                minor: old(self).global_pool@.lock_minor(),
            }),
            !old(lctx).lock_obj_contains(KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr@)),
        ensures
            final(self).wf(),
            wlock_ensures(old(self).global_pool, final(self).global_pool, LockId{
                container: old(self).global_pool@.container_depth(),
                process: old(self).global_pool@.process_depth(),
                major: old(self).global_pool@.current_lock_major(),
                minor: old(self).global_pool@.lock_minor(),
            }, final(lctx), ret@),
            lock_ensures(old(lctx), final(lctx), final(self).global_pool.view(), LockId{
                container: old(self).global_pool@.container_depth(),
                process: old(self).global_pool@.process_depth(),
                major: old(self).global_pool@.current_lock_major(),
                minor: old(self).global_pool@.lock_minor(),
            }, KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr@)),
            // Other fields untouched.
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let lock_id = Ghost(LockId{
            container: self.global_pool@.container_depth(),
            process: self.global_pool@.process_depth(),
            major: self.global_pool@.current_lock_major(),
            minor: self.global_pool@.lock_minor(),
        });
        self.global_pool.wlock(Tracked(lctx), lock_id, Ghost(KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr@)))
    }

    /// Release the inner `global_pool` write lock. Mirrors `wunlock_quota`.
    pub fn wunlock_global_pool(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            old(self).global_pool.wlocked_by(old(lctx)),
            old(self).global_pool.inv(),

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self).global_pool.locking_thread()->Write_lock_id,

            old(lctx).lock_entry_contains(
                old(self).global_pool.lock_id(),
                KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr@)),
        ensures
            final(self).wf(),
            wunlock_ensures(old(self).global_pool, final(self).global_pool),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).global_pool.view(),
                lock_perm@.lock_id(),
                KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr@),
                lock_perm@.ordering_lock_id(),
            ),
            // Other fields untouched.
            final(self).cpu_caches == old(self).cpu_caches,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        self.global_pool.wunlock(Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorGlobalPoll(page_size@, alloc_ptr@)))
    }

    /// Acquire the per-cpu `cpu_caches[cpu_id]` write lock. Builds
    /// `KernelObjId::AllocatorCache`. The lock id is inferred from the
    /// array element's traits.
    pub fn wlock_cache(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            old(self).wf(),
            index_valid(NUM_CPUS, cpu_id),
            wlock_requires(old(self).cpu_caches[cpu_id]@, old(lctx)),
            old(lctx).lock_id_acyclic(LockId{
                container: old(self).cpu_caches[cpu_id].container_depth(),
                process: old(self).cpu_caches[cpu_id].process_depth(),
                major: old(self).cpu_caches[cpu_id]@@.current_lock_major(),
                minor: old(self).cpu_caches[cpu_id].lock_minor(),
            }),
            !old(lctx).lock_obj_contains(
                KernelObjId::AllocatorCache(page_size@, alloc_ptr@, cpu_id)),
        ensures
            final(self).wf(),
            wlock_ensures(old(self).cpu_caches[cpu_id]@, final(self).cpu_caches[cpu_id]@, LockId{
                container: old(self).cpu_caches[cpu_id].container_depth(),
                process: old(self).cpu_caches[cpu_id].process_depth(),
                major: old(self).cpu_caches[cpu_id]@@.current_lock_major(),
                minor: old(self).cpu_caches[cpu_id].lock_minor(),
            }, final(lctx), ret@),
            lock_ensures(old(lctx), final(lctx), final(self).cpu_caches[cpu_id]@@, LockId{
                container: old(self).cpu_caches[cpu_id].container_depth(),
                process: old(self).cpu_caches[cpu_id].process_depth(),
                major: old(self).cpu_caches[cpu_id]@@.current_lock_major(),
                minor: old(self).cpu_caches[cpu_id].lock_minor(),
            }, KernelObjId::AllocatorCache(page_size@, alloc_ptr@, cpu_id)),
            // Other fields untouched.
            final(self).cpu_caches.unchanged_except(&old(self).cpu_caches, cpu_id),
            final(self).global_pool == old(self).global_pool,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let ghost old_caches = self.cpu_caches;
        let ret = self.cpu_caches.wlock(cpu_id, Tracked(lctx), Ghost(KernelObjId::AllocatorCache(page_size@, alloc_ptr@, cpu_id)));
        proof {
            // total_free_pages_wf: the fold over cache lengths is preserved.
            // wlock only moves cpu_caches[cpu_id]'s lock state; its payload
            // view() (hence linked_list.len()) is preserved (wlock_ensures),
            // and every other slot is unchanged (unchanged_except).
            old_caches.lemma_view_len();
            self.cpu_caches.lemma_view_len();
            assert forall|i: int| 0 <= i < old_caches.view().len()
                implies #[trigger] old_caches.view()[i].view().linked_list.len()
                    == self.cpu_caches.view()[i].view().linked_list.len()
            by {
                if i != cpu_id as int {
                    assert(self.cpu_caches[i as usize] === old_caches[i as usize]);
                }
            };
            lemma_cache_len_fold_congruence(old_caches.view(), self.cpu_caches.view());
        }
        ret
    }

    /// Release the per-cpu `cpu_caches[cpu_id]` write lock.
    ///
    /// `total_free_pages_wf` folds over live cache lengths, and `wunlock`
    /// preserves the cache's payload `view()` (only lock state changes), so
    /// the fold — and thus `wf()` — is preserved across unlock with no
    /// caller-side length-consistency obligation.
    pub fn wunlock_cache(&mut self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            old(self).wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(self).cpu_caches[cpu_id]@.wlocked_by(old(lctx)),
            old(self).cpu_caches[cpu_id]@.being_killed() == false,

            lock_perm@.state() is WriteLock,
            lock_perm@.thread_id() == old(lctx).thread_id(),
            lock_perm@.lock_id() == old(self).cpu_caches[cpu_id]@.locking_thread()->Write_lock_id,

            old(lctx).lock_entry_contains(
                old(self).cpu_caches[cpu_id].lock_id(),
                KernelObjId::AllocatorCache(page_size@, alloc_ptr@, cpu_id)),
        ensures
            final(self).wf(),
            wunlock_ensures(old(self).cpu_caches[cpu_id]@, final(self).cpu_caches[cpu_id]@),
            unlock_ensures(
                old(lctx),
                final(lctx),
                final(self).cpu_caches[cpu_id]@@,
                lock_perm@.lock_id(),
                KernelObjId::AllocatorCache(page_size@, alloc_ptr@, cpu_id),
                lock_perm@.ordering_lock_id(),
            ),
            // Other fields untouched.
            final(self).cpu_caches.unchanged_except(&old(self).cpu_caches, cpu_id),
            final(self).global_pool == old(self).global_pool,
            final(self).quota == old(self).quota,
            final(self).owning_container == old(self).owning_container,
            final(self).total_free_pages == old(self).total_free_pages,
    {
        let ghost old_caches = self.cpu_caches;
        self.cpu_caches.wunlock(cpu_id, Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorCache(page_size@, alloc_ptr@, cpu_id)));
        proof {
            // total_free_pages_wf: fold preserved — wunlock keeps the payload
            // view() (wunlock_ensures) and every other slot (unchanged_except).
            old_caches.lemma_view_len();
            self.cpu_caches.lemma_view_len();
            assert forall|i: int| 0 <= i < old_caches.view().len()
                implies #[trigger] old_caches.view()[i].view().linked_list.len()
                    == self.cpu_caches.view()[i].view().linked_list.len()
            by {
                if i != cpu_id as int {
                    assert(self.cpu_caches[i as usize] === old_caches[i as usize]);
                }
            };
            lemma_cache_len_fold_congruence(old_caches.view(), self.cpu_caches.view());
        }
    }

    // pub fn try_allocate_quota(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, quota: usize, cpu_id: CpuId) -> (ret :bool)
    //     requires
    //         old(self).wf(),
    //         old(self).cpu_caches_unlocked(),
    //         old(self).global_pool_unlocked(),
    //         // old(self).quota_unlocked(),
    //         old(self).local_quota_clean(cpu_id),
    //         index_valid(NUM_CPUS, cpu_id),
    //         old(lctx).thread_id() == cpu_id,

    //         wlock_requires(old(self).cpu_caches.spec_index(cpu_id).view(), old(lctx)),
    //         // wlock_requires(old(self).quota, old(lctx)),
    //         wlock_requires(old(self).global_pool, old(lctx)),

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
    //             self.global_pool_unlocked()
    //             &&&
    //             self.quota_unlocked()
    //             &&&
    //             self.cpu_caches == old(self).cpu_caches
    //             &&&
    //             self.global_pool == old(self).global_pool
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
    //         assert(self.global_pool.inv());
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
*/

}
