use vstd::prelude::*;

use crate::*;
use vstd::simple_pptr::*;

verus! {
#[verifier::reject_recursive_types(SIZE)]
pub struct PageAllocator<const SIZE: usize> {
    pub cpu_caches: LockedArray<AllocatorCache<SIZE>, (), (), NUM_CPUS, NO_KILL_STATE>,
    pub global_pool: RwLock<GlobalPool<SIZE>, (), (), NO_KILL_STATE>,
    pub quota: RwLock<AllocatorQuota<SIZE>, (), (), NO_KILL_STATE>,
    pub total_free_pages: Ghost<usize>,

    pub owning_container: RwLockContainerPtr,
}

impl<const SIZE: usize> LockInvTrait for PageAllocator<SIZE> {
    open spec fn inv(&self) -> bool {
        &&& self.wf()
        &&& self.quota.inv()
    }
}

impl<const SIZE: usize> PageAllocator<SIZE> {
    pub fn new_with_global_pool(owning_container: RwLockContainerPtr, container_depth: usize, linked_list: LinkedList<PagePtr, 233>, quota_value: usize) -> (ret: Self)
        requires
            linked_list.wf(),
            linked_list.container_depth.view() == Some(container_depth),
            linked_list.minor.view() == Some(owning_container),
        ensures
            ret.inv(),
            ret.owning_container == owning_container,
            ret.total_free_pages.view() == linked_list.view().len(),
            ret.quota.view().view() == quota_value,
            ret.quota.view().container_depth == container_depth,
            ret.quota.view().lock_minor() == seq![owning_container],
            !ret.quota.locked(),
            ret.global_pool.view().view() == linked_list.view(),
            ret.global_pool.view().map() == linked_list.map(),
            !ret.global_pool.locked(),
            forall|cpu_id: CpuId| #![trigger ret.cpu_caches.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> {
                    &&& ret.cpu_caches.spec_index(cpu_id).view().view().linked_list.view() == Seq::<PagePtr>::empty()
                    &&& ret.cpu_caches.spec_index(cpu_id).view().view().linked_list.map() == Map::<usize, PagePtr>::empty()
                    &&& !ret.cpu_caches.spec_index(cpu_id).view().locked()
                },
    {
        assert(linked_list.view().len() == linked_list.length) by { linked_list.wf_implies_view_len_eq_len(); };
        let mut cache_array: Array<RwLock<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>, NUM_CPUS> = Array::new();
        let mut cpu_id = 0;
        while cpu_id < NUM_CPUS
            invariant
                cache_array.wf(),
                0 <= cpu_id <= NUM_CPUS,
                forall|i: CpuId| #![trigger cache_array.spec_index(i)]
                    index_valid(NUM_CPUS, i) && i < cpu_id ==> {
                        &&& cache_array.spec_index(i).inv()
                        &&& cache_array.spec_index(i).view().linked_list.view() == Seq::<PagePtr>::empty()
                        &&& cache_array.spec_index(i).view().linked_list.map() == Map::<usize, PagePtr>::empty()
                        &&& !cache_array.spec_index(i).locked()
                    },
                forall|i: int| #![trigger cache_array.view().spec_index(i)] 0 <= i < cpu_id ==> cache_array.view().spec_index(i).view().linked_list.view().len() == 0,
            decreases NUM_CPUS - cpu_id,
        {
            let cache = AllocatorCache { linked_list: LinkedList::new(Some(container_depth), Some(cpu_id)) };
            cache_array.set(cpu_id, RwLock::new_unlocked(cache, (), Ghost(())));
            cpu_id = cpu_id + 1;
        }
        let total_free_pages = linked_list.length;
        let cpu_caches = LockedArray::from_array(cache_array);
        let global_pool = RwLock::new_unlocked(GlobalPool { linked_list }, (), Ghost(()));
        let quota = RwLock::new_unlocked(AllocatorQuota { value: quota_value, minor: Ghost(owning_container), container_depth }, (), Ghost(()));
        let ret = Self { cpu_caches, global_pool, quota, total_free_pages: Ghost(total_free_pages), owning_container };
        proof { lemma_cache_len_fold_all_zero(ret.cpu_caches.view()); ret.global_pool.view().wf_implies_view_len_eq_len(); }
        ret
    }

    pub fn new_empty(owning_container: RwLockContainerPtr, container_depth: usize) -> (ret: Self)
        ensures
            ret.inv(),
            ret.owning_container == owning_container,
            ret.total_free_pages.view() == 0,
            ret.quota.view().view() == 0,
            ret.quota.view().container_depth == container_depth,
            ret.quota.view().lock_minor() == seq![owning_container],
            !ret.quota.locked(),
            ret.global_pool.view().view() == Seq::<PagePtr>::empty(),
            ret.global_pool.view().map() == Map::<usize, PagePtr>::empty(),
            !ret.global_pool.locked(),
            forall|cpu_id: CpuId| #![trigger ret.cpu_caches.spec_index(cpu_id)]
                index_valid(NUM_CPUS, cpu_id) ==> {
                    &&& ret.cpu_caches.spec_index(cpu_id).view().view().linked_list.view() == Seq::<PagePtr>::empty()
                    &&& ret.cpu_caches.spec_index(cpu_id).view().view().linked_list.map() == Map::<usize, PagePtr>::empty()
                    &&& !ret.cpu_caches.spec_index(cpu_id).view().locked()
                },
    {
        let mut cache_array: Array<RwLock<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>, NUM_CPUS> = Array::new();
        let mut cpu_id = 0;
        while cpu_id < NUM_CPUS
            invariant
                cache_array.wf(),
                0 <= cpu_id <= NUM_CPUS,
                forall|i: CpuId| #![trigger cache_array.spec_index(i)]
                    index_valid(NUM_CPUS, i) && i < cpu_id ==> {
                        &&& cache_array.spec_index(i).inv()
                        &&& cache_array.spec_index(i).view().linked_list.view() == Seq::<PagePtr>::empty()
                        &&& cache_array.spec_index(i).view().linked_list.map() == Map::<usize, PagePtr>::empty()
                        &&& !cache_array.spec_index(i).locked()
                    },
                forall|i: int| #![trigger cache_array.view().spec_index(i)]
                    0 <= i < cpu_id ==> cache_array.view().spec_index(i).view().linked_list.view().len() == 0,
            decreases NUM_CPUS - cpu_id,
        {
            let cache = AllocatorCache { linked_list: LinkedList::new(Some(container_depth), Some(cpu_id)) };
            cache_array.set(cpu_id, RwLock::new_unlocked(cache, (), Ghost(())));
            cpu_id = cpu_id + 1;
        }
        let cpu_caches = LockedArray::from_array(cache_array);
        let global_pool = RwLock::new_unlocked(GlobalPool { linked_list: LinkedList::new(Some(container_depth), Some(owning_container)) }, (), Ghost(()));
        let quota = RwLock::new_unlocked(AllocatorQuota { value: 0, minor: Ghost(owning_container), container_depth }, (), Ghost(()));
        let ret = Self { cpu_caches, global_pool, quota, total_free_pages: Ghost(0), owning_container };
        proof { lemma_cache_len_fold_all_zero(ret.cpu_caches.view()); }
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
        forall|cpu_i: CpuId| #![trigger self.cpu_caches.spec_index(cpu_i)] index_valid(NUM_CPUS, cpu_i) ==> self.cpu_caches.spec_index(cpu_i).inv()
    }

    /// The quota's intrinsic minor lock id is the owning container pointer.
    /// `AllocatorQuota` sits in a bare `RwLock` (not in a wrapper that
    /// provides a minor), so it carries its own `Ghost<usize>` minor field;
    /// this invariant pins that minor to `owning_container`.
    pub open spec fn quota_minor_wf(&self) -> bool { self.quota.view().lock_minor() == seq![self.owning_container] }

    /// The global pool's intrinsic minor lock id is the owning container
    /// pointer. Same reasoning as `quota_minor_wf` — `LinkedList` carries
    /// its own minor.
    pub open spec fn global_pool_minor_wf(&self) -> bool { self.global_pool.view().lock_minor() == seq![self.owning_container] }

    pub open spec fn total_free_pages_wf(&self) -> bool {
        self.global_pool.view().len() + self.cpu_caches.view().fold_left(0int, |sum: int, cpu_rw_lock: RwLock<AllocatorCache<SIZE>, (), (), NO_KILL_STATE>| { sum + cpu_rw_lock.view().linked_list.len() }) == self.total_free_pages.view()
    }
}

impl<const SIZE: usize> PageAllocator<SIZE> {
    pub fn wlock_quota(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>,
        Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            wlock_requires(old(perm).value().quota, old(lctx)),
            old(lctx).lock_id_acyclic(old(perm).value().quota.lock_id()),
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(perm).value().wf(),
            wlock_ensures(old(perm).value().quota, final(perm).value().quota, old(perm).value().quota.lock_id(), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(perm).value().quota.lock_id(), KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())),
            final(perm).value().cpu_caches == old(perm).value().cpu_caches,
            final(perm).value().global_pool == old(perm).value().global_pool,
            final(perm).value().owning_container == old(perm).value().owning_container,
            final(perm).value().total_free_pages == old(perm).value().total_free_pages,
    {
        let lock_id = Ghost(old(perm).value().quota.lock_id());
        wlock_quota::<SIZE>(pptr, Tracked(perm), Tracked(lctx), lock_id, Ghost(KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())))
    }

    pub fn wunlock_quota(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>,
        Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            old(perm).value().quota.wlocked_by(old(lctx)),
            old(perm).value().quota.inv(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(perm).value().quota.locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(perm).value().quota.lock_id(), KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())),
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(perm).value().wf(),
            final(perm).value().quota.lock_id() == old(perm).value().quota.lock_id(),
            wunlock_ensures(old(perm).value().quota, final(perm).value().quota),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view()), old(perm).value().quota.lock_id()),
            final(perm).value().cpu_caches == old(perm).value().cpu_caches,
            final(perm).value().global_pool == old(perm).value().global_pool,
            final(perm).value().owning_container == old(perm).value().owning_container,
            final(perm).value().total_free_pages == old(perm).value().total_free_pages,
    {
        wunlock_quota::<SIZE>(pptr, Tracked(perm), Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorQuota(page_size.view(), alloc_ptr.view())))
    }

    pub fn wlock_cache(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            index_valid(NUM_CPUS, cpu_id),
            wlock_requires(old(perm).value().cpu_caches.spec_index(cpu_id).view(), old(lctx)),
            old(lctx).lock_id_acyclic(old(perm).value().cpu_caches.lock_id_by_index(cpu_id)),
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(perm).value().wf(),
            wlock_ensures(old(perm).value().cpu_caches.spec_index(cpu_id).view(), final(perm).value().cpu_caches.spec_index(cpu_id).view(), old(perm).value().cpu_caches.lock_id_by_index(cpu_id), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(perm).value().cpu_caches.lock_id_by_index(cpu_id), KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)),
            final(perm).value().cpu_caches.unchanged_except(&old(perm).value().cpu_caches, cpu_id),
            final(perm).value().global_pool == old(perm).value().global_pool,
            final(perm).value().quota == old(perm).value().quota,
            final(perm).value().owning_container == old(perm).value().owning_container,
            final(perm).value().total_free_pages == old(perm).value().total_free_pages,
    {
        let ghost old_caches = perm.value().cpu_caches;
        let ret = wlock_cache::<SIZE>(pptr, Tracked(&mut *perm), cpu_id, Tracked(lctx), Ghost(KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)));
        assert(perm.value().total_free_pages_wf()) by { old_caches.view_index_eq_element_value(); perm.value().cpu_caches.view_index_eq_element_value(); lemma_cache_len_fold_congruence(old_caches.view(), perm.value().cpu_caches.view()); };
        ret
    }

    pub fn wunlock_cache(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, cpu_id: CpuId,
        Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(perm).value().cpu_caches.spec_index(cpu_id).view().wlocked_by(old(lctx)),
            old(perm).value().cpu_caches.spec_index(cpu_id).view().being_killed() == false,
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(perm).value().cpu_caches.spec_index(cpu_id).lock_id(), KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)),
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(perm).value().wf(),
            final(perm).value().cpu_caches.spec_index(cpu_id).lock_id() == old(perm).value().cpu_caches.spec_index(cpu_id).lock_id(),
            wunlock_ensures(old(perm).value().cpu_caches.spec_index(cpu_id).view(), final(perm).value().cpu_caches.spec_index(cpu_id).view()),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id), old(perm).value().cpu_caches.spec_index(cpu_id).lock_id()),
            final(perm).value().cpu_caches.unchanged_except(&old(perm).value().cpu_caches, cpu_id),
            final(perm).value().global_pool == old(perm).value().global_pool,
            final(perm).value().quota == old(perm).value().quota,
            final(perm).value().owning_container == old(perm).value().owning_container,
            final(perm).value().total_free_pages == old(perm).value().total_free_pages,
    {
        let ghost old_caches = perm.value().cpu_caches;
        wunlock_cache::<SIZE>(pptr, Tracked(&mut *perm), cpu_id, Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorCache(page_size.view(), alloc_ptr.view(), cpu_id)));
        assert(perm.value().total_free_pages_wf()) by { old_caches.view_index_eq_element_value(); perm.value().cpu_caches.view_index_eq_element_value(); lemma_cache_len_fold_congruence(old_caches.view(), perm.value().cpu_caches.view()); };
    }

    pub fn wlock_global_pool(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>,
        Tracked(lctx): Tracked<&mut LocalContext>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>) -> (ret: Tracked<LockPerm>)
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            wlock_requires(old(perm).value().global_pool, old(lctx)),
            old(lctx).lock_id_acyclic(old(perm).value().global_pool.lock_id()),
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(perm).value().wf(),
            wlock_ensures(old(perm).value().global_pool, final(perm).value().global_pool, old(perm).value().global_pool.lock_id(), final(lctx), ret.view()),
            lock_ensures(old(lctx), final(lctx), old(perm).value().global_pool.lock_id(), KernelObjId::AllocatorGlobalPool(page_size.view(), alloc_ptr.view())),
            final(perm).value().cpu_caches == old(perm).value().cpu_caches,
            final(perm).value().quota == old(perm).value().quota,
            final(perm).value().owning_container == old(perm).value().owning_container,
            final(perm).value().total_free_pages == old(perm).value().total_free_pages,
    {
        let lock_id = Ghost(old(perm).value().global_pool.lock_id());
        wlock_global_pool::<SIZE>(pptr, Tracked(perm), Tracked(lctx), lock_id, Ghost(KernelObjId::AllocatorGlobalPool(page_size.view(), alloc_ptr.view())))
    }

    pub fn wunlock_global_pool(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>,
        Tracked(lctx): Tracked<&mut LocalContext>, lock_perm: Tracked<LockPerm>, page_size: Ghost<PageSize>, alloc_ptr: Ghost<RwLockPageAllocatorPtr>)
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            old(perm).value().global_pool.wlocked_by(old(lctx)),
            old(perm).value().global_pool.inv(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == old(lctx).thread_id(),
            lock_perm.view().lock_id() == old(perm).value().global_pool.locking_thread()->Write_lock_id,
            old(lctx).lock_entry_contains(old(perm).value().global_pool.lock_id(), KernelObjId::AllocatorGlobalPool(page_size.view(), alloc_ptr.view())),
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(perm).value().wf(),
            final(perm).value().global_pool.lock_id() == old(perm).value().global_pool.lock_id(),
            wunlock_ensures(old(perm).value().global_pool, final(perm).value().global_pool),
            unlock_ensures(old(lctx), final(lctx), KernelObjId::AllocatorGlobalPool(page_size.view(), alloc_ptr.view()), old(perm).value().global_pool.lock_id()),
            final(perm).value().cpu_caches == old(perm).value().cpu_caches,
            final(perm).value().quota == old(perm).value().quota,
            final(perm).value().owning_container == old(perm).value().owning_container,
            final(perm).value().total_free_pages == old(perm).value().total_free_pages,
    {
        wunlock_global_pool::<SIZE>(pptr, Tracked(perm), Tracked(lctx), lock_perm, Ghost(KernelObjId::AllocatorGlobalPool(page_size.view(), alloc_ptr.view())))
    }

    pub fn push_cache_page(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, cpu_id: CpuId,
        node_addr: usize, node_perm: Tracked<PointsTo<Node<PagePtr>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>)
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(perm).value().cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            old(perm).value().cpu_caches.spec_index(cpu_id).view().is_init(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(perm).value().cpu_caches.spec_index(cpu_id).view().view().view().len() < ALLOCATOR_MAX_WATERMARK,
            node_perm.view().is_init(),
            !old(perm).value().cpu_caches.spec_index(cpu_id).view().view().view().contains(node_perm.view().value().view()),
            node_perm.view().addr() == node_addr,
            old(perm).value().total_free_pages.view() < usize::MAX,
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(perm).value().wf(),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().view().view() == old(perm).value().cpu_caches.spec_index(cpu_id).view().view().view().insert(0, node_perm.view().value().view()),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().view().map() == old(perm).value().cpu_caches.spec_index(cpu_id).view().view().map().insert(node_addr, node_perm.view().value().view()),
            !old(perm).value().cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(node_addr),
            final(perm).value().total_free_pages.view() == old(perm).value().total_free_pages.view() + 1,
            final(perm).value().cpu_caches.entries_unchanged_except(&old(perm).value().cpu_caches, cpu_id),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().is_init(),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().write_lock_perm_match(lock_perm.view()),
            final(perm).value().cpu_caches.spec_index(cpu_id).lock_id() == old(perm).value().cpu_caches.spec_index(cpu_id).lock_id(),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread() == old(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread(),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().being_killed() == old(perm).value().cpu_caches.spec_index(cpu_id).view().being_killed(),
            final(perm).value().global_pool == old(perm).value().global_pool,
            final(perm).value().quota == old(perm).value().quota,
            final(perm).value().owning_container == old(perm).value().owning_container,
    {
        {
            let cache = borrow_mut_cache(pptr, Tracked(&mut *perm), cpu_id, Tracked(lctx), lock_perm);
            assert(cache.linked_list.length != usize::MAX) by { cache.linked_list.wf_implies_view_len_eq_len(); };
            cache.linked_list.push_head(node_addr, node_perm);
        }
        proof { set_total_free_pages_ghost(perm, (perm.value().total_free_pages.view() + 1) as usize); }
        assert(perm.value().wf()) by { lemma_cache_len_fold_change_one_array(perm.value().cpu_caches, old(perm).value().cpu_caches, cpu_id); };
    }

    pub fn pop_cache_page(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, cpu_id: CpuId,
        Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            index_valid(NUM_CPUS, cpu_id),
            old(perm).value().cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            old(perm).value().cpu_caches.spec_index(cpu_id).view().is_init(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
            old(perm).value().cpu_caches.spec_index(cpu_id).view().view().view().len() > 0,
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(perm).value().wf(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(perm).value().cpu_caches.spec_index(cpu_id).view().view().view().spec_index(0),
            old(perm).value().cpu_caches.spec_index(cpu_id).view().view().map().dom().contains(ret.0),
            old(perm).value().cpu_caches.spec_index(cpu_id).view().view().map().spec_index(ret.0) == ret.1.view().value().view(),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().view().view() == old(perm).value().cpu_caches.spec_index(cpu_id).view().view().view().skip(1),
            !final(perm).value().cpu_caches.spec_index(cpu_id).view().view().view().contains(ret.1.view().value().view()),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().view().map() == old(perm).value().cpu_caches.spec_index(cpu_id).view().view().map().remove(ret.0),
            final(perm).value().total_free_pages.view() == old(perm).value().total_free_pages.view() - 1,
            final(perm).value().cpu_caches.entries_unchanged_except(&old(perm).value().cpu_caches, cpu_id),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().is_init(),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().wlocked_by(lctx),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().write_lock_perm_match(lock_perm.view()),
            final(perm).value().cpu_caches.spec_index(cpu_id).lock_id() == old(perm).value().cpu_caches.spec_index(cpu_id).lock_id(),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread() == old(perm).value().cpu_caches.spec_index(cpu_id).view().locking_thread(),
            final(perm).value().cpu_caches.spec_index(cpu_id).view().being_killed() == old(perm).value().cpu_caches.spec_index(cpu_id).view().being_killed(),
            final(perm).value().global_pool == old(perm).value().global_pool,
            final(perm).value().quota == old(perm).value().quota,
            final(perm).value().owning_container == old(perm).value().owning_container,
    {
        proof { lemma_cache_len_fold_ge_elem(old(perm).value().cpu_caches.view(), cpu_id as int); }
        let (node_addr, node_perm) = {
            let cache_mut = borrow_mut_cache(pptr, Tracked(&mut *perm), cpu_id, Tracked(lctx), lock_perm);
            let (node_addr, Tracked(node_perm)) = cache_mut.linked_list.pop_head();
            (node_addr, Tracked(node_perm))
        };
        proof {
            set_total_free_pages_ghost(perm, (perm.value().total_free_pages.view() - 1) as usize);
            lemma_cache_len_fold_change_one_array(old(perm).value().cpu_caches, perm.value().cpu_caches, cpu_id);
        }
        (node_addr, node_perm)
    }

    pub fn push_global_pool_page(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, node_addr: usize,
        node_perm: Tracked<PointsTo<Node<PagePtr>>>, Tracked(lctx): Tracked<&LocalContext>, lock_perm: Tracked<&LockPerm>)
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            old(perm).value().global_pool.wlocked_by(lctx),
            old(perm).value().global_pool.is_init(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(perm).value().global_pool.locking_thread()->Write_lock_id,
            node_perm.view().is_init(),
            node_perm.view().addr() == node_addr,
            !old(perm).value().global_pool.view().view().contains(node_perm.view().value().view()),
            old(perm).value().total_free_pages.view() < usize::MAX,
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(perm).value().wf(),
            final(perm).value().global_pool.view().view() == old(perm).value().global_pool.view().view().insert(0, node_perm.view().value().view()),
            final(perm).value().global_pool.view().map() == old(perm).value().global_pool.view().map().insert(node_addr, node_perm.view().value().view()),
            !old(perm).value().global_pool.view().map().dom().contains(node_addr),
            final(perm).value().total_free_pages.view() == old(perm).value().total_free_pages.view() + 1,
            final(perm).value().global_pool.is_init(),
            final(perm).value().global_pool.wlocked_by(lctx),
            final(perm).value().global_pool.write_lock_perm_match(lock_perm.view()),
            final(perm).value().global_pool.lock_id() == old(perm).value().global_pool.lock_id(),
            final(perm).value().global_pool.locking_thread() == old(perm).value().global_pool.locking_thread(),
            final(perm).value().global_pool.being_killed() == old(perm).value().global_pool.being_killed(),
            final(perm).value().cpu_caches == old(perm).value().cpu_caches,
            final(perm).value().quota == old(perm).value().quota,
            final(perm).value().owning_container == old(perm).value().owning_container,
    {
        assert(perm.value().global_pool.view().linked_list.length != usize::MAX) by { lemma_cache_len_fold_nonneg(perm.value().cpu_caches.view()); perm.value().global_pool.view().linked_list.wf_implies_view_len_eq_len(); };
        {
            let pool = borrow_mut_global_pool(pptr, Tracked(&mut *perm), Tracked(lctx), lock_perm);
            pool.linked_list.push_head(node_addr, node_perm);
        }
        proof { set_total_free_pages_ghost(perm, (perm.value().total_free_pages.view() + 1) as usize); }
        assert(perm.value().wf()) by { perm.value().global_pool.view().wf_implies_view_len_eq_len(); old(perm).value().global_pool.view().wf_implies_view_len_eq_len(); };
    }

    pub fn pop_global_pool_page(pptr: &PPtr<PageAllocator<SIZE>>, Tracked(perm): Tracked<&mut PointsTo<PageAllocator<SIZE>>>, Tracked(lctx): Tracked<&LocalContext>,
        lock_perm: Tracked<&LockPerm>) -> (ret: (usize, Tracked<PointsTo<Node<PagePtr>>>))
        requires
            pptr.addr() == old(perm).addr(),
            old(perm).is_init(),
            old(perm).value().wf(),
            old(perm).value().global_pool.wlocked_by(lctx),
            old(perm).value().global_pool.is_init(),
            lock_perm.view().state() is WriteLock,
            lock_perm.view().thread_id() == lctx.thread_id(),
            lock_perm.view().lock_id() == old(perm).value().global_pool.locking_thread()->Write_lock_id,
            old(perm).value().global_pool.view().len() > 0,
        ensures
            final(perm).addr() == old(perm).addr(),
            final(perm).is_init(),
            final(perm).value().wf(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == old(perm).value().global_pool.view().view().spec_index(0),
            old(perm).value().global_pool.view().map().dom().contains(ret.0),
            old(perm).value().global_pool.view().map().spec_index(ret.0) == ret.1.view().value().view(),
            final(perm).value().global_pool.view().view() == old(perm).value().global_pool.view().view().skip(1),
            final(perm).value().global_pool.view().map() == old(perm).value().global_pool.view().map().remove(ret.0),
            final(perm).value().total_free_pages.view() == old(perm).value().total_free_pages.view() - 1,
            final(perm).value().global_pool.is_init(),
            final(perm).value().global_pool.wlocked_by(lctx),
            final(perm).value().global_pool.write_lock_perm_match(lock_perm.view()),
            final(perm).value().global_pool.lock_id() == old(perm).value().global_pool.lock_id(),
            final(perm).value().global_pool.locking_thread() == old(perm).value().global_pool.locking_thread(),
            final(perm).value().global_pool.being_killed() == old(perm).value().global_pool.being_killed(),
            final(perm).value().cpu_caches == old(perm).value().cpu_caches,
            final(perm).value().quota == old(perm).value().quota,
            final(perm).value().owning_container == old(perm).value().owning_container,
    {
        proof { lemma_cache_len_fold_nonneg(old(perm).value().cpu_caches.view()); }
        let (node_addr, node_perm) = {
            let poll_mut = borrow_mut_global_pool(pptr, Tracked(&mut *perm), Tracked(lctx), lock_perm);
            let (node_addr, Tracked(node_perm)) = poll_mut.linked_list.pop_head();
            (node_addr, Tracked(node_perm))
        };
        proof {
            set_total_free_pages_ghost(perm, (perm.value().total_free_pages.view() - 1) as usize);
            perm.value().global_pool.view().wf_implies_view_len_eq_len();
            old(perm).value().global_pool.view().wf_implies_view_len_eq_len();
        }
        (node_addr, node_perm)
    }
}
}

const ASSERT_PAGE_ALLOCATOR_FITS_4K: [(); 1] = [(); (core::mem::size_of::<PageAllocator<ALLOCATOR_SIZE_4K>>() <= PAGE_SZ_4K) as usize];
