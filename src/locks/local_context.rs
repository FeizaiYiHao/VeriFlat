use vstd::prelude::*;
use crate::*;
use core::sync::atomic::*;
use vstd::std_specs::cmp::*;

verus! {

pub ghost enum LCtxtLockState{
    Acquire,
    Release,
}

/// The lockable pieces nested in one `PageAllocatorUnLockedMap` entry.
/// `PageSize` is deliberately not part of this key: the three allocator maps
/// in `LocalContext` mirror the three allocator maps in `KernelK`.
pub ghost enum AllocatorLockObjId {
    Quota(RwLockPageAllocatorPtr),
    Cache(RwLockPageAllocatorPtr, CpuId),
    GlobalPool(RwLockPageAllocatorPtr),
}

pub tracked struct LCtxtState{
    pub kernel_view_locking_state: LCtxtLockState,
    pub user_view_locking_state: LCtxtLockState,
}

/// Per-thread ledger of held dynamic lock ids.
///
/// Each field is aligned with one lock-bearing field of `KernelK`.  Keeping
/// the maps separate avoids quantifying a single heterogeneous `KernelObjId`
/// map whenever a lock acquisition checks the global ordering.
pub tracked struct LocalContext{
    thread_id: LockThreadId,
    container_lock_map: Map<RwLockContainerPtr, LockId>,
    process_lock_map: Map<RwLockProcessPtr, LockId>,
    thread_lock_map: Map<RwLockThreadPtr, LockId>,
    endpoint_lock_map: Map<RwLockEndpointPtr, LockId>,
    scheduler_lock_map: Map<RwLockSchedulerPtr, LockId>,
    pagetable_lock_map: Map<RwLockPageTableRoot, LockId>,
    page_lock_map: Map<PageIndex, LockId>,
    cpu_lock_map: Map<CpuId, LockId>,
    allocator_4k_lock_map: Map<AllocatorLockObjId, LockId>,
    allocator_2m_lock_map: Map<AllocatorLockObjId, LockId>,
    allocator_1g_lock_map: Map<AllocatorLockObjId, LockId>,
    state: LCtxtState,
}

/// One opaque universal ordering check for one homogeneous ledger map.
/// `LocalContext::lock_id_acyclic` combines an instance for every KernelK
/// lock-bearing field.
#[verifier::opaque]
pub open spec fn lock_map_acyclic<K>(lock_map: Map<K, LockId>, lock_id: LockId) -> bool {
    forall|key: K|
        lock_map.dom().contains(key)
        ==> lock_id.spec_gt(lock_map[key])
}

impl LocalContext{
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }

    pub closed spec fn container_lock_map(&self) -> Map<RwLockContainerPtr, LockId> {
        self.container_lock_map
    }

    pub closed spec fn process_lock_map(&self) -> Map<RwLockProcessPtr, LockId> {
        self.process_lock_map
    }

    pub closed spec fn thread_lock_map(&self) -> Map<RwLockThreadPtr, LockId> {
        self.thread_lock_map
    }

    pub closed spec fn endpoint_lock_map(&self) -> Map<RwLockEndpointPtr, LockId> {
        self.endpoint_lock_map
    }

    pub closed spec fn scheduler_lock_map(&self) -> Map<RwLockSchedulerPtr, LockId> {
        self.scheduler_lock_map
    }

    pub closed spec fn pagetable_lock_map(&self) -> Map<RwLockPageTableRoot, LockId> {
        self.pagetable_lock_map
    }

    pub closed spec fn page_lock_map(&self) -> Map<PageIndex, LockId> {
        self.page_lock_map
    }

    pub closed spec fn cpu_lock_map(&self) -> Map<CpuId, LockId> {
        self.cpu_lock_map
    }

    pub closed spec fn allocator_4k_lock_map(&self) -> Map<AllocatorLockObjId, LockId> {
        self.allocator_4k_lock_map
    }

    pub closed spec fn allocator_2m_lock_map(&self) -> Map<AllocatorLockObjId, LockId> {
        self.allocator_2m_lock_map
    }

    pub closed spec fn allocator_1g_lock_map(&self) -> Map<AllocatorLockObjId, LockId> {
        self.allocator_1g_lock_map
    }

    pub open spec fn allocator_lock_map(&self, page_size: PageSize) -> Map<AllocatorLockObjId, LockId> {
        match page_size {
            PageSize::SZ4k => self.allocator_4k_lock_map(),
            PageSize::SZ2m => self.allocator_2m_lock_map(),
            PageSize::SZ1g => self.allocator_1g_lock_map(),
        }
    }

    pub closed spec fn kernel_view_locking_state(&self) -> LCtxtLockState {
        self.state.kernel_view_locking_state
    }

    pub closed spec fn user_view_locking_state(&self) -> LCtxtLockState {
        self.state.user_view_locking_state
    }

    pub open spec fn wf(&self) -> bool {
        true
    }

    /// Test whether one logical object is registered in its corresponding
    /// homogeneous map.  This is the generic lock primitive's bridge from its
    /// `KernelObjId` argument to the per-KernelK-layout ledgers.
    pub open spec fn lock_map_contains(&self, obj_id: KernelObjId) -> bool {
        match obj_id {
            KernelObjId::Container(c) => self.container_lock_map().dom().contains(c),
            KernelObjId::Process(p) => self.process_lock_map().dom().contains(p),
            KernelObjId::Thread(t) => self.thread_lock_map().dom().contains(t),
            KernelObjId::Endpoint(e) => self.endpoint_lock_map().dom().contains(e),
            KernelObjId::Scheduler(s) => self.scheduler_lock_map().dom().contains(s),
            KernelObjId::PageTable(pt) => self.pagetable_lock_map().dom().contains(pt),
            KernelObjId::Page(i) => self.page_lock_map().dom().contains(i),
            KernelObjId::Cpu(c) => self.cpu_lock_map().dom().contains(c),
            KernelObjId::AllocatorQuota(PageSize::SZ4k, p) =>
                self.allocator_4k_lock_map().dom().contains(AllocatorLockObjId::Quota(p)),
            KernelObjId::AllocatorQuota(PageSize::SZ2m, p) =>
                self.allocator_2m_lock_map().dom().contains(AllocatorLockObjId::Quota(p)),
            KernelObjId::AllocatorQuota(PageSize::SZ1g, p) =>
                self.allocator_1g_lock_map().dom().contains(AllocatorLockObjId::Quota(p)),
            KernelObjId::AllocatorCache(PageSize::SZ4k, p, c) =>
                self.allocator_4k_lock_map().dom().contains(AllocatorLockObjId::Cache(p, c)),
            KernelObjId::AllocatorCache(PageSize::SZ2m, p, c) =>
                self.allocator_2m_lock_map().dom().contains(AllocatorLockObjId::Cache(p, c)),
            KernelObjId::AllocatorCache(PageSize::SZ1g, p, c) =>
                self.allocator_1g_lock_map().dom().contains(AllocatorLockObjId::Cache(p, c)),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, p) =>
                self.allocator_4k_lock_map().dom().contains(AllocatorLockObjId::GlobalPool(p)),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, p) =>
                self.allocator_2m_lock_map().dom().contains(AllocatorLockObjId::GlobalPool(p)),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, p) =>
                self.allocator_1g_lock_map().dom().contains(AllocatorLockObjId::GlobalPool(p)),
        }
    }

    pub open spec fn lock_id_for_obj(&self, obj_id: KernelObjId) -> LockId
        recommends self.lock_map_contains(obj_id)
    {
        match obj_id {
            KernelObjId::Container(c) => self.container_lock_map()[c],
            KernelObjId::Process(p) => self.process_lock_map()[p],
            KernelObjId::Thread(t) => self.thread_lock_map()[t],
            KernelObjId::Endpoint(e) => self.endpoint_lock_map()[e],
            KernelObjId::Scheduler(s) => self.scheduler_lock_map()[s],
            KernelObjId::PageTable(pt) => self.pagetable_lock_map()[pt],
            KernelObjId::Page(i) => self.page_lock_map()[i],
            KernelObjId::Cpu(c) => self.cpu_lock_map()[c],
            KernelObjId::AllocatorQuota(PageSize::SZ4k, p) =>
                self.allocator_4k_lock_map()[AllocatorLockObjId::Quota(p)],
            KernelObjId::AllocatorQuota(PageSize::SZ2m, p) =>
                self.allocator_2m_lock_map()[AllocatorLockObjId::Quota(p)],
            KernelObjId::AllocatorQuota(PageSize::SZ1g, p) =>
                self.allocator_1g_lock_map()[AllocatorLockObjId::Quota(p)],
            KernelObjId::AllocatorCache(PageSize::SZ4k, p, c) =>
                self.allocator_4k_lock_map()[AllocatorLockObjId::Cache(p, c)],
            KernelObjId::AllocatorCache(PageSize::SZ2m, p, c) =>
                self.allocator_2m_lock_map()[AllocatorLockObjId::Cache(p, c)],
            KernelObjId::AllocatorCache(PageSize::SZ1g, p, c) =>
                self.allocator_1g_lock_map()[AllocatorLockObjId::Cache(p, c)],
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, p) =>
                self.allocator_4k_lock_map()[AllocatorLockObjId::GlobalPool(p)],
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, p) =>
                self.allocator_2m_lock_map()[AllocatorLockObjId::GlobalPool(p)],
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, p) =>
                self.allocator_1g_lock_map()[AllocatorLockObjId::GlobalPool(p)],
        }
    }

    pub open spec fn lock_maps_equal(&self, other: &Self) -> bool {
        &&& self.container_lock_map() =~= other.container_lock_map()
        &&& self.process_lock_map() =~= other.process_lock_map()
        &&& self.thread_lock_map() =~= other.thread_lock_map()
        &&& self.endpoint_lock_map() =~= other.endpoint_lock_map()
        &&& self.scheduler_lock_map() =~= other.scheduler_lock_map()
        &&& self.pagetable_lock_map() =~= other.pagetable_lock_map()
        &&& self.page_lock_map() =~= other.page_lock_map()
        &&& self.cpu_lock_map() =~= other.cpu_lock_map()
        &&& self.allocator_4k_lock_map() =~= other.allocator_4k_lock_map()
        &&& self.allocator_2m_lock_map() =~= other.allocator_2m_lock_map()
        &&& self.allocator_1g_lock_map() =~= other.allocator_1g_lock_map()
    }

    pub open spec fn all_lock_maps_empty(&self) -> bool {
        &&& self.container_lock_map() == Map::<RwLockContainerPtr, LockId>::empty()
        &&& self.process_lock_map() == Map::<RwLockProcessPtr, LockId>::empty()
        &&& self.thread_lock_map() == Map::<RwLockThreadPtr, LockId>::empty()
        &&& self.endpoint_lock_map() == Map::<RwLockEndpointPtr, LockId>::empty()
        &&& self.scheduler_lock_map() == Map::<RwLockSchedulerPtr, LockId>::empty()
        &&& self.pagetable_lock_map() == Map::<RwLockPageTableRoot, LockId>::empty()
        &&& self.page_lock_map() == Map::<PageIndex, LockId>::empty()
        &&& self.cpu_lock_map() == Map::<CpuId, LockId>::empty()
        &&& self.allocator_4k_lock_map() == Map::<AllocatorLockObjId, LockId>::empty()
        &&& self.allocator_2m_lock_map() == Map::<AllocatorLockObjId, LockId>::empty()
        &&& self.allocator_1g_lock_map() == Map::<AllocatorLockObjId, LockId>::empty()
    }

    /// A short-lived operation-level description of which logical locks are
    /// held.  Unlike the old stored heterogeneous map, this is derived from
    /// the per-type maps and is used only by wrapper contracts that enumerate
    /// a small fixed lock set.
    pub open spec fn lock_obj_ids_eq(&self, obj_ids: Set<KernelObjId>) -> bool {
        forall|obj_id: KernelObjId|
            self.lock_map_contains(obj_id) == obj_ids.contains(obj_id)
    }

    pub open spec fn lock_maps_inserted(
        &self,
        old: &Self,
        obj_id: KernelObjId,
        lock_id: LockId,
    ) -> bool {
        match obj_id {
            KernelObjId::Container(c) =>
                self.container_lock_map() =~= old.container_lock_map().insert(c, lock_id)
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map()
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Process(p) =>
                self.process_lock_map() =~= old.process_lock_map().insert(p, lock_id)
                && self.container_lock_map() =~= old.container_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map()
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Thread(t) =>
                self.thread_lock_map() =~= old.thread_lock_map().insert(t, lock_id)
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map()
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Endpoint(e) =>
                self.endpoint_lock_map() =~= old.endpoint_lock_map().insert(e, lock_id)
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map()
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Scheduler(s) =>
                self.scheduler_lock_map() =~= old.scheduler_lock_map().insert(s, lock_id)
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map()
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::PageTable(pt) =>
                self.pagetable_lock_map() =~= old.pagetable_lock_map().insert(pt, lock_id)
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map()
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Page(i) =>
                self.page_lock_map() =~= old.page_lock_map().insert(i, lock_id)
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map()
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Cpu(c) =>
                self.cpu_lock_map() =~= old.cpu_lock_map().insert(c, lock_id)
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::AllocatorQuota(PageSize::SZ4k, p) =>
                self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map().insert(AllocatorLockObjId::Quota(p), lock_id)
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorQuota(PageSize::SZ2m, p) =>
                self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map().insert(AllocatorLockObjId::Quota(p), lock_id)
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorQuota(PageSize::SZ1g, p) =>
                self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map().insert(AllocatorLockObjId::Quota(p), lock_id)
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorCache(PageSize::SZ4k, p, c) =>
                self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map().insert(AllocatorLockObjId::Cache(p, c), lock_id)
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorCache(PageSize::SZ2m, p, c) =>
                self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map().insert(AllocatorLockObjId::Cache(p, c), lock_id)
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorCache(PageSize::SZ1g, p, c) =>
                self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map().insert(AllocatorLockObjId::Cache(p, c), lock_id)
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, p) =>
                self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map().insert(AllocatorLockObjId::GlobalPool(p), lock_id)
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, p) =>
                self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map().insert(AllocatorLockObjId::GlobalPool(p), lock_id)
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, p) =>
                self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map().insert(AllocatorLockObjId::GlobalPool(p), lock_id)
                && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map()
                && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map()
                && self.container_lock_map() =~= old.container_lock_map()
                && self.process_lock_map() =~= old.process_lock_map()
                && self.thread_lock_map() =~= old.thread_lock_map()
                && self.endpoint_lock_map() =~= old.endpoint_lock_map()
                && self.scheduler_lock_map() =~= old.scheduler_lock_map()
                && self.pagetable_lock_map() =~= old.pagetable_lock_map()
                && self.page_lock_map() =~= old.page_lock_map()
                && self.cpu_lock_map() =~= old.cpu_lock_map(),
        }
    }

    pub open spec fn lock_maps_removed(
        &self,
        old: &Self,
        obj_id: KernelObjId,
    ) -> bool {
        match obj_id {
            KernelObjId::Container(c) => self.container_lock_map() =~= old.container_lock_map().remove(c) && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map() && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Process(p) => self.process_lock_map() =~= old.process_lock_map().remove(p) && self.container_lock_map() =~= old.container_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map() && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Thread(t) => self.thread_lock_map() =~= old.thread_lock_map().remove(t) && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map() && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Endpoint(e) => self.endpoint_lock_map() =~= old.endpoint_lock_map().remove(e) && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map() && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Scheduler(s) => self.scheduler_lock_map() =~= old.scheduler_lock_map().remove(s) && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map() && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::PageTable(pt) => self.pagetable_lock_map() =~= old.pagetable_lock_map().remove(pt) && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map() && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Page(i) => self.page_lock_map() =~= old.page_lock_map().remove(i) && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map() && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::Cpu(c) => self.cpu_lock_map() =~= old.cpu_lock_map().remove(c) && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map(),
            KernelObjId::AllocatorQuota(PageSize::SZ4k, p) => self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map().remove(AllocatorLockObjId::Quota(p)) && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorQuota(PageSize::SZ2m, p) => self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map().remove(AllocatorLockObjId::Quota(p)) && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorQuota(PageSize::SZ1g, p) => self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map().remove(AllocatorLockObjId::Quota(p)) && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorCache(PageSize::SZ4k, p, c) => self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map().remove(AllocatorLockObjId::Cache(p, c)) && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorCache(PageSize::SZ2m, p, c) => self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map().remove(AllocatorLockObjId::Cache(p, c)) && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorCache(PageSize::SZ1g, p, c) => self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map().remove(AllocatorLockObjId::Cache(p, c)) && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, p) => self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map().remove(AllocatorLockObjId::GlobalPool(p)) && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, p) => self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map().remove(AllocatorLockObjId::GlobalPool(p)) && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, p) => self.allocator_1g_lock_map() =~= old.allocator_1g_lock_map().remove(AllocatorLockObjId::GlobalPool(p)) && self.allocator_4k_lock_map() =~= old.allocator_4k_lock_map() && self.allocator_2m_lock_map() =~= old.allocator_2m_lock_map() && self.container_lock_map() =~= old.container_lock_map() && self.process_lock_map() =~= old.process_lock_map() && self.thread_lock_map() =~= old.thread_lock_map() && self.endpoint_lock_map() =~= old.endpoint_lock_map() && self.scheduler_lock_map() =~= old.scheduler_lock_map() && self.pagetable_lock_map() =~= old.pagetable_lock_map() && self.page_lock_map() =~= old.page_lock_map() && self.cpu_lock_map() =~= old.cpu_lock_map(),
        }
    }

    /// Predicate: `lock_id` is strictly greater than every id held in every
    /// per-KernelK-layout map.  This remains a global ordering relation while
    /// avoiding a heterogeneous quantified key space.
    pub open spec fn lock_id_acyclic(&self, lock_id: LockId) -> bool {
        &&& lock_map_acyclic(self.container_lock_map(), lock_id)
        &&& lock_map_acyclic(self.process_lock_map(), lock_id)
        &&& lock_map_acyclic(self.thread_lock_map(), lock_id)
        &&& lock_map_acyclic(self.endpoint_lock_map(), lock_id)
        &&& lock_map_acyclic(self.scheduler_lock_map(), lock_id)
        &&& lock_map_acyclic(self.pagetable_lock_map(), lock_id)
        &&& lock_map_acyclic(self.page_lock_map(), lock_id)
        &&& lock_map_acyclic(self.cpu_lock_map(), lock_id)
        &&& lock_map_acyclic(self.allocator_4k_lock_map(), lock_id)
        &&& lock_map_acyclic(self.allocator_2m_lock_map(), lock_id)
        &&& lock_map_acyclic(self.allocator_1g_lock_map(), lock_id)
    }

    pub open spec fn obj_id_fresh(&self, obj_id: KernelObjId) -> bool {
        !self.lock_map_contains(obj_id)
    }

    /// Establish the first acquisition's ordering obligation from the empty
    /// per-type ledger state minted at syscall entry.
    pub proof fn lemma_all_lock_maps_empty_imply_lock_id_acyclic(&self)
        requires
            self.all_lock_maps_empty(),
        ensures
            forall|lock_id: LockId| self.lock_id_acyclic(lock_id),
    {
        reveal(LocalContext::all_lock_maps_empty);
        reveal(LocalContext::lock_id_acyclic);
        reveal(lock_map_acyclic);
    }

    /// A single lock acquisition preserves every prospective acyclic ordering
    /// when the prospective id also tops the just-inserted id.  The proof
    /// dispatches through the per-type ledger selected by `obj_id`; callers
    /// therefore never need to reconstruct a heterogeneous map.
    pub proof fn lemma_lock_id_acyclic_after_insert(
        &self,
        old: &Self,
        obj_id: KernelObjId,
        inserted_lock_id: LockId,
        prospective_lock_id: LockId,
    )
        requires
            old.lock_id_acyclic(prospective_lock_id),
            prospective_lock_id.spec_gt(inserted_lock_id),
            self.lock_maps_inserted(old, obj_id, inserted_lock_id),
        ensures
            self.lock_id_acyclic(prospective_lock_id),
    {
        reveal(LocalContext::lock_id_acyclic);
        reveal(LocalContext::lock_maps_inserted);
        reveal(lock_map_acyclic);
    }

    /// Common syscall lock prefixes are stated once over the concrete typed
    /// ledgers.  They expose a small derived object set to legacy operation
    /// proofs without reintroducing a stored heterogeneous map.
    pub proof fn lemma_cpu_scheduler_locks_from_empty(
        &self,
        initial: &Self,
        after_cpu: &Self,
        cpu_id: CpuId,
        scheduler_ptr: RwLockSchedulerPtr,
        cpu_lock_id: LockId,
        scheduler_lock_id: LockId,
    )
        requires
            initial.all_lock_maps_empty(),
            after_cpu.lock_maps_inserted(initial, KernelObjId::Cpu(cpu_id), cpu_lock_id),
            self.lock_maps_inserted(after_cpu, KernelObjId::Scheduler(scheduler_ptr), scheduler_lock_id),
        ensures
            self.lock_obj_ids_eq(set![
                KernelObjId::Cpu(cpu_id),
                KernelObjId::Scheduler(scheduler_ptr),
            ]),
    {
        reveal(LocalContext::all_lock_maps_empty);
        reveal(LocalContext::lock_maps_inserted);
        reveal(LocalContext::lock_obj_ids_eq);
    }

    pub proof fn lemma_cpu_scheduler_process_locks_from_empty(
        &self,
        initial: &Self,
        after_cpu: &Self,
        after_scheduler: &Self,
        cpu_id: CpuId,
        scheduler_ptr: RwLockSchedulerPtr,
        process_ptr: RwLockProcessPtr,
        cpu_lock_id: LockId,
        scheduler_lock_id: LockId,
        process_lock_id: LockId,
    )
        requires
            initial.all_lock_maps_empty(),
            after_cpu.lock_maps_inserted(initial, KernelObjId::Cpu(cpu_id), cpu_lock_id),
            after_scheduler.lock_maps_inserted(after_cpu, KernelObjId::Scheduler(scheduler_ptr), scheduler_lock_id),
            self.lock_maps_inserted(after_scheduler, KernelObjId::Process(process_ptr), process_lock_id),
        ensures
            self.lock_obj_ids_eq(set![
                KernelObjId::Cpu(cpu_id),
                KernelObjId::Scheduler(scheduler_ptr),
                KernelObjId::Process(process_ptr),
            ]),
    {
        reveal(LocalContext::all_lock_maps_empty);
        reveal(LocalContext::lock_maps_inserted);
        reveal(LocalContext::lock_obj_ids_eq);
    }

    /// Allocator scans acquire and release a homogeneous family of cache
    /// locks.  Keep their transient operation view local to that family; the
    /// concrete update remains the 4k allocator ledger only.
    pub proof fn lemma_allocator_4k_cache_inserted_view(
        &self,
        old: &Self,
        allocator_ptr: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        lock_id: LockId,
    )
        requires
            self.lock_maps_inserted(
                old,
                KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id),
                lock_id),
            !old.lock_map_contains(
                KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id)),
        ensures
            forall|obj: KernelObjId|
                self.lock_map_contains(obj)
                <==> old.lock_map_contains(obj)
                    || obj == KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id),
            forall|obj: KernelObjId|
                old.lock_map_contains(obj)
                ==> self.lock_map_contains(obj)
                    && self.lock_id_for_obj(obj) == old.lock_id_for_obj(obj),
    {
        reveal(LocalContext::lock_maps_inserted);
    }

    pub proof fn lemma_allocator_4k_global_pool_inserted_view(
        &self,
        old: &Self,
        allocator_ptr: RwLockPageAllocatorPtr,
        lock_id: LockId,
    )
        requires
            self.lock_maps_inserted(
                old,
                KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, allocator_ptr),
                lock_id),
            !old.lock_map_contains(
                KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, allocator_ptr)),
        ensures
            forall|obj: KernelObjId|
                self.lock_map_contains(obj)
                <==> old.lock_map_contains(obj)
                    || obj == KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, allocator_ptr),
            forall|obj: KernelObjId|
                old.lock_map_contains(obj)
                ==> self.lock_map_contains(obj)
                    && self.lock_id_for_obj(obj) == old.lock_id_for_obj(obj),
    {
        reveal(LocalContext::lock_maps_inserted);
    }

    pub proof fn lemma_allocator_4k_cache_removed_view(
        &self,
        old: &Self,
        allocator_ptr: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
    )
        requires
            self.lock_maps_removed(
                old,
                KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id)),
        ensures
            forall|obj: KernelObjId|
                self.lock_map_contains(obj)
                <==> old.lock_map_contains(obj)
                    && obj != KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id),
            forall|obj: KernelObjId|
                self.lock_map_contains(obj)
                ==> old.lock_id_for_obj(obj) == self.lock_id_for_obj(obj),
    {
        reveal(LocalContext::lock_maps_removed);
    }

    pub proof fn lemma_allocator_4k_cache_remove_restores(
        &self,
        old: &Self,
        after_insert: &Self,
        allocator_ptr: RwLockPageAllocatorPtr,
        cpu_id: CpuId,
        lock_id: LockId,
    )
        requires
            after_insert.lock_maps_inserted(
                old,
                KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id),
                lock_id),
            !old.lock_map_contains(
                KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id)),
            self.lock_maps_removed(
                after_insert,
                KernelObjId::AllocatorCache(PageSize::SZ4k, allocator_ptr, cpu_id)),
        ensures
            self.lock_maps_equal(old),
    {
        reveal(LocalContext::lock_maps_inserted);
        reveal(LocalContext::lock_maps_removed);
        reveal(LocalContext::lock_maps_equal);
        assert(old.allocator_4k_lock_map().insert(
            AllocatorLockObjId::Cache(allocator_ptr, cpu_id), lock_id).remove(
            AllocatorLockObjId::Cache(allocator_ptr, cpu_id))
            =~= old.allocator_4k_lock_map());
    }

    pub proof fn lemma_allocator_4k_global_pool_remove_restores(
        &self,
        old: &Self,
        after_insert: &Self,
        allocator_ptr: RwLockPageAllocatorPtr,
        lock_id: LockId,
    )
        requires
            after_insert.lock_maps_inserted(
                old,
                KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, allocator_ptr),
                lock_id),
            !old.lock_map_contains(
                KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, allocator_ptr)),
            self.lock_maps_removed(
                after_insert,
                KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, allocator_ptr)),
        ensures
            self.lock_maps_equal(old),
    {
        reveal(LocalContext::lock_maps_inserted);
        reveal(LocalContext::lock_maps_removed);
        reveal(LocalContext::lock_maps_equal);
        assert(old.allocator_4k_lock_map().insert(
            AllocatorLockObjId::GlobalPool(allocator_ptr), lock_id).remove(
            AllocatorLockObjId::GlobalPool(allocator_ptr))
            =~= old.allocator_4k_lock_map());
    }

    /// Reassemble the per-map acyclicity conjuncts from an operation-local
    /// bound over the logical object ids.  This is the bridge used by lock
    /// acquisition proofs that reason about a heterogeneous operation lock
    /// set, while the stored ledger and the solver-facing acyclicity predicate
    /// remain split by KernelK layout.
    pub proof fn lemma_lock_id_acyclic_from_obj_id_bound(&self, lock_id: LockId)
        requires
            forall|obj_id: KernelObjId|
                self.lock_map_contains(obj_id)
                ==> lock_id.spec_gt(self.lock_id_for_obj(obj_id)),
        ensures
            self.lock_id_acyclic(lock_id),
    {
        reveal(LocalContext::lock_id_acyclic);
        reveal(lock_map_acyclic);

        assert forall|c: RwLockContainerPtr|
            self.container_lock_map().dom().contains(c)
            implies lock_id.spec_gt(self.container_lock_map()[c]) by {
            assert(self.lock_map_contains(KernelObjId::Container(c)));
            assert(self.lock_id_for_obj(KernelObjId::Container(c)) == self.container_lock_map()[c]);
        };
        assert forall|p: RwLockProcessPtr|
            self.process_lock_map().dom().contains(p)
            implies lock_id.spec_gt(self.process_lock_map()[p]) by {
            assert(self.lock_map_contains(KernelObjId::Process(p)));
            assert(self.lock_id_for_obj(KernelObjId::Process(p)) == self.process_lock_map()[p]);
        };
        assert forall|t: RwLockThreadPtr|
            self.thread_lock_map().dom().contains(t)
            implies lock_id.spec_gt(self.thread_lock_map()[t]) by {
            assert(self.lock_map_contains(KernelObjId::Thread(t)));
            assert(self.lock_id_for_obj(KernelObjId::Thread(t)) == self.thread_lock_map()[t]);
        };
        assert forall|e: RwLockEndpointPtr|
            self.endpoint_lock_map().dom().contains(e)
            implies lock_id.spec_gt(self.endpoint_lock_map()[e]) by {
            assert(self.lock_map_contains(KernelObjId::Endpoint(e)));
            assert(self.lock_id_for_obj(KernelObjId::Endpoint(e)) == self.endpoint_lock_map()[e]);
        };
        assert forall|s: RwLockSchedulerPtr|
            self.scheduler_lock_map().dom().contains(s)
            implies lock_id.spec_gt(self.scheduler_lock_map()[s]) by {
            assert(self.lock_map_contains(KernelObjId::Scheduler(s)));
            assert(self.lock_id_for_obj(KernelObjId::Scheduler(s)) == self.scheduler_lock_map()[s]);
        };
        assert forall|pt: RwLockPageTableRoot|
            self.pagetable_lock_map().dom().contains(pt)
            implies lock_id.spec_gt(self.pagetable_lock_map()[pt]) by {
            assert(self.lock_map_contains(KernelObjId::PageTable(pt)));
            assert(self.lock_id_for_obj(KernelObjId::PageTable(pt)) == self.pagetable_lock_map()[pt]);
        };
        assert forall|i: PageIndex|
            self.page_lock_map().dom().contains(i)
            implies lock_id.spec_gt(self.page_lock_map()[i]) by {
            assert(self.lock_map_contains(KernelObjId::Page(i)));
            assert(self.lock_id_for_obj(KernelObjId::Page(i)) == self.page_lock_map()[i]);
        };
        assert forall|c: CpuId|
            self.cpu_lock_map().dom().contains(c)
            implies lock_id.spec_gt(self.cpu_lock_map()[c]) by {
            assert(self.lock_map_contains(KernelObjId::Cpu(c)));
            assert(self.lock_id_for_obj(KernelObjId::Cpu(c)) == self.cpu_lock_map()[c]);
        };
        assert forall|obj: AllocatorLockObjId|
            self.allocator_4k_lock_map().dom().contains(obj)
            implies lock_id.spec_gt(self.allocator_4k_lock_map()[obj]) by {
            match obj {
                AllocatorLockObjId::Quota(p) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorQuota(PageSize::SZ4k, p)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorQuota(PageSize::SZ4k, p)) == self.allocator_4k_lock_map()[obj]);
                }
                AllocatorLockObjId::Cache(p, c) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorCache(PageSize::SZ4k, p, c)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorCache(PageSize::SZ4k, p, c)) == self.allocator_4k_lock_map()[obj]);
                }
                AllocatorLockObjId::GlobalPool(p) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, p)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, p)) == self.allocator_4k_lock_map()[obj]);
                }
            }
        };
        assert forall|obj: AllocatorLockObjId|
            self.allocator_2m_lock_map().dom().contains(obj)
            implies lock_id.spec_gt(self.allocator_2m_lock_map()[obj]) by {
            match obj {
                AllocatorLockObjId::Quota(p) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorQuota(PageSize::SZ2m, p)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorQuota(PageSize::SZ2m, p)) == self.allocator_2m_lock_map()[obj]);
                }
                AllocatorLockObjId::Cache(p, c) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorCache(PageSize::SZ2m, p, c)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorCache(PageSize::SZ2m, p, c)) == self.allocator_2m_lock_map()[obj]);
                }
                AllocatorLockObjId::GlobalPool(p) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, p)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, p)) == self.allocator_2m_lock_map()[obj]);
                }
            }
        };
        assert forall|obj: AllocatorLockObjId|
            self.allocator_1g_lock_map().dom().contains(obj)
            implies lock_id.spec_gt(self.allocator_1g_lock_map()[obj]) by {
            match obj {
                AllocatorLockObjId::Quota(p) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorQuota(PageSize::SZ1g, p)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorQuota(PageSize::SZ1g, p)) == self.allocator_1g_lock_map()[obj]);
                }
                AllocatorLockObjId::Cache(p, c) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorCache(PageSize::SZ1g, p, c)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorCache(PageSize::SZ1g, p, c)) == self.allocator_1g_lock_map()[obj]);
                }
                AllocatorLockObjId::GlobalPool(p) => {
                    assert(self.lock_map_contains(KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, p)));
                    assert(self.lock_id_for_obj(KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, p)) == self.allocator_1g_lock_map()[obj]);
                }
            }
        };
    }

    pub proof fn lemma_lock_id_eq_imply_acyclic_eq(&self)
        ensures
            forall|lock_id1: LockId, lock_id2: LockId|
                #![trigger self.lock_id_acyclic(lock_id1), self.lock_id_acyclic(lock_id2)]
                {
                    &&& lock_id1.container == lock_id2.container
                    &&& lock_id1.process == lock_id2.process
                    &&& lock_id1.major == lock_id2.major
                    &&& lock_id1.minor == lock_id2.minor
                }
                ==>
                self.lock_id_acyclic(lock_id1) == self.lock_id_acyclic(lock_id2)
    {
    }

    /// TCB: update one held dynamic lock id during Release.  The selected map
    /// is determined by the same `KernelObjId` dispatch as the lock primitive.
    #[verifier::external_body]
    pub proof fn update_lock_id(
        tracked &mut self,
        obj_id: KernelObjId,
        new_lock_id: LockId,
    )
        requires
            old(self).kernel_view_locking_state() is Release,
            old(self).lock_map_contains(obj_id),
        ensures
            final(self).lock_maps_inserted(old(self), obj_id, new_lock_id),
            final(self).thread_id() == old(self).thread_id(),
            final(self).kernel_view_locking_state() == old(self).kernel_view_locking_state(),
            final(self).user_view_locking_state() == old(self).user_view_locking_state(),
    {
        unimplemented!()
    }
}

pub open spec fn lock_ensures<T:LockUserVisibilityTrait>(old:&LocalContext, new:&LocalContext, value:T, lock_id: LockId, obj_id: KernelObjId) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& new.kernel_view_locking_state() is Acquire
    &&& new.user_view_locking_state() == old.user_view_locking_state()
    &&& new.lock_maps_inserted(old, obj_id, lock_id)
}

/// Precondition for releasing any lock guarded by `T`.
pub open spec fn unlock_requires<T:LockUserVisibilityTrait>(old:&LocalContext) -> bool {
    T::is_user_visible() ==> old.user_view_locking_state() is Release
}

pub open spec fn unlock_ensures<T:LockUserVisibilityTrait>(old:&LocalContext, new:&LocalContext, value:T, lock_token: LockToken, obj_id: KernelObjId) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& old.kernel_view_locking_state() is Acquire ==> new.kernel_view_locking_state() is Release
    &&& old.kernel_view_locking_state() is Release ==> new.kernel_view_locking_state() is Release
    &&& new.user_view_locking_state() == old.user_view_locking_state()
    &&& new.lock_maps_removed(old, obj_id)
}

}
