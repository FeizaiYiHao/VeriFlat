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
    lock_id_set: Set<LockId>,
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

impl LocalContext{
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }

    pub closed spec fn lock_id_set(&self) -> Set<LockId> {
        self.lock_id_set
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

    #[verifier::opaque]
    pub open spec fn wf(&self) -> bool {
        &&& forall|lock_id: LockId|
            #![trigger self.lock_id_set().contains(lock_id)]
            self.lock_id_set().contains(lock_id)
            ==
            {
                |||
                self.cpu_lock_map().values().contains(lock_id)
                |||
                self.page_lock_map().values().contains(lock_id)
                |||
                self.container_lock_map().values().contains(lock_id)
                |||
                self.process_lock_map().values().contains(lock_id)
                |||
                self.thread_lock_map().values().contains(lock_id)
                |||
                self.endpoint_lock_map().values().contains(lock_id)
                |||
                self.scheduler_lock_map().values().contains(lock_id)
                |||
                self.pagetable_lock_map().values().contains(lock_id)
                |||
                self.allocator_4k_lock_map().values().contains(lock_id)
                |||
                self.allocator_2m_lock_map().values().contains(lock_id)
                |||
                self.allocator_1g_lock_map().values().contains(lock_id)
            }
        &&& forall|cpu_id: CpuId|
            #![trigger self.cpu_lock_map().dom().contains(cpu_id)]
            self.cpu_lock_map().dom().contains(cpu_id)
            ==> self.lock_id_set().contains(self.cpu_lock_map()[cpu_id])
        &&& forall|page_index: PageIndex|
            #![trigger self.page_lock_map().dom().contains(page_index)]
            self.page_lock_map().dom().contains(page_index)
            ==> self.lock_id_set().contains(self.page_lock_map()[page_index])
        &&& forall|container_ptr: RwLockContainerPtr|
            #![trigger self.container_lock_map().dom().contains(container_ptr)]
            self.container_lock_map().dom().contains(container_ptr)
            ==> self.lock_id_set().contains(self.container_lock_map()[container_ptr])
        &&& forall|process_ptr: RwLockProcessPtr|
            #![trigger self.process_lock_map().dom().contains(process_ptr)]
            self.process_lock_map().dom().contains(process_ptr)
            ==> self.lock_id_set().contains(self.process_lock_map()[process_ptr])
        &&& forall|thread_ptr: RwLockThreadPtr|
            #![trigger self.thread_lock_map().dom().contains(thread_ptr)]
            self.thread_lock_map().dom().contains(thread_ptr)
            ==> self.lock_id_set().contains(self.thread_lock_map()[thread_ptr])
        &&& forall|endpoint_ptr: RwLockEndpointPtr|
            #![trigger self.endpoint_lock_map().dom().contains(endpoint_ptr)]
            self.endpoint_lock_map().dom().contains(endpoint_ptr)
            ==> self.lock_id_set().contains(self.endpoint_lock_map()[endpoint_ptr])
        &&& forall|scheduler_ptr: RwLockSchedulerPtr|
            #![trigger self.scheduler_lock_map().dom().contains(scheduler_ptr)]
            self.scheduler_lock_map().dom().contains(scheduler_ptr)
            ==> self.lock_id_set().contains(self.scheduler_lock_map()[scheduler_ptr])
        &&& forall|pagetable_ptr: RwLockPageTableRoot|
            #![trigger self.pagetable_lock_map().dom().contains(pagetable_ptr)]
            self.pagetable_lock_map().dom().contains(pagetable_ptr)
            ==> self.lock_id_set().contains(self.pagetable_lock_map()[pagetable_ptr])
        &&& forall|obj_id: AllocatorLockObjId|
            #![trigger self.allocator_4k_lock_map().dom().contains(obj_id)]
            self.allocator_4k_lock_map().dom().contains(obj_id)
            ==> self.lock_id_set().contains(self.allocator_4k_lock_map()[obj_id])
        &&& forall|obj_id: AllocatorLockObjId|
            #![trigger self.allocator_2m_lock_map().dom().contains(obj_id)]
            self.allocator_2m_lock_map().dom().contains(obj_id)
            ==> self.lock_id_set().contains(self.allocator_2m_lock_map()[obj_id])
        &&& forall|obj_id: AllocatorLockObjId|
            #![trigger self.allocator_1g_lock_map().dom().contains(obj_id)]
            self.allocator_1g_lock_map().dom().contains(obj_id)
            ==> self.lock_id_set().contains(self.allocator_1g_lock_map()[obj_id])
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
        &&& self.wf() == other.wf()
        &&& self.lock_id_set() =~= other.lock_id_set()
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

    pub open spec fn lock_maps_inserted(
        &self,
        old: &Self,
        obj_id: KernelObjId,
        lock_id: LockId,
    ) -> bool {
        &&& self.lock_id_set() =~= if old.lock_map_contains(obj_id) {
            old.lock_id_set().remove(old.lock_id_for_obj(obj_id)).insert(lock_id)
        } else {
            old.lock_id_set().insert(lock_id)
        }
        &&& match obj_id {
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
        &&& self.lock_id_set() =~=
            old.lock_id_set().remove(old.lock_id_for_obj(obj_id))
        &&& match obj_id {
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

    /// Predicate: `lock_id` is strictly greater than every currently held id.
    /// `wf()` ties this compact set to the per-KernelK-layout typed maps.
    pub open spec fn lock_id_acyclic(&self, lock_id: LockId) -> bool {
        forall|held_lock_id: LockId|
            #![trigger self.lock_id_set().contains(held_lock_id)]
            self.lock_id_set().contains(held_lock_id)
            ==> lock_id.spec_gt(held_lock_id)
    }

    pub open spec fn obj_id_fresh(&self, obj_id: KernelObjId) -> bool {
        !self.lock_map_contains(obj_id)
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

    /// TCB: explicitly close the acquire phase without releasing a lock.
    /// This is used when a payload mutation changes a held object's dynamic
    /// ordering id: enter Release first, then update that id before the first
    /// physical unlock.
    #[verifier::external_body]
    pub proof fn enter_kernel_view_release(tracked &mut self)
        requires
            old(self).kernel_view_locking_state() is Acquire,
        ensures
            final(self).thread_id() == old(self).thread_id(),
            final(self).kernel_view_locking_state() is Release,
            final(self).user_view_locking_state() == old(self).user_view_locking_state(),
            final(self).lock_maps_equal(old(self)),
            final(self).wf(),
    {
        unimplemented!()
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
            final(self).wf(),
    {
        unimplemented!()
    }
}

pub open spec fn lock_ensures<T:LockUserVisibilityTrait>(old:&LocalContext, new:&LocalContext, value:T, lock_id: LockId, obj_id: KernelObjId) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& new.kernel_view_locking_state() is Acquire
    &&& new.user_view_locking_state() == old.user_view_locking_state()
    &&& new.lock_maps_inserted(old, obj_id, lock_id)
    &&& new.lock_id_set() == old.lock_id_set().insert(lock_id)
    &&& new.wf()
}

/// Precondition for releasing any lock guarded by `T`.
pub open spec fn unlock_requires<T:LockUserVisibilityTrait>(old:&LocalContext) -> bool {
    T::is_user_visible() ==> old.user_view_locking_state() is Release
}

pub open spec fn unlock_ensures<T:LockUserVisibilityTrait>(
    old: &LocalContext,
    new: &LocalContext,
    value: T,
    lock_token: LockToken,
    obj_id: KernelObjId,
    lock_id: LockId,
) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& old.kernel_view_locking_state() is Acquire ==> new.kernel_view_locking_state() is Release
    &&& old.kernel_view_locking_state() is Release ==> new.kernel_view_locking_state() is Release
    &&& new.user_view_locking_state() == old.user_view_locking_state()
    &&& new.lock_maps_removed(old, obj_id)
    &&& new.lock_id_set() == old.lock_id_set().remove(lock_id)
    &&& new.wf()
}

}
