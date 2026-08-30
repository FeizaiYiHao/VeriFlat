use vstd::prelude::*;
use crate::*;

verus! {

pub ghost enum LCtxtLockState {
    Acquire,
    Release,
}

pub tracked struct LCtxtState {
    pub kernel_view_locking_state: LCtxtLockState,
}

pub ghost enum TypedLockMode {
    Read,
    Write,
}

/// The complete forward lock record stored under a typed object key.
pub ghost struct TypedHeldLock {
    pub lock_id: LockId,
    pub mode: TypedLockMode,
}

pub ghost struct AllocatorLockMaps {
    pub quota: Map<RwLockPageAllocatorPtr, TypedHeldLock>,
    pub cache: Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock>,
    pub global_pool: Map<RwLockPageAllocatorPtr, TypedHeldLock>,
}

pub open spec fn typed_lock_map_contains_mode<K>(
    map: Map<K, TypedHeldLock>,
    key: K,
    mode: TypedLockMode,
) -> bool {
    map.dom().contains(key) && map.index(key).mode == mode
}

pub open spec fn typed_lock_map_ids_acyclic<K>(
    map: Map<K, TypedHeldLock>,
    lock_id: LockId,
) -> bool {
    forall|key: K|
        #![trigger map.dom().contains(key)]
        map.dom().contains(key) ==> lock_id.spec_gt(map.index(key).lock_id)
}

pub open spec fn typed_lock_map_majors_lt<K>(
    map: Map<K, TypedHeldLock>,
    major: LockMajorId,
) -> bool {
    forall|key: K|
        #![trigger map.dom().contains(key)]
        map.dom().contains(key) ==> map.index(key).lock_id.major < major
}

pub open spec fn typed_lock_map_majors_le<K>(
    map: Map<K, TypedHeldLock>,
    major: LockMajorId,
) -> bool {
    forall|key: K|
        #![trigger map.dom().contains(key)]
        map.dom().contains(key) ==> map.index(key).lock_id.major <= major
}

/// Per-thread forward maps of held locks, partitioned by object family.
///
/// Each entry is keyed by the actual object locator and carries both its
/// current dynamic ordering id and its read/write mode. There is no parallel
/// reverse lock-id ledger.
pub tracked struct LocalContext {
    thread_id: LockThreadId,
    page_lock_map: Map<PageIndex, TypedHeldLock>,
    cpu_lock_map: Map<CpuId, TypedHeldLock>,
    container_lock_map: Map<RwLockContainerPtr, TypedHeldLock>,
    process_lock_map: Map<RwLockProcessPtr, TypedHeldLock>,
    thread_lock_map: Map<RwLockThreadPtr, TypedHeldLock>,
    endpoint_lock_map: Map<RwLockEndpointPtr, TypedHeldLock>,
    scheduler_lock_map: Map<RwLockSchedulerPtr, TypedHeldLock>,
    pcid_allocator_lock_map: Map<RwLockPcidAllocatorPtr, TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>,
    iommu_table_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>,
    allocator_4k_lock_maps: AllocatorLockMaps,
    allocator_2m_lock_maps: AllocatorLockMaps,
    allocator_1g_lock_maps: AllocatorLockMaps,
    state: LCtxtState,
}

impl LocalContext {
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }

    pub closed spec fn page_lock_map(&self) -> Map<PageIndex, TypedHeldLock> {
        self.page_lock_map
    }

    pub closed spec fn cpu_lock_map(&self) -> Map<CpuId, TypedHeldLock> {
        self.cpu_lock_map
    }

    pub closed spec fn container_lock_map(&self) -> Map<RwLockContainerPtr, TypedHeldLock> {
        self.container_lock_map
    }

    pub closed spec fn process_lock_map(&self) -> Map<RwLockProcessPtr, TypedHeldLock> {
        self.process_lock_map
    }

    pub closed spec fn thread_lock_map(&self) -> Map<RwLockThreadPtr, TypedHeldLock> {
        self.thread_lock_map
    }

    pub closed spec fn endpoint_lock_map(&self) -> Map<RwLockEndpointPtr, TypedHeldLock> {
        self.endpoint_lock_map
    }

    pub closed spec fn scheduler_lock_map(&self) -> Map<RwLockSchedulerPtr, TypedHeldLock> {
        self.scheduler_lock_map
    }

    pub closed spec fn pcid_allocator_lock_map(&self) -> Map<RwLockPcidAllocatorPtr, TypedHeldLock> {
        self.pcid_allocator_lock_map
    }

    pub closed spec fn pagetable_lock_map(&self) -> Map<RwLockPageTableRoot, TypedHeldLock> {
        self.pagetable_lock_map
    }

    pub closed spec fn iommu_table_lock_map(&self) -> Map<RwLockPageTableRoot, TypedHeldLock> {
        self.iommu_table_lock_map
    }

    pub closed spec fn allocator_4k_lock_maps(&self) -> AllocatorLockMaps {
        self.allocator_4k_lock_maps
    }

    pub closed spec fn allocator_2m_lock_maps(&self) -> AllocatorLockMaps {
        self.allocator_2m_lock_maps
    }

    pub closed spec fn allocator_1g_lock_maps(&self) -> AllocatorLockMaps {
        self.allocator_1g_lock_maps
    }

    pub open spec fn allocator_quota_4k_lock_map(&self) -> Map<RwLockPageAllocatorPtr, TypedHeldLock> {
        self.allocator_4k_lock_maps().quota
    }

    pub open spec fn allocator_quota_2m_lock_map(&self) -> Map<RwLockPageAllocatorPtr, TypedHeldLock> {
        self.allocator_2m_lock_maps().quota
    }

    pub open spec fn allocator_quota_1g_lock_map(&self) -> Map<RwLockPageAllocatorPtr, TypedHeldLock> {
        self.allocator_1g_lock_maps().quota
    }

    pub open spec fn allocator_cache_4k_lock_map(
        &self,
    ) -> Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock> {
        self.allocator_4k_lock_maps().cache
    }

    pub open spec fn allocator_cache_2m_lock_map(
        &self,
    ) -> Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock> {
        self.allocator_2m_lock_maps().cache
    }

    pub open spec fn allocator_cache_1g_lock_map(
        &self,
    ) -> Map<(RwLockPageAllocatorPtr, CpuId), TypedHeldLock> {
        self.allocator_1g_lock_maps().cache
    }

    pub open spec fn allocator_global_pool_4k_lock_map(
        &self,
    ) -> Map<RwLockPageAllocatorPtr, TypedHeldLock> {
        self.allocator_4k_lock_maps().global_pool
    }

    pub open spec fn allocator_global_pool_2m_lock_map(
        &self,
    ) -> Map<RwLockPageAllocatorPtr, TypedHeldLock> {
        self.allocator_2m_lock_maps().global_pool
    }

    pub open spec fn allocator_global_pool_1g_lock_map(
        &self,
    ) -> Map<RwLockPageAllocatorPtr, TypedHeldLock> {
        self.allocator_1g_lock_maps().global_pool
    }

    pub closed spec fn kernel_view_locking_state(&self) -> LCtxtLockState {
        self.state.kernel_view_locking_state
    }

    /// Read one lock record through its object-family tag.
    pub open spec fn typed_lock_entry(&self, obj_id: KernelObjId) -> Option<TypedHeldLock> {
        match obj_id {
            KernelObjId::Page(index) => if self.page_lock_map().dom().contains(index) {
                Some(self.page_lock_map().index(index))
            } else { None },
            KernelObjId::Cpu(cpu_id) => if self.cpu_lock_map().dom().contains(cpu_id) {
                Some(self.cpu_lock_map().index(cpu_id))
            } else { None },
            KernelObjId::Container(ptr) => if self.container_lock_map().dom().contains(ptr) {
                Some(self.container_lock_map().index(ptr))
            } else { None },
            KernelObjId::Process(ptr) => if self.process_lock_map().dom().contains(ptr) {
                Some(self.process_lock_map().index(ptr))
            } else { None },
            KernelObjId::Thread(ptr) => if self.thread_lock_map().dom().contains(ptr) {
                Some(self.thread_lock_map().index(ptr))
            } else { None },
            KernelObjId::Endpoint(ptr) => if self.endpoint_lock_map().dom().contains(ptr) {
                Some(self.endpoint_lock_map().index(ptr))
            } else { None },
            KernelObjId::Scheduler(ptr) => if self.scheduler_lock_map().dom().contains(ptr) {
                Some(self.scheduler_lock_map().index(ptr))
            } else { None },
            KernelObjId::PcidAllocator(ptr) => if self.pcid_allocator_lock_map().dom().contains(ptr) {
                Some(self.pcid_allocator_lock_map().index(ptr))
            } else { None },
            KernelObjId::PageTable(ptr) => if self.pagetable_lock_map().dom().contains(ptr) {
                Some(self.pagetable_lock_map().index(ptr))
            } else { None },
            KernelObjId::IommuTable(ptr) => if self.iommu_table_lock_map().dom().contains(ptr) {
                Some(self.iommu_table_lock_map().index(ptr))
            } else { None },
            KernelObjId::AllocatorQuota(PageSize::SZ4k, ptr) =>
                if self.allocator_quota_4k_lock_map().dom().contains(ptr) {
                    Some(self.allocator_quota_4k_lock_map().index(ptr))
                } else { None },
            KernelObjId::AllocatorQuota(PageSize::SZ2m, ptr) =>
                if self.allocator_quota_2m_lock_map().dom().contains(ptr) {
                    Some(self.allocator_quota_2m_lock_map().index(ptr))
                } else { None },
            KernelObjId::AllocatorQuota(PageSize::SZ1g, ptr) =>
                if self.allocator_quota_1g_lock_map().dom().contains(ptr) {
                    Some(self.allocator_quota_1g_lock_map().index(ptr))
                } else { None },
            KernelObjId::AllocatorCache(PageSize::SZ4k, ptr, cpu_id) =>
                if self.allocator_cache_4k_lock_map().dom().contains((ptr, cpu_id)) {
                    Some(self.allocator_cache_4k_lock_map().index((ptr, cpu_id)))
                } else { None },
            KernelObjId::AllocatorCache(PageSize::SZ2m, ptr, cpu_id) =>
                if self.allocator_cache_2m_lock_map().dom().contains((ptr, cpu_id)) {
                    Some(self.allocator_cache_2m_lock_map().index((ptr, cpu_id)))
                } else { None },
            KernelObjId::AllocatorCache(PageSize::SZ1g, ptr, cpu_id) =>
                if self.allocator_cache_1g_lock_map().dom().contains((ptr, cpu_id)) {
                    Some(self.allocator_cache_1g_lock_map().index((ptr, cpu_id)))
                } else { None },
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, ptr) =>
                if self.allocator_global_pool_4k_lock_map().dom().contains(ptr) {
                    Some(self.allocator_global_pool_4k_lock_map().index(ptr))
                } else { None },
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, ptr) =>
                if self.allocator_global_pool_2m_lock_map().dom().contains(ptr) {
                    Some(self.allocator_global_pool_2m_lock_map().index(ptr))
                } else { None },
            KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, ptr) =>
                if self.allocator_global_pool_1g_lock_map().dom().contains(ptr) {
                    Some(self.allocator_global_pool_1g_lock_map().index(ptr))
                } else { None },
        }
    }

    pub open spec fn lock_entry_contains(
        &self,
        lock_id: LockId,
        obj_id: KernelObjId,
    ) -> bool {
        match self.typed_lock_entry(obj_id) {
            Some(entry) => entry.lock_id == lock_id,
            None => false,
        }
    }

    pub open spec fn lock_obj_contains(&self, obj_id: KernelObjId) -> bool {
        self.typed_lock_entry(obj_id) is Some
    }

    pub open spec fn no_locks_held(&self) -> bool {
        &&& self.page_lock_map().dom().is_empty()
        &&& self.cpu_lock_map().dom().is_empty()
        &&& self.container_lock_map().dom().is_empty()
        &&& self.process_lock_map().dom().is_empty()
        &&& self.thread_lock_map().dom().is_empty()
        &&& self.endpoint_lock_map().dom().is_empty()
        &&& self.scheduler_lock_map().dom().is_empty()
        &&& self.pcid_allocator_lock_map().dom().is_empty()
        &&& self.pagetable_lock_map().dom().is_empty()
        &&& self.iommu_table_lock_map().dom().is_empty()
        &&& self.allocator_quota_4k_lock_map().dom().is_empty()
        &&& self.allocator_cache_4k_lock_map().dom().is_empty()
        &&& self.allocator_global_pool_4k_lock_map().dom().is_empty()
        &&& self.allocator_quota_2m_lock_map().dom().is_empty()
        &&& self.allocator_cache_2m_lock_map().dom().is_empty()
        &&& self.allocator_global_pool_2m_lock_map().dom().is_empty()
        &&& self.allocator_quota_1g_lock_map().dom().is_empty()
        &&& self.allocator_cache_1g_lock_map().dom().is_empty()
        &&& self.allocator_global_pool_1g_lock_map().dom().is_empty()
    }

    /// Exact typed-map scope used while unwinding the ordinary syscall locks.
    pub open spec fn cpu_process_thread_lock_scope(
        &self,
        cpus: Set<CpuId>,
        processes: Set<RwLockProcessPtr>,
        threads: Set<RwLockThreadPtr>,
    ) -> bool {
        &&& self.page_lock_map().dom().is_empty()
        &&& self.cpu_lock_map().dom() =~= cpus
        &&& self.container_lock_map().dom().is_empty()
        &&& self.process_lock_map().dom() =~= processes
        &&& self.thread_lock_map().dom() =~= threads
        &&& self.endpoint_lock_map().dom().is_empty()
        &&& self.scheduler_lock_map().dom().is_empty()
        &&& self.pcid_allocator_lock_map().dom().is_empty()
        &&& self.pagetable_lock_map().dom().is_empty()
        &&& self.iommu_table_lock_map().dom().is_empty()
        &&& self.allocator_quota_4k_lock_map().dom().is_empty()
        &&& self.allocator_cache_4k_lock_map().dom().is_empty()
        &&& self.allocator_global_pool_4k_lock_map().dom().is_empty()
        &&& self.allocator_quota_2m_lock_map().dom().is_empty()
        &&& self.allocator_cache_2m_lock_map().dom().is_empty()
        &&& self.allocator_global_pool_2m_lock_map().dom().is_empty()
        &&& self.allocator_quota_1g_lock_map().dom().is_empty()
        &&& self.allocator_cache_1g_lock_map().dom().is_empty()
        &&& self.allocator_global_pool_1g_lock_map().dom().is_empty()
    }

    /// `lock_id` is strictly greater than every held id.
    pub open spec fn lock_id_acyclic(&self, lock_id: LockId) -> bool {
        &&& typed_lock_map_ids_acyclic(self.page_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.cpu_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.container_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.process_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.thread_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.endpoint_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.scheduler_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.pcid_allocator_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.pagetable_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.iommu_table_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_quota_4k_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_cache_4k_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_global_pool_4k_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_quota_2m_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_cache_2m_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_global_pool_2m_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_quota_1g_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_cache_1g_lock_map(), lock_id)
        &&& typed_lock_map_ids_acyclic(self.allocator_global_pool_1g_lock_map(), lock_id)
    }

    pub open spec fn held_lock_majors_lt(&self, major: LockMajorId) -> bool {
        &&& typed_lock_map_majors_lt(self.page_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.cpu_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.container_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.process_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.thread_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.endpoint_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.scheduler_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.pcid_allocator_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.pagetable_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.iommu_table_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_quota_4k_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_cache_4k_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_global_pool_4k_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_quota_2m_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_cache_2m_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_global_pool_2m_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_quota_1g_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_cache_1g_lock_map(), major)
        &&& typed_lock_map_majors_lt(self.allocator_global_pool_1g_lock_map(), major)
    }

    pub open spec fn held_lock_majors_le(&self, major: LockMajorId) -> bool {
        &&& typed_lock_map_majors_le(self.page_lock_map(), major)
        &&& typed_lock_map_majors_le(self.cpu_lock_map(), major)
        &&& typed_lock_map_majors_le(self.container_lock_map(), major)
        &&& typed_lock_map_majors_le(self.process_lock_map(), major)
        &&& typed_lock_map_majors_le(self.thread_lock_map(), major)
        &&& typed_lock_map_majors_le(self.endpoint_lock_map(), major)
        &&& typed_lock_map_majors_le(self.scheduler_lock_map(), major)
        &&& typed_lock_map_majors_le(self.pcid_allocator_lock_map(), major)
        &&& typed_lock_map_majors_le(self.pagetable_lock_map(), major)
        &&& typed_lock_map_majors_le(self.iommu_table_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_quota_4k_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_cache_4k_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_global_pool_4k_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_quota_2m_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_cache_2m_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_global_pool_2m_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_quota_1g_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_cache_1g_lock_map(), major)
        &&& typed_lock_map_majors_le(self.allocator_global_pool_1g_lock_map(), major)
    }

    pub open spec fn holds_no_allocator_locks(&self, page_size: PageSize) -> bool {
        match page_size {
            PageSize::SZ4k => {
                &&& self.allocator_quota_4k_lock_map().dom().is_empty()
                &&& self.allocator_cache_4k_lock_map().dom().is_empty()
                &&& self.allocator_global_pool_4k_lock_map().dom().is_empty()
            },
            PageSize::SZ2m => {
                &&& self.allocator_quota_2m_lock_map().dom().is_empty()
                &&& self.allocator_cache_2m_lock_map().dom().is_empty()
                &&& self.allocator_global_pool_2m_lock_map().dom().is_empty()
            },
            PageSize::SZ1g => {
                &&& self.allocator_quota_1g_lock_map().dom().is_empty()
                &&& self.allocator_cache_1g_lock_map().dom().is_empty()
                &&& self.allocator_global_pool_1g_lock_map().dom().is_empty()
            },
        }
    }

    #[verifier::opaque]
    pub open spec fn holds_no_typed_allocator_locks(
        &self,
        page_size: PageSize,
    ) -> bool {
        match page_size {
            PageSize::SZ4k => {
                &&& self.allocator_quota_4k_lock_map().dom().is_empty()
                &&& self.allocator_cache_4k_lock_map().dom().is_empty()
                &&& self.allocator_global_pool_4k_lock_map().dom().is_empty()
            },
            PageSize::SZ2m => {
                &&& self.allocator_quota_2m_lock_map().dom().is_empty()
                &&& self.allocator_cache_2m_lock_map().dom().is_empty()
                &&& self.allocator_global_pool_2m_lock_map().dom().is_empty()
            },
            PageSize::SZ1g => {
                &&& self.allocator_quota_1g_lock_map().dom().is_empty()
                &&& self.allocator_cache_1g_lock_map().dom().is_empty()
                &&& self.allocator_global_pool_1g_lock_map().dom().is_empty()
            },
        }
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

    /// TCB: close the Acquire phase without changing any typed lock map.
    #[verifier::external_body]
    pub proof fn enter_kernel_view_release(tracked &mut self)
        requires
            old(self).kernel_view_locking_state() is Acquire,
        ensures
            final(self).thread_id() == old(self).thread_id(),
            final(self).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(self), final(self)),
    {
        unimplemented!()
    }

    /// TCB: replace one held object's dynamic id during Release.
    #[verifier::external_body]
    pub proof fn update_lock_id(
        tracked &mut self,
        obj_id: KernelObjId,
        old_entry: TypedHeldLock,
        new_lock_id: LockId,
    )
        requires
            old(self).kernel_view_locking_state() is Release,
            old(self).typed_lock_entry(obj_id) == Some(old_entry),
        ensures
            final(self).thread_id() == old(self).thread_id(),
            typed_lock_maps_inserted(
                old(self), final(self), obj_id,
                TypedHeldLock {
                    lock_id: new_lock_id,
                    mode: old_entry.mode,
                }),
            final(self).lock_entry_contains(new_lock_id, obj_id),
            old_entry.lock_id != new_lock_id ==>
                !final(self).lock_entry_contains(old_entry.lock_id, obj_id),
            final(self).kernel_view_locking_state()
                == old(self).kernel_view_locking_state(),
    {
        unimplemented!()
    }
}

pub open spec fn typed_lock_maps_unchanged(
    old: &LocalContext,
    new: &LocalContext,
) -> bool {
    &&& new.page_lock_map() == old.page_lock_map()
    &&& new.cpu_lock_map() == old.cpu_lock_map()
    &&& new.container_lock_map() == old.container_lock_map()
    &&& new.process_lock_map() == old.process_lock_map()
    &&& new.thread_lock_map() == old.thread_lock_map()
    &&& new.endpoint_lock_map() == old.endpoint_lock_map()
    &&& new.scheduler_lock_map() == old.scheduler_lock_map()
    &&& new.pcid_allocator_lock_map() == old.pcid_allocator_lock_map()
    &&& new.pagetable_lock_map() == old.pagetable_lock_map()
    &&& new.iommu_table_lock_map() == old.iommu_table_lock_map()
    &&& new.allocator_quota_4k_lock_map() == old.allocator_quota_4k_lock_map()
    &&& new.allocator_cache_4k_lock_map() == old.allocator_cache_4k_lock_map()
    &&& new.allocator_global_pool_4k_lock_map()
        == old.allocator_global_pool_4k_lock_map()
    &&& new.allocator_2m_lock_maps() == old.allocator_2m_lock_maps()
    &&& new.allocator_1g_lock_maps() == old.allocator_1g_lock_maps()
}

pub open spec fn typed_lock_maps_inserted(
    old: &LocalContext,
    new: &LocalContext,
    obj_id: KernelObjId,
    entry: TypedHeldLock,
) -> bool {
    &&& new.page_lock_map() == match obj_id {
        KernelObjId::Page(index) => old.page_lock_map().insert(index, entry),
        _ => old.page_lock_map(),
    }
    &&& new.cpu_lock_map() == match obj_id {
        KernelObjId::Cpu(cpu_id) => old.cpu_lock_map().insert(cpu_id, entry),
        _ => old.cpu_lock_map(),
    }
    &&& new.container_lock_map() == match obj_id {
        KernelObjId::Container(ptr) => old.container_lock_map().insert(ptr, entry),
        _ => old.container_lock_map(),
    }
    &&& new.process_lock_map() == match obj_id {
        KernelObjId::Process(ptr) => old.process_lock_map().insert(ptr, entry),
        _ => old.process_lock_map(),
    }
    &&& new.thread_lock_map() == match obj_id {
        KernelObjId::Thread(ptr) => old.thread_lock_map().insert(ptr, entry),
        _ => old.thread_lock_map(),
    }
    &&& new.endpoint_lock_map() == match obj_id {
        KernelObjId::Endpoint(ptr) => old.endpoint_lock_map().insert(ptr, entry),
        _ => old.endpoint_lock_map(),
    }
    &&& new.scheduler_lock_map() == match obj_id {
        KernelObjId::Scheduler(ptr) => old.scheduler_lock_map().insert(ptr, entry),
        _ => old.scheduler_lock_map(),
    }
    &&& new.pcid_allocator_lock_map() == match obj_id {
        KernelObjId::PcidAllocator(ptr) => old.pcid_allocator_lock_map().insert(ptr, entry),
        _ => old.pcid_allocator_lock_map(),
    }
    &&& new.pagetable_lock_map() == match obj_id {
        KernelObjId::PageTable(ptr) => old.pagetable_lock_map().insert(ptr, entry),
        _ => old.pagetable_lock_map(),
    }
    &&& new.iommu_table_lock_map() == match obj_id {
        KernelObjId::IommuTable(ptr) => old.iommu_table_lock_map().insert(ptr, entry),
        _ => old.iommu_table_lock_map(),
    }
    &&& new.allocator_quota_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorQuota(PageSize::SZ4k, ptr) =>
            old.allocator_quota_4k_lock_map().insert(ptr, entry),
        _ => old.allocator_quota_4k_lock_map(),
    }
    &&& new.allocator_cache_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorCache(PageSize::SZ4k, ptr, cpu_id) =>
            old.allocator_cache_4k_lock_map().insert((ptr, cpu_id), entry),
        _ => old.allocator_cache_4k_lock_map(),
    }
    &&& new.allocator_global_pool_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, ptr) =>
            old.allocator_global_pool_4k_lock_map().insert(ptr, entry),
        _ => old.allocator_global_pool_4k_lock_map(),
    }
    &&& new.allocator_2m_lock_maps() == match obj_id {
        KernelObjId::AllocatorQuota(PageSize::SZ2m, ptr) => AllocatorLockMaps {
            quota: old.allocator_quota_2m_lock_map().insert(ptr, entry),
            cache: old.allocator_cache_2m_lock_map(),
            global_pool: old.allocator_global_pool_2m_lock_map(),
        },
        KernelObjId::AllocatorCache(PageSize::SZ2m, ptr, cpu_id) => AllocatorLockMaps {
            quota: old.allocator_quota_2m_lock_map(),
            cache: old.allocator_cache_2m_lock_map().insert((ptr, cpu_id), entry),
            global_pool: old.allocator_global_pool_2m_lock_map(),
        },
        KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, ptr) => AllocatorLockMaps {
            quota: old.allocator_quota_2m_lock_map(),
            cache: old.allocator_cache_2m_lock_map(),
            global_pool: old.allocator_global_pool_2m_lock_map().insert(ptr, entry),
        },
        _ => old.allocator_2m_lock_maps(),
    }
    &&& new.allocator_1g_lock_maps() == match obj_id {
        KernelObjId::AllocatorQuota(PageSize::SZ1g, ptr) => AllocatorLockMaps {
            quota: old.allocator_quota_1g_lock_map().insert(ptr, entry),
            cache: old.allocator_cache_1g_lock_map(),
            global_pool: old.allocator_global_pool_1g_lock_map(),
        },
        KernelObjId::AllocatorCache(PageSize::SZ1g, ptr, cpu_id) => AllocatorLockMaps {
            quota: old.allocator_quota_1g_lock_map(),
            cache: old.allocator_cache_1g_lock_map().insert((ptr, cpu_id), entry),
            global_pool: old.allocator_global_pool_1g_lock_map(),
        },
        KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, ptr) => AllocatorLockMaps {
            quota: old.allocator_quota_1g_lock_map(),
            cache: old.allocator_cache_1g_lock_map(),
            global_pool: old.allocator_global_pool_1g_lock_map().insert(ptr, entry),
        },
        _ => old.allocator_1g_lock_maps(),
    }
}

pub open spec fn typed_lock_maps_removed(
    old: &LocalContext,
    new: &LocalContext,
    obj_id: KernelObjId,
) -> bool {
    &&& new.page_lock_map() == match obj_id {
        KernelObjId::Page(index) => old.page_lock_map().remove(index),
        _ => old.page_lock_map(),
    }
    &&& new.cpu_lock_map() == match obj_id {
        KernelObjId::Cpu(cpu_id) => old.cpu_lock_map().remove(cpu_id),
        _ => old.cpu_lock_map(),
    }
    &&& new.container_lock_map() == match obj_id {
        KernelObjId::Container(ptr) => old.container_lock_map().remove(ptr),
        _ => old.container_lock_map(),
    }
    &&& new.process_lock_map() == match obj_id {
        KernelObjId::Process(ptr) => old.process_lock_map().remove(ptr),
        _ => old.process_lock_map(),
    }
    &&& new.thread_lock_map() == match obj_id {
        KernelObjId::Thread(ptr) => old.thread_lock_map().remove(ptr),
        _ => old.thread_lock_map(),
    }
    &&& new.endpoint_lock_map() == match obj_id {
        KernelObjId::Endpoint(ptr) => old.endpoint_lock_map().remove(ptr),
        _ => old.endpoint_lock_map(),
    }
    &&& new.scheduler_lock_map() == match obj_id {
        KernelObjId::Scheduler(ptr) => old.scheduler_lock_map().remove(ptr),
        _ => old.scheduler_lock_map(),
    }
    &&& new.pcid_allocator_lock_map() == match obj_id {
        KernelObjId::PcidAllocator(ptr) => old.pcid_allocator_lock_map().remove(ptr),
        _ => old.pcid_allocator_lock_map(),
    }
    &&& new.pagetable_lock_map() == match obj_id {
        KernelObjId::PageTable(ptr) => old.pagetable_lock_map().remove(ptr),
        _ => old.pagetable_lock_map(),
    }
    &&& new.iommu_table_lock_map() == match obj_id {
        KernelObjId::IommuTable(ptr) => old.iommu_table_lock_map().remove(ptr),
        _ => old.iommu_table_lock_map(),
    }
    &&& new.allocator_quota_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorQuota(PageSize::SZ4k, ptr) =>
            old.allocator_quota_4k_lock_map().remove(ptr),
        _ => old.allocator_quota_4k_lock_map(),
    }
    &&& new.allocator_cache_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorCache(PageSize::SZ4k, ptr, cpu_id) =>
            old.allocator_cache_4k_lock_map().remove((ptr, cpu_id)),
        _ => old.allocator_cache_4k_lock_map(),
    }
    &&& new.allocator_global_pool_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, ptr) =>
            old.allocator_global_pool_4k_lock_map().remove(ptr),
        _ => old.allocator_global_pool_4k_lock_map(),
    }
    &&& new.allocator_2m_lock_maps() == match obj_id {
        KernelObjId::AllocatorQuota(PageSize::SZ2m, ptr) => AllocatorLockMaps {
            quota: old.allocator_quota_2m_lock_map().remove(ptr),
            cache: old.allocator_cache_2m_lock_map(),
            global_pool: old.allocator_global_pool_2m_lock_map(),
        },
        KernelObjId::AllocatorCache(PageSize::SZ2m, ptr, cpu_id) => AllocatorLockMaps {
            quota: old.allocator_quota_2m_lock_map(),
            cache: old.allocator_cache_2m_lock_map().remove((ptr, cpu_id)),
            global_pool: old.allocator_global_pool_2m_lock_map(),
        },
        KernelObjId::AllocatorGlobalPoll(PageSize::SZ2m, ptr) => AllocatorLockMaps {
            quota: old.allocator_quota_2m_lock_map(),
            cache: old.allocator_cache_2m_lock_map(),
            global_pool: old.allocator_global_pool_2m_lock_map().remove(ptr),
        },
        _ => old.allocator_2m_lock_maps(),
    }
    &&& new.allocator_1g_lock_maps() == match obj_id {
        KernelObjId::AllocatorQuota(PageSize::SZ1g, ptr) => AllocatorLockMaps {
            quota: old.allocator_quota_1g_lock_map().remove(ptr),
            cache: old.allocator_cache_1g_lock_map(),
            global_pool: old.allocator_global_pool_1g_lock_map(),
        },
        KernelObjId::AllocatorCache(PageSize::SZ1g, ptr, cpu_id) => AllocatorLockMaps {
            quota: old.allocator_quota_1g_lock_map(),
            cache: old.allocator_cache_1g_lock_map().remove((ptr, cpu_id)),
            global_pool: old.allocator_global_pool_1g_lock_map(),
        },
        KernelObjId::AllocatorGlobalPoll(PageSize::SZ1g, ptr) => AllocatorLockMaps {
            quota: old.allocator_quota_1g_lock_map(),
            cache: old.allocator_cache_1g_lock_map(),
            global_pool: old.allocator_global_pool_1g_lock_map().remove(ptr),
        },
        _ => old.allocator_1g_lock_maps(),
    }
}

pub open spec fn lock_ensures<T>(
    old: &LocalContext,
    new: &LocalContext,
    value: T,
    lock_id: LockId,
    obj_id: KernelObjId,
) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& new.kernel_view_locking_state() is Acquire
    &&& typed_lock_maps_inserted(old, new, obj_id, TypedHeldLock {
        lock_id,
        mode: TypedLockMode::Write,
    })
}

pub open spec fn unlock_ensures<T>(
    old: &LocalContext,
    new: &LocalContext,
    value: T,
    lock_token: LockToken,
    obj_id: KernelObjId,
    lock_id: LockId,
) -> bool {
    &&& new.thread_id() == old.thread_id()
    &&& old.kernel_view_locking_state() is Acquire
        ==> new.kernel_view_locking_state() is Release
    &&& old.kernel_view_locking_state() is Release
        ==> new.kernel_view_locking_state() is Release
    &&& !new.lock_entry_contains(lock_id, obj_id)
    &&& typed_lock_maps_removed(old, new, obj_id)
}

}
