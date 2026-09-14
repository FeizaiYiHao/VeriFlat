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

/// Per-thread ledger of held locks.
///
/// Every entry records the exact ordering id and object used by the physical
/// lock. If a held object's dynamic ordering id changes during Release, the
/// corresponding pair is replaced explicitly by `update_lock_id`.
pub tracked struct LocalContext {
    thread_id: LockThreadId,
    cpu_id: CpuId,
    page_lock_map: Map<PageIndex, TypedHeldLock>,
    cpu_lock_map: Map<CpuId, TypedHeldLock>,
    pcid_needflush_lock_map: Map<(CpuId, Pcid), TypedHeldLock>,
    container_lock_map: Map<RwLockContainerPtr, TypedHeldLock>,
    process_lock_map: Map<RwLockProcessPtr, TypedHeldLock>,
    thread_lock_map: Map<RwLockThreadPtr, TypedHeldLock>,
    endpoint_lock_map: Map<RwLockEndpointPtr, TypedHeldLock>,
    scheduler_lock_map: Map<RwLockSchedulerPtr, TypedHeldLock>,
    pcid_allocator_lock_map: Map<RwLockPcidAllocatorPtr, TypedHeldLock>,
    cpu_set_lock_map: Map<RwLockCpuSetPtr, TypedHeldLock>,
    pagetable_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>,
    iommu_table_lock_map: Map<RwLockPageTableRoot, TypedHeldLock>,
    allocator_4k_lock_maps: AllocatorLockMaps,
    allocator_2m_lock_maps: AllocatorLockMaps,
    allocator_1g_lock_maps: AllocatorLockMaps,
    lock_id_set: Set<HeldLock>,
    state: LCtxtState,
}

impl LocalContext {
    /// The executing CPU, fixed for this kernel execution; must be bound at entry.
    pub closed spec fn cpu_id(&self) -> CpuId {
        self.cpu_id
    }

    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }

    pub closed spec fn page_lock_map(&self) -> Map<PageIndex, TypedHeldLock> {
        self.page_lock_map
    }

    pub closed spec fn cpu_lock_map(&self) -> Map<CpuId, TypedHeldLock> {
        self.cpu_lock_map
    }

    pub closed spec fn pcid_needflush_lock_map(&self) -> Map<(CpuId, Pcid), TypedHeldLock> {
        self.pcid_needflush_lock_map
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

    pub closed spec fn cpu_set_lock_map(&self) -> Map<RwLockCpuSetPtr, TypedHeldLock> {
        self.cpu_set_lock_map
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

    pub closed spec fn lock_id_set(&self) -> Set<HeldLock> {
        self.lock_id_set
    }

    pub closed spec fn kernel_view_locking_state(&self) -> LCtxtLockState {
        self.state.kernel_view_locking_state
    }

    pub open spec fn typed_lock_entry(&self, obj_id: KernelObjId) -> Option<TypedHeldLock> {
        match obj_id {
            KernelObjId::Page(index) => if self.page_lock_map().dom().contains(index) {
                Some(self.page_lock_map().index(index))
            } else { None },
            KernelObjId::Cpu(cpu_id) => if self.cpu_lock_map().dom().contains(cpu_id) {
                Some(self.cpu_lock_map().index(cpu_id))
            } else { None },
            KernelObjId::PcidNeedFlush(cpu_id, pcid) => if self.pcid_needflush_lock_map().dom().contains((cpu_id, pcid)) {
                Some(self.pcid_needflush_lock_map().index((cpu_id, pcid)))
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
            KernelObjId::CpuSet(ptr) => if self.cpu_set_lock_map().dom().contains(ptr) {
                Some(self.cpu_set_lock_map().index(ptr))
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

    pub open spec fn lock_entry_contains(&self, lock_id: LockId, obj_id: KernelObjId) -> bool {
        match self.typed_lock_entry(obj_id) {
            Some(entry) => entry.lock_id == lock_id,
            None => false,
        }
    }

    pub open spec fn no_locks_held(&self) -> bool {
        &&& self.page_lock_map().dom().is_empty()
        &&& self.cpu_lock_map().dom().is_empty()
        &&& self.pcid_needflush_lock_map().dom().is_empty()
        &&& self.container_lock_map().dom().is_empty()
        &&& self.process_lock_map().dom().is_empty()
        &&& self.thread_lock_map().dom().is_empty()
        &&& self.endpoint_lock_map().dom().is_empty()
        &&& self.scheduler_lock_map().dom().is_empty()
        &&& self.pcid_allocator_lock_map().dom().is_empty()
        &&& self.cpu_set_lock_map().dom().is_empty()
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
        forall|held: HeldLock|
            #![trigger self.lock_id_set().contains(held)]
            self.lock_id_set().contains(held) ==> lock_id.spec_gt(held.0)
    }

    pub open spec fn held_lock_majors_lt(&self, major: LockMajorId) -> bool {
        forall|held: HeldLock|
            #![trigger self.lock_id_set().contains(held)]
            self.lock_id_set().contains(held) ==> held.0.major < major
    }

    pub open spec fn held_lock_majors_le(&self, major: LockMajorId) -> bool {
        forall|held: HeldLock|
            #![trigger self.lock_id_set().contains(held)]
            self.lock_id_set().contains(held) ==> held.0.major <= major
    }

    #[verifier::opaque]
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

    /// TCB: close the Acquire phase without changing either held-lock representation.
    #[verifier::external_body]
    pub proof fn enter_kernel_view_release(tracked &mut self)
        requires
            old(self).kernel_view_locking_state() is Acquire,
        ensures
            final(self).cpu_id() == old(self).cpu_id(),
            final(self).thread_id() == old(self).thread_id(),
            final(self).kernel_view_locking_state() is Release,
            final(self).lock_id_set() == old(self).lock_id_set(),
            typed_lock_maps_unchanged(old(self), final(self)),
            lock_id_set_aligned(old(self)) ==> lock_id_set_aligned(final(self)),
    {
        unimplemented!()
    }

    /// TCB: replace one held object's dynamic id during Release.
    #[verifier::external_body]
    pub proof fn update_lock_id(
        tracked &mut self,
        obj_id: KernelObjId,
        old_lock_id: LockId,
        new_lock_id: LockId,
    )
        requires
            old(self).kernel_view_locking_state() is Release,
            old(self).lock_entry_contains(old_lock_id, obj_id),
            lock_id_set_aligned(old(self)),
        ensures
            final(self).cpu_id() == old(self).cpu_id(),
            final(self).lock_id_set() == old(self).lock_id_set().remove((old_lock_id, obj_id)).insert((new_lock_id, obj_id)),
            typed_lock_maps_inserted(old(self), final(self), obj_id, TypedHeldLock {
                lock_id: new_lock_id,
                mode: match old(self).typed_lock_entry(obj_id) {
                    Some(entry) => entry.mode,
                    None => TypedLockMode::Write,
                },
            }),
            final(self).thread_lock_map() == match obj_id {
                KernelObjId::Thread(ptr) => old(self).thread_lock_map().insert(ptr, TypedHeldLock {
                    lock_id: new_lock_id,
                    mode: match old(self).typed_lock_entry(obj_id) {
                        Some(entry) => entry.mode,
                        None => TypedLockMode::Write,
                    },
                }),
                _ => old(self).thread_lock_map(),
            },
            final(self).typed_lock_entry(obj_id) == Some(TypedHeldLock {
                lock_id: new_lock_id,
                mode: match old(self).typed_lock_entry(obj_id) {
                    Some(entry) => entry.mode,
                    None => TypedLockMode::Write,
                },
            }),
            final(self).lock_entry_contains(new_lock_id, obj_id),
            final(self).thread_id() == old(self).thread_id(),
            final(self).lock_id_set().contains((new_lock_id, obj_id)),
            old_lock_id != new_lock_id ==> !final(self).lock_id_set().contains((old_lock_id, obj_id)),
            forall|held: HeldLock|
                #![trigger final(self).lock_id_set().contains((held.0, held.1))]
                held.1 != obj_id ==> final(self).lock_id_set().contains((held.0, held.1)) == old(self).lock_id_set().contains((held.0, held.1)),
            final(self).kernel_view_locking_state() == old(self).kernel_view_locking_state(),
            lock_id_set_aligned(final(self)),
    {
        unimplemented!()
    }
}

#[verifier::opaque]
pub open spec fn lock_id_set_aligned(lctx: &LocalContext) -> bool {
    &&& forall|held: HeldLock|
        #![trigger lctx.lock_id_set().contains(held)]
        lctx.lock_id_set().contains(held) ==> lctx.lock_entry_contains(held.0, held.1)
    &&& forall|obj_id: KernelObjId|
        #![trigger lctx.typed_lock_entry(obj_id)]
        match lctx.typed_lock_entry(obj_id) {
            Some(entry) => lctx.lock_id_set().contains((entry.lock_id, obj_id)),
            None => true,
        }
}

pub open spec fn typed_lock_maps_unchanged(old: &LocalContext, new: &LocalContext) -> bool {
    &&& new.page_lock_map() == old.page_lock_map()
    &&& new.cpu_lock_map() == old.cpu_lock_map()
    &&& new.pcid_needflush_lock_map() == old.pcid_needflush_lock_map()
    &&& new.container_lock_map() == old.container_lock_map()
    &&& new.process_lock_map() == old.process_lock_map()
    &&& new.thread_lock_map() == old.thread_lock_map()
    &&& new.endpoint_lock_map() == old.endpoint_lock_map()
    &&& new.scheduler_lock_map() == old.scheduler_lock_map()
    &&& new.pcid_allocator_lock_map() == old.pcid_allocator_lock_map()
    &&& new.cpu_set_lock_map() == old.cpu_set_lock_map()
    &&& new.pagetable_lock_map() == old.pagetable_lock_map()
    &&& new.iommu_table_lock_map() == old.iommu_table_lock_map()
    &&& new.allocator_quota_4k_lock_map() == old.allocator_quota_4k_lock_map()
    &&& new.allocator_cache_4k_lock_map() == old.allocator_cache_4k_lock_map()
    &&& new.allocator_global_pool_4k_lock_map() == old.allocator_global_pool_4k_lock_map()
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
    &&& new.pcid_needflush_lock_map() == match obj_id {
        KernelObjId::PcidNeedFlush(cpu_id, pcid) => old.pcid_needflush_lock_map().insert((cpu_id, pcid), entry),
        _ => old.pcid_needflush_lock_map(),
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
    &&& new.cpu_set_lock_map() == match obj_id {
        KernelObjId::CpuSet(ptr) => old.cpu_set_lock_map().insert(ptr, entry),
        _ => old.cpu_set_lock_map(),
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
        KernelObjId::AllocatorQuota(PageSize::SZ4k, ptr) => old.allocator_quota_4k_lock_map().insert(ptr, entry),
        _ => old.allocator_quota_4k_lock_map(),
    }
    &&& new.allocator_cache_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorCache(PageSize::SZ4k, ptr, cpu_id) => old.allocator_cache_4k_lock_map().insert((ptr, cpu_id), entry),
        _ => old.allocator_cache_4k_lock_map(),
    }
    &&& new.allocator_global_pool_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, ptr) => old.allocator_global_pool_4k_lock_map().insert(ptr, entry),
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

pub proof fn held_lock_majors_lt_preserved_for_fresh_typed_insert(
    old: &LocalContext,
    new: &LocalContext,
    obj_id: KernelObjId,
    entry: TypedHeldLock,
    major: LockMajorId,
)
    requires
        old.held_lock_majors_lt(major),
        old.typed_lock_entry(obj_id) is None,
        typed_lock_maps_inserted(old, new, obj_id, entry),
        lock_id_set_aligned(old),
        lock_id_set_aligned(new),
        entry.lock_id.major < major,
    ensures
        new.held_lock_majors_lt(major),
{
    if !new.held_lock_majors_lt(major) {
        let held = choose|held: HeldLock| #![auto] new.lock_id_set().contains(held) && held.0.major >= major;
        match old.typed_lock_entry(held.1) {
            Some(old_entry) => { assert(new.typed_lock_entry(held.1) == Some(old_entry) && held.0.major < major) by { reveal(lock_id_set_aligned); }; },
            None => { assert(new.typed_lock_entry(held.1) == Some(entry) && held.0.major < major) by { reveal(lock_id_set_aligned); }; },
        }
    }
}

pub broadcast proof fn held_lock_major_lt_preserved_for_typed_maps_unchanged(
    old: &LocalContext,
    new: &LocalContext,
    major: LockMajorId,
    held: HeldLock,
)
    requires
        #[trigger] old.held_lock_majors_lt(major),
        #[trigger] typed_lock_maps_unchanged(old, new),
        #[trigger] lock_id_set_aligned(old),
        #[trigger] lock_id_set_aligned(new),
    ensures
        #[trigger] new.lock_id_set().contains(held) ==> held.0.major < major,
{
    if new.lock_id_set().contains(held) {
        let obj_id = held.1;
        let entry = new.typed_lock_entry(obj_id)->0;
        assert({
            &&& new.lock_entry_contains(held.0, obj_id)
            &&& entry.lock_id == held.0
            &&& old.typed_lock_entry(obj_id) == Some(entry)
            &&& old.lock_id_set().contains((entry.lock_id, obj_id))
            &&& held.0.major < major
        }) by {
            reveal(lock_id_set_aligned);
        };
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
    &&& new.pcid_needflush_lock_map() == match obj_id {
        KernelObjId::PcidNeedFlush(cpu_id, pcid) => old.pcid_needflush_lock_map().remove((cpu_id, pcid)),
        _ => old.pcid_needflush_lock_map(),
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
    &&& new.cpu_set_lock_map() == match obj_id {
        KernelObjId::CpuSet(ptr) => old.cpu_set_lock_map().remove(ptr),
        _ => old.cpu_set_lock_map(),
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
        KernelObjId::AllocatorQuota(PageSize::SZ4k, ptr) => old.allocator_quota_4k_lock_map().remove(ptr),
        _ => old.allocator_quota_4k_lock_map(),
    }
    &&& new.allocator_cache_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorCache(PageSize::SZ4k, ptr, cpu_id) => old.allocator_cache_4k_lock_map().remove((ptr, cpu_id)),
        _ => old.allocator_cache_4k_lock_map(),
    }
    &&& new.allocator_global_pool_4k_lock_map() == match obj_id {
        KernelObjId::AllocatorGlobalPoll(PageSize::SZ4k, ptr) => old.allocator_global_pool_4k_lock_map().remove(ptr),
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

pub open spec fn lock_ensures(
    old: &LocalContext,
    new: &LocalContext,
    lock_id: LockId,
    obj_id: KernelObjId,
) -> bool {
    &&& new.cpu_id() == old.cpu_id()
    &&& new.thread_id() == old.thread_id()
    &&& new.kernel_view_locking_state() is Acquire
    &&& new.lock_id_set() == old.lock_id_set().insert((lock_id, obj_id))
    &&& typed_lock_maps_inserted(old, new, obj_id, TypedHeldLock {
        lock_id,
        mode: TypedLockMode::Write,
    })
    &&& lock_id_set_aligned(old) ==> lock_id_set_aligned(new)
}

pub open spec fn unlock_ensures(
    old: &LocalContext,
    new: &LocalContext,
    obj_id: KernelObjId,
    lock_id: LockId,
) -> bool {
    &&& new.cpu_id() == old.cpu_id()
    &&& new.thread_id() == old.thread_id()
    &&& old.kernel_view_locking_state() is Acquire ==> new.kernel_view_locking_state() is Release
    &&& old.kernel_view_locking_state() is Release ==> new.kernel_view_locking_state() is Release
    &&& new.lock_id_set() == old.lock_id_set().remove((lock_id, obj_id))
    &&& typed_lock_maps_removed(old, new, obj_id)
    &&& lock_id_set_aligned(old) ==> lock_id_set_aligned(new)
}

}
