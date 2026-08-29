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

/// Per-thread ledger of held locks.
///
/// Every entry records the exact ordering id and object used by the physical
/// lock. If a held object's dynamic ordering id changes during Release, the
/// corresponding pair is replaced explicitly by `update_lock_id`.
pub tracked struct LocalContext {
    thread_id: LockThreadId,
    lock_id_set: Set<HeldLock>,
    page_lock_set: Set<PageIndex>,
    cpu_lock_set: Set<CpuId>,
    container_lock_set: Set<RwLockContainerPtr>,
    process_lock_set: Set<RwLockProcessPtr>,
    thread_lock_set: Set<RwLockThreadPtr>,
    endpoint_lock_set: Set<RwLockEndpointPtr>,
    scheduler_lock_set: Set<RwLockSchedulerPtr>,
    pcid_allocator_lock_set: Set<RwLockPcidAllocatorPtr>,
    pagetable_lock_set: Set<RwLockPageTableRoot>,
    iommu_table_lock_set: Set<RwLockPageTableRoot>,
    allocator_quota_lock_set: Set<(PageSize, RwLockPageAllocatorPtr)>,
    allocator_cache_lock_set: Set<(PageSize, RwLockPageAllocatorPtr, CpuId)>,
    allocator_global_pool_lock_set: Set<(PageSize, RwLockPageAllocatorPtr)>,
    state: LCtxtState,
}

impl LocalContext {
    pub closed spec fn thread_id(&self) -> LockThreadId {
        self.thread_id
    }

    pub closed spec fn lock_id_set(&self) -> Set<HeldLock> {
        self.lock_id_set
    }

    pub closed spec fn page_lock_set(&self) -> Set<PageIndex> {
        self.page_lock_set
    }

    pub closed spec fn cpu_lock_set(&self) -> Set<CpuId> {
        self.cpu_lock_set
    }

    pub closed spec fn container_lock_set(&self) -> Set<RwLockContainerPtr> {
        self.container_lock_set
    }

    pub closed spec fn process_lock_set(&self) -> Set<RwLockProcessPtr> {
        self.process_lock_set
    }

    pub closed spec fn thread_lock_set(&self) -> Set<RwLockThreadPtr> {
        self.thread_lock_set
    }

    pub closed spec fn endpoint_lock_set(&self) -> Set<RwLockEndpointPtr> {
        self.endpoint_lock_set
    }

    pub closed spec fn scheduler_lock_set(&self) -> Set<RwLockSchedulerPtr> {
        self.scheduler_lock_set
    }

    pub closed spec fn pcid_allocator_lock_set(&self) -> Set<RwLockPcidAllocatorPtr> {
        self.pcid_allocator_lock_set
    }

    pub closed spec fn pagetable_lock_set(&self) -> Set<RwLockPageTableRoot> {
        self.pagetable_lock_set
    }

    pub closed spec fn iommu_table_lock_set(&self) -> Set<RwLockPageTableRoot> {
        self.iommu_table_lock_set
    }

    pub closed spec fn allocator_quota_lock_set(
        &self,
    ) -> Set<(PageSize, RwLockPageAllocatorPtr)> {
        self.allocator_quota_lock_set
    }

    pub closed spec fn allocator_cache_lock_set(
        &self,
    ) -> Set<(PageSize, RwLockPageAllocatorPtr, CpuId)> {
        self.allocator_cache_lock_set
    }

    pub closed spec fn allocator_global_pool_lock_set(
        &self,
    ) -> Set<(PageSize, RwLockPageAllocatorPtr)> {
        self.allocator_global_pool_lock_set
    }

    pub open spec fn held_lock_id_set(&self) -> Set<HeldLock> {
        self.lock_id_set()
    }

    pub closed spec fn kernel_view_locking_state(&self) -> LCtxtLockState {
        self.state.kernel_view_locking_state
    }

    pub open spec fn lock_entry_contains(
        &self,
        lock_id: LockId,
        obj_id: KernelObjId,
    ) -> bool {
        self.lock_id_set().contains((lock_id, obj_id))
    }

    pub open spec fn lock_obj_contains(&self, obj_id: KernelObjId) -> bool {
        exists|lock_id: LockId| self.lock_entry_contains(lock_id, obj_id)
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

    pub open spec fn holds_no_allocator_locks(&self, page_size: PageSize) -> bool {
        forall|held: HeldLock|
            #![trigger self.lock_id_set().contains(held)]
            self.lock_id_set().contains(held) ==> match held.1 {
                KernelObjId::AllocatorQuota(size, _) => size != page_size,
                KernelObjId::AllocatorCache(size, _, _) => size != page_size,
                KernelObjId::AllocatorGlobalPoll(size, _) => size != page_size,
                _ => true,
            }
    }

    #[verifier::opaque]
    pub open spec fn holds_no_typed_allocator_locks(
        &self,
        page_size: PageSize,
    ) -> bool {
        &&& (forall|ptr: RwLockPageAllocatorPtr|
            #![trigger self.allocator_quota_lock_set().contains((page_size, ptr))]
            !self.allocator_quota_lock_set().contains((page_size, ptr)))
        &&& (forall|ptr: RwLockPageAllocatorPtr, cpu_id: CpuId|
            #![trigger self.allocator_cache_lock_set().contains((page_size, ptr, cpu_id))]
            !self.allocator_cache_lock_set().contains((page_size, ptr, cpu_id)))
        &&& (forall|ptr: RwLockPageAllocatorPtr|
            #![trigger self.allocator_global_pool_lock_set().contains((page_size, ptr))]
            !self.allocator_global_pool_lock_set().contains((page_size, ptr)))
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

    /// TCB: close the Acquire phase without changing the held-lock ledger.
    #[verifier::external_body]
    pub proof fn enter_kernel_view_release(tracked &mut self)
        requires
            old(self).kernel_view_locking_state() is Acquire,
        ensures
            final(self).thread_id() == old(self).thread_id(),
            final(self).kernel_view_locking_state() is Release,
            final(self).lock_id_set() == old(self).lock_id_set(),
            typed_lock_sets_unchanged(old(self), final(self)),
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
            old(self).lock_id_set().contains((old_lock_id, obj_id)),
        ensures
            final(self).lock_id_set()
                == old(self).lock_id_set()
                    .remove((old_lock_id, obj_id))
                    .insert((new_lock_id, obj_id)),
            final(self).thread_id() == old(self).thread_id(),
            final(self).lock_id_set().contains((new_lock_id, obj_id)),
            old_lock_id != new_lock_id ==>
                !final(self).lock_id_set().contains((old_lock_id, obj_id)),
            forall|held: HeldLock|
                #![trigger final(self).lock_entry_contains(held.0, held.1)]
                held.1 != obj_id
                ==> final(self).lock_entry_contains(held.0, held.1)
                    == old(self).lock_entry_contains(held.0, held.1),
            final(self).kernel_view_locking_state()
                == old(self).kernel_view_locking_state(),
            typed_lock_sets_unchanged(old(self), final(self)),
    {
        unimplemented!()
    }
}

pub open spec fn typed_lock_sets_unchanged(
    old: &LocalContext,
    new: &LocalContext,
) -> bool {
    &&& new.page_lock_set() == old.page_lock_set()
    &&& new.cpu_lock_set() == old.cpu_lock_set()
    &&& new.container_lock_set() == old.container_lock_set()
    &&& new.process_lock_set() == old.process_lock_set()
    &&& new.thread_lock_set() == old.thread_lock_set()
    &&& new.endpoint_lock_set() == old.endpoint_lock_set()
    &&& new.scheduler_lock_set() == old.scheduler_lock_set()
    &&& new.pcid_allocator_lock_set() == old.pcid_allocator_lock_set()
    &&& new.pagetable_lock_set() == old.pagetable_lock_set()
    &&& new.iommu_table_lock_set() == old.iommu_table_lock_set()
    &&& new.allocator_quota_lock_set() == old.allocator_quota_lock_set()
    &&& new.allocator_cache_lock_set() == old.allocator_cache_lock_set()
    &&& new.allocator_global_pool_lock_set() == old.allocator_global_pool_lock_set()
}

pub open spec fn typed_lock_sets_inserted(
    old: &LocalContext,
    new: &LocalContext,
    obj_id: KernelObjId,
) -> bool {
    &&& new.page_lock_set() == match obj_id {
        KernelObjId::Page(index) => old.page_lock_set().insert(index),
        _ => old.page_lock_set(),
    }
    &&& new.cpu_lock_set() == match obj_id {
        KernelObjId::Cpu(cpu_id) => old.cpu_lock_set().insert(cpu_id),
        _ => old.cpu_lock_set(),
    }
    &&& new.container_lock_set() == match obj_id {
        KernelObjId::Container(ptr) => old.container_lock_set().insert(ptr),
        _ => old.container_lock_set(),
    }
    &&& new.process_lock_set() == match obj_id {
        KernelObjId::Process(ptr) => old.process_lock_set().insert(ptr),
        _ => old.process_lock_set(),
    }
    &&& new.thread_lock_set() == match obj_id {
        KernelObjId::Thread(ptr) => old.thread_lock_set().insert(ptr),
        _ => old.thread_lock_set(),
    }
    &&& new.endpoint_lock_set() == match obj_id {
        KernelObjId::Endpoint(ptr) => old.endpoint_lock_set().insert(ptr),
        _ => old.endpoint_lock_set(),
    }
    &&& new.scheduler_lock_set() == match obj_id {
        KernelObjId::Scheduler(ptr) => old.scheduler_lock_set().insert(ptr),
        _ => old.scheduler_lock_set(),
    }
    &&& new.pcid_allocator_lock_set() == match obj_id {
        KernelObjId::PcidAllocator(ptr) => old.pcid_allocator_lock_set().insert(ptr),
        _ => old.pcid_allocator_lock_set(),
    }
    &&& new.pagetable_lock_set() == match obj_id {
        KernelObjId::PageTable(ptr) => old.pagetable_lock_set().insert(ptr),
        _ => old.pagetable_lock_set(),
    }
    &&& new.iommu_table_lock_set() == match obj_id {
        KernelObjId::IommuTable(ptr) => old.iommu_table_lock_set().insert(ptr),
        _ => old.iommu_table_lock_set(),
    }
    &&& new.allocator_quota_lock_set() == match obj_id {
        KernelObjId::AllocatorQuota(size, ptr) =>
            old.allocator_quota_lock_set().insert((size, ptr)),
        _ => old.allocator_quota_lock_set(),
    }
    &&& new.allocator_cache_lock_set() == match obj_id {
        KernelObjId::AllocatorCache(size, ptr, cpu_id) =>
            old.allocator_cache_lock_set().insert((size, ptr, cpu_id)),
        _ => old.allocator_cache_lock_set(),
    }
    &&& new.allocator_global_pool_lock_set() == match obj_id {
        KernelObjId::AllocatorGlobalPoll(size, ptr) =>
            old.allocator_global_pool_lock_set().insert((size, ptr)),
        _ => old.allocator_global_pool_lock_set(),
    }
}

pub open spec fn typed_lock_sets_removed(
    old: &LocalContext,
    new: &LocalContext,
    obj_id: KernelObjId,
) -> bool {
    &&& new.page_lock_set() == match obj_id {
        KernelObjId::Page(index) => old.page_lock_set().remove(index),
        _ => old.page_lock_set(),
    }
    &&& new.cpu_lock_set() == match obj_id {
        KernelObjId::Cpu(cpu_id) => old.cpu_lock_set().remove(cpu_id),
        _ => old.cpu_lock_set(),
    }
    &&& new.container_lock_set() == match obj_id {
        KernelObjId::Container(ptr) => old.container_lock_set().remove(ptr),
        _ => old.container_lock_set(),
    }
    &&& new.process_lock_set() == match obj_id {
        KernelObjId::Process(ptr) => old.process_lock_set().remove(ptr),
        _ => old.process_lock_set(),
    }
    &&& new.thread_lock_set() == match obj_id {
        KernelObjId::Thread(ptr) => old.thread_lock_set().remove(ptr),
        _ => old.thread_lock_set(),
    }
    &&& new.endpoint_lock_set() == match obj_id {
        KernelObjId::Endpoint(ptr) => old.endpoint_lock_set().remove(ptr),
        _ => old.endpoint_lock_set(),
    }
    &&& new.scheduler_lock_set() == match obj_id {
        KernelObjId::Scheduler(ptr) => old.scheduler_lock_set().remove(ptr),
        _ => old.scheduler_lock_set(),
    }
    &&& new.pcid_allocator_lock_set() == match obj_id {
        KernelObjId::PcidAllocator(ptr) => old.pcid_allocator_lock_set().remove(ptr),
        _ => old.pcid_allocator_lock_set(),
    }
    &&& new.pagetable_lock_set() == match obj_id {
        KernelObjId::PageTable(ptr) => old.pagetable_lock_set().remove(ptr),
        _ => old.pagetable_lock_set(),
    }
    &&& new.iommu_table_lock_set() == match obj_id {
        KernelObjId::IommuTable(ptr) => old.iommu_table_lock_set().remove(ptr),
        _ => old.iommu_table_lock_set(),
    }
    &&& new.allocator_quota_lock_set() == match obj_id {
        KernelObjId::AllocatorQuota(size, ptr) =>
            old.allocator_quota_lock_set().remove((size, ptr)),
        _ => old.allocator_quota_lock_set(),
    }
    &&& new.allocator_cache_lock_set() == match obj_id {
        KernelObjId::AllocatorCache(size, ptr, cpu_id) =>
            old.allocator_cache_lock_set().remove((size, ptr, cpu_id)),
        _ => old.allocator_cache_lock_set(),
    }
    &&& new.allocator_global_pool_lock_set() == match obj_id {
        KernelObjId::AllocatorGlobalPoll(size, ptr) =>
            old.allocator_global_pool_lock_set().remove((size, ptr)),
        _ => old.allocator_global_pool_lock_set(),
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
    &&& new.lock_id_set() == old.lock_id_set().insert((lock_id, obj_id))
    &&& typed_lock_sets_inserted(old, new, obj_id)
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
    &&& new.lock_id_set() == old.lock_id_set().remove((lock_id, obj_id))
    &&& !new.lock_id_set().contains((lock_id, obj_id))
    &&& typed_lock_sets_removed(old, new, obj_id)
    &&& forall|held: HeldLock|
        #![trigger new.lock_entry_contains(held.0, held.1)]
        held.1 != obj_id
        ==> new.lock_entry_contains(held.0, held.1)
            == old.lock_entry_contains(held.0, held.1)
}

}
