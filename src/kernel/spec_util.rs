use vstd::prelude::*;
use crate::*;
use super::*;
verus! {

/// TODO kill all these
pub open spec fn cpu_objects_unlocked(
    cpu_array: CpuLockedArray,
    thread_id: LockThreadId,
) -> bool {
    forall|cpu_i: CpuId|
        #![trigger cpu_array.spec_index(cpu_i).view().locked_by_thread(thread_id), index_valid(NUM_CPUS, cpu_i)]
        index_valid(NUM_CPUS, cpu_i)
        ==>
        cpu_array.spec_index(cpu_i).view().locked_by_thread(thread_id) == false
}

#[verifier::opaque]
pub open spec fn cpu_objects_unlocked_except(
    cpu_array: CpuLockedArray,
    thread_id: LockThreadId,
    exceptions: Set<CpuId>,
) -> bool {
    forall|cpu_i: CpuId|
        #![trigger cpu_array.spec_index(cpu_i).view().locked_by_thread(thread_id), index_valid(NUM_CPUS, cpu_i)]
        index_valid(NUM_CPUS, cpu_i) && !exceptions.contains(cpu_i)
        ==> !cpu_array.spec_index(cpu_i).view().locked_by_thread(thread_id)
}

pub open spec fn page_objects_unlocked(
    page_array: PageLockedArray,
    thread_id: LockThreadId,
) -> bool {
    forall|p_i: PageIndex|
        #![trigger page_array.spec_index(p_i), index_valid(NUM_PAGES, p_i)]
        index_valid(NUM_PAGES, p_i)
        ==>
        page_array.spec_index(p_i).view().locked_by_thread(thread_id) == false
}

#[verifier::opaque]
pub open spec fn page_objects_unlocked_except(
    page_array: PageLockedArray,
    thread_id: LockThreadId,
    exceptions: Set<PageIndex>,
) -> bool {
    forall|p_i: PageIndex|
        #![trigger page_array.spec_index(p_i).view().locked_by_thread(thread_id), index_valid(NUM_PAGES, p_i)]
        index_valid(NUM_PAGES, p_i) && !exceptions.contains(p_i)
        ==> !page_array.spec_index(p_i).view().locked_by_thread(thread_id)
}

pub open spec fn container_objects_unlocked(
    container_map: ContainerLockedMap,
    thread_id: LockThreadId,
) -> bool {
    forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr)
        ==>
        container_map.spec_index(c_ptr).locked_by_thread(thread_id) == false
}

pub open spec fn process_objects_unlocked(
    process_map: ProcessLockedMap,
    thread_id: LockThreadId,
) -> bool {
    forall|p_ptr: RwLockProcessPtr|
        #![trigger process_map.dom().contains(p_ptr)]
        process_map.dom().contains(p_ptr)
        ==>
        process_map.spec_index(p_ptr).locked_by_thread(thread_id) == false
}

#[verifier::opaque]
pub open spec fn process_objects_unlocked_except(
    process_map: ProcessLockedMap,
    thread_id: LockThreadId,
    exceptions: Set<RwLockProcessPtr>,
) -> bool {
    forall|p_ptr: RwLockProcessPtr|
        #![trigger process_map.spec_index(p_ptr).locked_by_thread(thread_id)]
        process_map.dom().contains(p_ptr) && !exceptions.contains(p_ptr)
        ==> !process_map.spec_index(p_ptr).locked_by_thread(thread_id)
}

pub open spec fn thread_objects_unlocked(
    thread_map: ThreadLockedMap,
    thread_id: LockThreadId,
) -> bool {
    forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr)]
        thread_map.dom().contains(t_ptr)
        ==>
        thread_map.spec_index(t_ptr).locked_by_thread(thread_id) == false
}

#[verifier::opaque]
pub open spec fn thread_objects_unlocked_except(
    thread_map: ThreadLockedMap,
    thread_id: LockThreadId,
    exceptions: Set<RwLockThreadPtr>,
) -> bool {
    forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr).locked_by_thread(thread_id)]
        thread_map.dom().contains(t_ptr) && !exceptions.contains(t_ptr)
        ==> !thread_map.spec_index(t_ptr).locked_by_thread(thread_id)
}

pub open spec fn endpoint_objects_unlocked(
    endpoint_map: EndpointLockedMap,
    thread_id: LockThreadId,
) -> bool {
    forall|e_ptr: RwLockEndpointPtr|
        #![trigger endpoint_map.spec_index(e_ptr)]
        endpoint_map.dom().contains(e_ptr)
        ==>
        endpoint_map.spec_index(e_ptr).locked_by_thread(thread_id) == false
}

#[verifier::opaque]
pub open spec fn endpoint_objects_unlocked_except(
    endpoint_map: EndpointLockedMap,
    thread_id: LockThreadId,
    exceptions: Set<RwLockEndpointPtr>,
) -> bool {
    forall|e_ptr: RwLockEndpointPtr|
        #![trigger endpoint_map.spec_index(e_ptr).locked_by_thread(thread_id)]
        endpoint_map.dom().contains(e_ptr) && !exceptions.contains(e_ptr)
        ==> !endpoint_map.spec_index(e_ptr).locked_by_thread(thread_id)
}

pub open spec fn pagetable_objects_unlocked(
    pagetable_map: PageTableLockedMap,
    thread_id: LockThreadId,
) -> bool {
    forall|pt_ptr: RwLockPageTableRoot|
        #![trigger pagetable_map.spec_index(pt_ptr).locked_by_thread(thread_id)]
        pagetable_map.dom().contains(pt_ptr)
        ==>
        pagetable_map.spec_index(pt_ptr).locked_by_thread(thread_id) == false
}

pub open spec fn iommu_table_objects_unlocked(
    iommu_table_map: IommuTableLockedMap,
    thread_id: LockThreadId,
) -> bool {
    forall|iommu_root: RwLockPageTableRoot|
        #![trigger iommu_table_map.spec_index(iommu_root).locked_by_thread(thread_id)]
        iommu_table_map.dom().contains(iommu_root)
        ==> iommu_table_map.spec_index(iommu_root).locked_by_thread(thread_id) == false
}

pub open spec fn scheduler_objects_unlocked(
    scheduler_map: SchedulerLockedMap,
    thread_id: LockThreadId,
) -> bool {
    forall|s_ptr: RwLockSchedulerPtr|
        #![trigger scheduler_map.spec_index(s_ptr).locked_by_thread(thread_id)]
        scheduler_map.dom().contains(s_ptr)
        ==>
        scheduler_map.spec_index(s_ptr).locked_by_thread(thread_id) == false
}

#[verifier::opaque]
pub open spec fn scheduler_objects_unlocked_except(
    scheduler_map: SchedulerLockedMap,
    thread_id: LockThreadId,
    exceptions: Set<RwLockSchedulerPtr>,
) -> bool {
    forall|s_ptr: RwLockSchedulerPtr|
        #![trigger scheduler_map.spec_index(s_ptr).locked_by_thread(thread_id)]
        scheduler_map.dom().contains(s_ptr) && !exceptions.contains(s_ptr)
        ==> !scheduler_map.spec_index(s_ptr).locked_by_thread(thread_id)
}

pub open spec fn pcid_allocator_objects_unlocked(
    allocator_map: PcidAllocatorLockedMap,
    thread_id: LockThreadId,
) -> bool {
    forall|allocator_ptr: RwLockPcidAllocatorPtr|
        #![trigger allocator_map.spec_index(allocator_ptr).locked_by_thread(thread_id)]
        allocator_map.dom().contains(allocator_ptr)
        ==> allocator_map.spec_index(allocator_ptr).locked_by_thread(thread_id) == false
}

pub open spec fn allocator_objects_unlocked(
    alloc_map: PageAllocatorUnLockedMap,
    thread_id: LockThreadId,
) -> bool {
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr|
        #![trigger alloc_map.spec_index(alloc_ptr).global_pool]
        alloc_map.dom().contains(alloc_ptr)
        ==>
        alloc_map.spec_index(alloc_ptr).global_pool.locked_by_thread(thread_id) == false
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr|
        #![trigger alloc_map.spec_index(alloc_ptr).quota]
        alloc_map.dom().contains(alloc_ptr)
        ==>
        alloc_map.spec_index(alloc_ptr).quota.locked_by_thread(thread_id) == false
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId|
        #![trigger alloc_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i), index_valid(NUM_CPUS, cpu_i)]
        alloc_map.dom().contains(alloc_ptr) && index_valid(NUM_CPUS, cpu_i)
        ==>
        alloc_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view()
            .locked_by_thread(thread_id) == false
}

impl KernelK{
    pub open spec fn get_process_pagetable(&self, process_ptr:RwLockProcessPtr) -> PageTable<PT_TYPE>
        recommends
            self.process_map.dom().contains(process_ptr)
    {
        self.pagetable_map.spec_index(self.process_map.spec_index(process_ptr).view().pagetable).view()
    }

    pub open spec fn get_process_iommu_table(
        &self,
        process_ptr: RwLockProcessPtr,
    ) -> Option<PageTable<IOMMU_TYPE>>
        recommends
            self.process_map.dom().contains(process_ptr),
    {
        match self.process_map.spec_index(process_ptr).view().iommu_table {
            Some(iommu_root) => Some(
                self.iommu_table_map.spec_index(iommu_root).view(),
            ),
            None => None,
        }
    }
    pub open spec fn all_objects_unlocked(&self, lctx: &LocalContext) -> bool{
        &&& cpu_objects_unlocked(self.cpu_array, lctx.thread_id())
        &&& page_objects_unlocked(self.page_array, lctx.thread_id())
        &&& container_objects_unlocked(self.container_map, lctx.thread_id())
        &&& process_objects_unlocked(self.process_map, lctx.thread_id())
        &&& thread_objects_unlocked(self.thread_map, lctx.thread_id())
        &&& endpoint_objects_unlocked(self.endpoint_map, lctx.thread_id())
        &&& pagetable_objects_unlocked(self.pagetable_map, lctx.thread_id())
        &&& iommu_table_objects_unlocked(self.iommu_table_map, lctx.thread_id())
        &&& scheduler_objects_unlocked(self.scheduler_map, lctx.thread_id())
        &&& pcid_allocator_objects_unlocked(
            self.pcid_allocator_map, lctx.thread_id())
        &&& allocator_objects_unlocked(self.allocator_4k_map, lctx.thread_id())
        &&& allocator_objects_unlocked(self.allocator_2m_map, lctx.thread_id())
        &&& allocator_objects_unlocked(self.allocator_1g_map, lctx.thread_id())
    }

}
}
