use vstd::prelude::*;
use crate::*;
use super::*;
verus! {

impl KernelK{
    pub open spec fn get_process_pagetable(&self, process_ptr:RwLockProcessPtr) -> PageTable<PT_TYPE>
        recommends
            self.process_map.dom().contains(process_ptr)
    {
        self.pagetable_map.spec_index(self.process_map.spec_index(process_ptr).view().pagetable).view()
    }
    pub open spec fn get_container_quota_4k(&self, container_ptr:RwLockContainerPtr) -> usize
        recommends
            self.container_map.dom().contains(container_ptr)
    {
        self.allocator_4k_map.spec_index(self.container_map.spec_index(container_ptr).view_rodata().view().allocator_ptr_4k).quota.view().value
    }

    pub open spec fn all_objects_unlocked(&self, lctx: &LocalContext) -> bool{
        &&&
        forall|cpu_i: CpuId|
            #![trigger self.cpu_array.spec_index(cpu_i).view().locked_by(lctx)]
            cpu_id_valid(cpu_i) 
            ==>
            self.cpu_array.spec_index(cpu_i).view().locked_by(lctx) == false
        &&&
        forall|p_i: PageIndex|
            #![trigger self.page_array.spec_index(p_i).view().locked_by(lctx)]
            page_index_valid(p_i) 
            ==>
            self.page_array.spec_index(p_i).view().locked_by(lctx) == false
        &&&
        forall|c_ptr:RwLockContainerPtr|
            #![trigger self.container_map.dom().contains(c_ptr)]
            self.container_map.dom().contains(c_ptr)
            ==>
            self.container_map.spec_index(c_ptr).locked_by(lctx) == false
        &&&
        forall|p_ptr:RwLockProcessPtr|
            #![trigger self.process_map.spec_index(p_ptr).locked_by(lctx)]
            self.process_map.dom().contains(p_ptr)
            ==>
            self.process_map.spec_index(p_ptr).locked_by(lctx) == false
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger self.thread_map.spec_index(t_ptr).locked_by(lctx)]
            self.thread_map.dom().contains(t_ptr)
            ==>
            self.thread_map.spec_index(t_ptr).locked_by(lctx) == false
        &&&
        forall|e_ptr:RwLockEndpointPtr|
            #![trigger self.endpoint_map.spec_index(e_ptr).locked_by(lctx)]
            self.endpoint_map.dom().contains(e_ptr)
            ==>
            self.endpoint_map.spec_index(e_ptr).locked_by(lctx) == false
        &&&
        forall|pt_ptr:RwLockPageTableRoot|
            #![trigger self.pagetable_map.spec_index(pt_ptr).locked_by(lctx)]
            self.pagetable_map.dom().contains(pt_ptr)
            ==>
            self.pagetable_map.spec_index(pt_ptr).locked_by(lctx) == false
        &&&
        forall|s_ptr:RwLockSchedulerPtr|
            #![trigger self.scheduler_map.spec_index(s_ptr).locked_by(lctx)]
            self.scheduler_map.dom().contains(s_ptr)
            ==>
            self.scheduler_map.spec_index(s_ptr).locked_by(lctx) == false
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr|
            #![trigger self.allocator_4k_map.spec_index(alloc_ptr).global_poll.locked_by(lctx)]
            self.allocator_4k_map.dom().contains(alloc_ptr)
            ==>
            self.allocator_4k_map.spec_index(alloc_ptr).global_poll.locked_by(lctx) == false
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i: CpuId|
            #![trigger self.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx)]
            self.allocator_4k_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
            ==>
            self.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx) == false
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr|
            #![trigger self.allocator_2m_map.spec_index(alloc_ptr).global_poll.locked_by(lctx)]
            self.allocator_2m_map.dom().contains(alloc_ptr)
            ==>
            self.allocator_2m_map.spec_index(alloc_ptr).global_poll.locked_by(lctx) == false
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i: CpuId|
            #![trigger self.allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx)]
            self.allocator_2m_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
            ==>
            self.allocator_2m_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx) == false
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr|
            #![trigger self.allocator_1g_map.spec_index(alloc_ptr).global_poll.locked_by(lctx)]
            self.allocator_1g_map.dom().contains(alloc_ptr)
            ==>
            self.allocator_1g_map.spec_index(alloc_ptr).global_poll.locked_by(lctx) == false
        &&&
        forall|alloc_ptr:RwLockPageAllocatorPtr, cpu_i: CpuId|
            #![trigger self.allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx)]
            self.allocator_1g_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
            ==>
            self.allocator_1g_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx) == false
    }
}

}