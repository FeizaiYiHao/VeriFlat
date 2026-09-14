use vstd::prelude::*;
use crate::*;

verus! {

impl KernelK {
    #[verifier::opaque]
    pub open spec fn all_objects_unlocked(&self, lctx: &LocalContext) -> bool {
        &&& forall|cpu_id: CpuId, pcid: Pcid|
            #![trigger self.pcid_needflush.spec_index(cpu_id, pcid).locked_by_thread(lctx.thread_id())]
            index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) ==> !self.pcid_needflush.spec_index(cpu_id, pcid).locked_by_thread(lctx.thread_id())
        &&& forall|cpu_i: CpuId|
            #![trigger self.cpu_arr.spec_index(cpu_i).view().locked_by_thread(lctx.thread_id()), index_valid(NUM_CPUS, cpu_i)]
            index_valid(NUM_CPUS, cpu_i) ==> self.cpu_arr.spec_index(cpu_i).view().locked_by_thread(lctx.thread_id()) == false
        &&& forall|p_i: PageIndex|
            #![trigger self.pg_arr.spec_index(p_i), index_valid(NUM_PAGES, p_i)]
            index_valid(NUM_PAGES, p_i) ==> self.pg_arr.spec_index(p_i).view().locked_by_thread(lctx.thread_id()) == false
        &&& forall|c_ptr: RwLockContainerPtr|
            #![trigger self.ctn_mp.dom().contains(c_ptr)]
            self.ctn_mp.dom().contains(c_ptr) ==> self.ctn_mp.spec_index(c_ptr).locked_by_thread(lctx.thread_id()) == false
        &&& forall|p_ptr: RwLockProcessPtr|
            #![trigger self.prc_mp.dom().contains(p_ptr)]
            self.prc_mp.dom().contains(p_ptr) ==> self.prc_mp.spec_index(p_ptr).locked_by_thread(lctx.thread_id()) == false
        &&& forall|t_ptr: RwLockThreadPtr|
            #![trigger self.thr_mp.spec_index(t_ptr)]
            self.thr_mp.dom().contains(t_ptr) ==> self.thr_mp.spec_index(t_ptr).locked_by_thread(lctx.thread_id()) == false
        &&& forall|e_ptr: RwLockEndpointPtr|
            #![trigger self.ep_mp.spec_index(e_ptr)]
            self.ep_mp.dom().contains(e_ptr) ==> self.ep_mp.spec_index(e_ptr).locked_by_thread(lctx.thread_id()) == false
        &&& forall|pt_ptr: RwLockPageTableRoot|
            #![trigger self.pt_mp.spec_index(pt_ptr).locked_by_thread(lctx.thread_id())]
            self.pt_mp.dom().contains(pt_ptr) ==> self.pt_mp.spec_index(pt_ptr).locked_by_thread(lctx.thread_id()) == false
        &&& forall|iommu_root: RwLockPageTableRoot|
            #![trigger self.it_mp.spec_index(iommu_root).locked_by_thread(lctx.thread_id())]
            self.it_mp.dom().contains(iommu_root) ==> self.it_mp.spec_index(iommu_root).locked_by_thread(lctx.thread_id()) == false
        &&& forall|s_ptr: RwLockSchedulerPtr|
            #![trigger self.sched_mp.spec_index(s_ptr).locked_by_thread(lctx.thread_id())]
            self.sched_mp.dom().contains(s_ptr) ==> self.sched_mp.spec_index(s_ptr).locked_by_thread(lctx.thread_id()) == false
        &&& forall|cpu_set_ptr: RwLockCpuSetPtr|
            #![trigger self.cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(lctx.thread_id())]
            self.cpu_set_mp.dom().contains(cpu_set_ptr) ==> self.cpu_set_mp.spec_index(cpu_set_ptr).locked_by_thread(lctx.thread_id()) == false
        &&& forall|allocator_ptr: RwLockPcidAllocatorPtr|
            #![trigger self.pcid_allc_mp.spec_index(allocator_ptr).locked_by_thread(lctx.thread_id())]
            self.pcid_allc_mp.dom().contains(allocator_ptr) ==> self.pcid_allc_mp.spec_index(allocator_ptr).locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allc_4k_mp.spec_index(alloc_ptr).global_pool]
            self.allc_4k_mp.dom().contains(alloc_ptr) ==> self.allc_4k_mp.spec_index(alloc_ptr).global_pool.locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allc_4k_mp.spec_index(alloc_ptr).quota]
            self.allc_4k_mp.dom().contains(alloc_ptr) ==> self.allc_4k_mp.spec_index(alloc_ptr).quota.locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId|
            #![trigger self.allc_4k_mp.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i), index_valid(NUM_CPUS, cpu_i)]
            self.allc_4k_mp.dom().contains(alloc_ptr) && index_valid(NUM_CPUS, cpu_i) ==> self.allc_4k_mp.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allc_2m_mp.spec_index(alloc_ptr).global_pool]
            self.allc_2m_mp.dom().contains(alloc_ptr) ==> self.allc_2m_mp.spec_index(alloc_ptr).global_pool.locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allc_2m_mp.spec_index(alloc_ptr).quota]
            self.allc_2m_mp.dom().contains(alloc_ptr) ==> self.allc_2m_mp.spec_index(alloc_ptr).quota.locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId|
            #![trigger self.allc_2m_mp.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i), index_valid(NUM_CPUS, cpu_i)]
            self.allc_2m_mp.dom().contains(alloc_ptr) && index_valid(NUM_CPUS, cpu_i) ==> self.allc_2m_mp.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allc_1g_mp.spec_index(alloc_ptr).global_pool]
            self.allc_1g_mp.dom().contains(alloc_ptr) ==> self.allc_1g_mp.spec_index(alloc_ptr).global_pool.locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allc_1g_mp.spec_index(alloc_ptr).quota]
            self.allc_1g_mp.dom().contains(alloc_ptr) ==> self.allc_1g_mp.spec_index(alloc_ptr).quota.locked_by_thread(lctx.thread_id()) == false
        &&& forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId|
            #![trigger self.allc_1g_mp.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i), index_valid(NUM_CPUS, cpu_i)]
            self.allc_1g_mp.dom().contains(alloc_ptr) && index_valid(NUM_CPUS, cpu_i) ==> self.allc_1g_mp.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by_thread(lctx.thread_id()) == false
    }
}

}
