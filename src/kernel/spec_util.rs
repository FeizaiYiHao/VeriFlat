use vstd::prelude::*;
use crate::*;
use super::*;
verus! {

// ============================================================
//   Per-type "objects unlocked" pieces
// ============================================================
//
// `all_objects_unlocked` is split into one opaque predicate per object
// kind. Keeping each piece opaque means the (large) `all_objects_unlocked`
// precondition only seeds the proof context with opaque calls, not ~18
// quantifiers — callers reveal just the pieces they actually touch.

#[verifier::opaque]
pub open spec fn cpu_objects_unlocked(cpu_array: LockedArray<Cpu, (), (), (), NUM_CPUS, CPU_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|cpu_i: CpuId|
        #![trigger cpu_array.spec_index(cpu_i).view().locked_by(lctx)]
        cpu_id_valid(cpu_i)
        ==>
        cpu_array.spec_index(cpu_i).view().locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn page_objects_unlocked(page_array: LockedArray<Page, (), (), (), NUM_PAGES, NO_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|p_i: PageIndex|
        #![trigger page_array.spec_index(p_i).view().locked_by(lctx)]
        page_index_valid(p_i)
        ==>
        page_array.spec_index(p_i).view().locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn container_objects_unlocked(container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, (), (), CONTAINER_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr)
        ==>
        container_map.spec_index(c_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn process_objects_unlocked(process_map: ProcessLockedMap, lctx: &LocalContext) -> bool {
    forall|p_ptr: RwLockProcessPtr|
        #![trigger process_map.dom().contains(p_ptr)]
        process_map.dom().contains(p_ptr)
        ==>
        process_map.spec_index(p_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn thread_objects_unlocked(thread_map: ThreadLockedMap, lctx: &LocalContext) -> bool {
    forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr).locked_by(lctx)]
        thread_map.dom().contains(t_ptr)
        ==>
        thread_map.spec_index(t_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn endpoint_objects_unlocked(endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (), (), (), ENDPOINT_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|e_ptr: RwLockEndpointPtr|
        #![trigger endpoint_map.spec_index(e_ptr).locked_by(lctx)]
        endpoint_map.dom().contains(e_ptr)
        ==>
        endpoint_map.spec_index(e_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn pagetable_objects_unlocked(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), (), (), PAGE_TABLE_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|pt_ptr: RwLockPageTableRoot|
        #![trigger pagetable_map.spec_index(pt_ptr).locked_by(lctx)]
        pagetable_map.dom().contains(pt_ptr)
        ==>
        pagetable_map.spec_index(pt_ptr).locked_by(lctx) == false
}

#[verifier::opaque]
pub open spec fn scheduler_objects_unlocked(scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), (), (), SCHEDULER_HAS_KILL_STATE>, lctx: &LocalContext) -> bool {
    forall|s_ptr: RwLockSchedulerPtr|
        #![trigger scheduler_map.spec_index(s_ptr).locked_by(lctx)]
        scheduler_map.dom().contains(s_ptr)
        ==>
        scheduler_map.spec_index(s_ptr).locked_by(lctx) == false
}

/// Reusable across the 4k / 2m / 1g allocator maps: quota, global poll, and
/// every cpu cache of every allocator is unlocked.
#[verifier::opaque]
pub open spec fn allocator_objects_unlocked(alloc_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>, lctx: &LocalContext) -> bool {
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr|
        #![trigger alloc_map.spec_index(alloc_ptr).global_poll.locked_by(lctx)]
        alloc_map.dom().contains(alloc_ptr)
        ==>
        alloc_map.spec_index(alloc_ptr).global_poll.locked_by(lctx) == false
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr|
        #![trigger alloc_map.spec_index(alloc_ptr).quota.locked_by(lctx)]
        alloc_map.dom().contains(alloc_ptr)
        ==>
        alloc_map.spec_index(alloc_ptr).quota.locked_by(lctx) == false
    &&&
    forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId|
        #![trigger alloc_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx)]
        alloc_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
        ==>
        alloc_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx) == false
}

impl KernelK{
    /// Everything is unlocked EXCEPT the cpu at `cpu_id`, the container at
    /// `container_ptr`, and the 4k allocator quota at `alloc_ptr_4k`. Used as
    /// a precondition for the exit-path helper so it can derive
    /// `all_objects_unlocked` after the 3 wunlocks.
    pub open spec fn all_objects_unlocked_except_3(
        &self,
        lctx: &LocalContext,
        cpu_id: CpuId,
        container_ptr: RwLockContainerPtr,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
    ) -> bool {
        // Pages: all unlocked
        &&& page_objects_unlocked(self.page_array, lctx)
        // CPU: all except cpu_id
        &&& (forall|cpu_i: CpuId|
            #![trigger self.cpu_array.spec_index(cpu_i).view().locked_by(lctx)]
            cpu_id_valid(cpu_i) && cpu_i != cpu_id
            ==>
            self.cpu_array.spec_index(cpu_i).view().locked_by(lctx) == false)
        // Containers: all except container_ptr
        &&& (forall|c_ptr: RwLockContainerPtr|
            #![trigger self.container_map.dom().contains(c_ptr)]
            self.container_map.dom().contains(c_ptr) && c_ptr != container_ptr
            ==>
            self.container_map.spec_index(c_ptr).locked_by(lctx) == false)
        // Processes: all unlocked
        &&& process_objects_unlocked(self.process_map, lctx)
        // Threads: all unlocked
        &&& thread_objects_unlocked(self.thread_map, lctx)
        // Endpoints: all unlocked
        &&& endpoint_objects_unlocked(self.endpoint_map, lctx)
        // Pagetables: all unlocked
        &&& pagetable_objects_unlocked(self.pagetable_map, lctx)
        // Schedulers: all unlocked
        &&& scheduler_objects_unlocked(self.scheduler_map, lctx)
        // 4k allocators: quota unlocked for all except alloc_ptr_4k; global_poll + cpu_caches all unlocked
        &&& (forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allocator_4k_map.spec_index(alloc_ptr).quota.locked_by(lctx)]
            self.allocator_4k_map.dom().contains(alloc_ptr) && alloc_ptr != alloc_ptr_4k
            ==>
            self.allocator_4k_map.spec_index(alloc_ptr).quota.locked_by(lctx) == false)
        &&& (forall|alloc_ptr: RwLockPageAllocatorPtr|
            #![trigger self.allocator_4k_map.spec_index(alloc_ptr).global_poll.locked_by(lctx)]
            self.allocator_4k_map.dom().contains(alloc_ptr)
            ==>
            self.allocator_4k_map.spec_index(alloc_ptr).global_poll.locked_by(lctx) == false)
        &&& (forall|alloc_ptr: RwLockPageAllocatorPtr, cpu_i: CpuId|
            #![trigger self.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx)]
            self.allocator_4k_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)
            ==>
            self.allocator_4k_map.spec_index(alloc_ptr).cpu_caches.spec_index(cpu_i).view().locked_by(lctx) == false)
        // 2m allocators: all unlocked
        &&& allocator_objects_unlocked(self.allocator_2m_map, lctx)
        // 1g allocators: all unlocked
        &&& allocator_objects_unlocked(self.allocator_1g_map, lctx)
    }

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

    /// Open conjunction of the per-type opaque pieces. Reveal only the piece
    /// you need (e.g. `cpu_objects_unlocked` before a cpu `wlock`).
    pub open spec fn all_objects_unlocked(&self, lctx: &LocalContext) -> bool{
        &&& cpu_objects_unlocked(self.cpu_array, lctx)
        &&& page_objects_unlocked(self.page_array, lctx)
        &&& container_objects_unlocked(self.container_map, lctx)
        &&& process_objects_unlocked(self.process_map, lctx)
        &&& thread_objects_unlocked(self.thread_map, lctx)
        &&& endpoint_objects_unlocked(self.endpoint_map, lctx)
        &&& pagetable_objects_unlocked(self.pagetable_map, lctx)
        &&& scheduler_objects_unlocked(self.scheduler_map, lctx)
        &&& allocator_objects_unlocked(self.allocator_4k_map, lctx)
        &&& allocator_objects_unlocked(self.allocator_2m_map, lctx)
        &&& allocator_objects_unlocked(self.allocator_1g_map, lctx)
    }
}

// NOTE: proof fns / lemmas do NOT belong here (this file is spec fns only).
// The set/thread-fold + staged-pages TCB axioms live in
//   lemma::lemma_t::kernel_fold_axioms;
// the kernel-state preservation lemmas live in
//   lemma::lemma_u::kernel_preservation.

}
