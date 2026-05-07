use cpu_tlb_management::cpu_array_wf;
use vstd::prelude::*;
use crate::*;
use vstd::simple_pptr::*;

verus! {

    pub const KERNEL_DEFAULT_PCID:Pcid = 0; 
    pub struct Kernel{
        pub pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, (), PAGE_TABLE_HAS_KILL_STATE>,
        pub page_array: LockedArray<Page, (), NUM_PAGES, NO_KILL_STATE>,
        pub cpu_array: LockedArray<Cpu, (), NUM_CPUS, CPU_HAS_KILL_STATE>,
        pub cpu_tlb: CpuTLB,

        pub root_container: RwLockContainerPtr, // Never dies
        pub container_map: LockedMap<RwLockContainerPtr, Container, ReadOnlyNode<ContainerRO>, CONTAINER_HAS_KILL_STATE>,        
        pub number_containers: RwLock<NumContainers, (), NO_KILL_STATE>,
        pub scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, (), SCHEDULER_HAS_KILL_STATE>,
        pub process_map: LockedMap<RwLockProcessPtr, Process, ReadOnlyNode<ProcessRO>, PROCESS_HAS_KILL_STATE>,
        pub thread_map: LockedMap<RwLockThreadPtr, Thread, (), THREAD_HAS_KILL_STATE>,
        pub endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, (),  ENDPOINT_HAS_KILL_STATE>,
        pub allocator_4k_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        pub allocator_2m_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,
        pub allocator_1g_map: UnLockedMap<RwLockPageAllocatorPtr, PageAllocator>,

        // pub container_to_pagetable_map: Ghost<Map<RwLockContainerPtr, Set<RwLockPageTableRoot>>>,

        pub default_pagetable: PageTable<PT_TYPE>, // Read only
    }

    impl Kernel{
        /// all spec functions under this are open
        pub open spec fn subsystems_inv(&self) -> bool {
            &&&
            self.default_pagetable_wf()
            &&&
            pagetable_perms_wf(self.pagetable_map)
            &&&
            page_array_wf(self.page_array)
            &&&
            cpu_array_wf(self.cpu_array, self.default_pagetable)
            &&&
            self.cpu_tlb.inv()
            &&&
            container_perms_wf(self.container_map)
            &&&
            process_perms_wf(self.process_map)
            &&&
            allocator_perms_wf(self.allocator_4k_map)
            &&&
            allocator_perms_wf(self.allocator_2m_map)
            &&&
            allocator_perms_wf(self.allocator_1g_map)
        }

        /// All spec functions under this are closed
        pub open spec fn inv(&self) -> bool {
            &&&
            self.subsystems_inv()

            // Memory spec
            &&&
            page_pagetable_wf(self.pagetable_map, self.page_array)
            &&&
            container_tree_wf(self.root_container, self.container_map)
            &&&
            self.number_containers_wf()
            &&&
            self.container_pages_wf()
            &&&
            self.process_pages_wf()            
            &&&
            self.allocator_pages_wf()
            &&&
            thread_pages_wf(self.thread_map, self.page_array)
            &&&
            endpoint_pages_wf(self.endpoint_map, self.page_array)
            &&&
            pagetable_pages_wf_inner(self.pagetable_map, self.page_array)
            &&&
            self.allocator_free_pages_wf()
            &&&
            hugepage_2m_wf(self.page_array)
            &&&
            hugepage_1g_wf(self.page_array)

            // Process management spec

            &&&
            container_process_wf(self.container_map, self.process_map)
            &&&
            per_container_process_tree_wf(self.container_map, self.process_map)
            &&&
            container_cpu_wf(self.container_map, self.cpu_array)
            &&&
            process_cpu_wf(self.process_map, self.cpu_array)
            &&&
            process_pagetable_match(self.process_map, self.pagetable_map)
            &&&
            process_thread_wf_inner(self.process_map, self.thread_map)

            // TLB spec
            &&&
            cpu_dirty_map_wf(self.container_map, self.process_map, self.cpu_array, self.cpu_tlb, self.pagetable_map)
            &&&
            tlb_wf_spec(self.cpu_tlb, self.pagetable_map, self.cpu_array)
        }

        pub open spec fn number_containers_wf(&self) -> bool {
            &&&
            self.number_containers.inv()
            &&&
            self.container_map.dom().len() == self.number_containers.view().view()
            &&&
            self.number_containers.view().view() <= MAX_NUM_CONTAINERS
        }

        pub open spec fn default_pagetable_wf(&self) -> bool {
            &&&
            self.default_pagetable.inv()
            &&&
            self.default_pagetable.pcid_or_ioid() == KERNEL_DEFAULT_PCID
            &&&
            self.default_pagetable.is_empty()
        }

        pub open spec fn allocator_free_pages_wf(&self) -> bool{
            &&&
            allocator_free_page_ptrs_wf(self.allocator_4k_map)
            &&&
            allocator_free_page_ptrs_wf(self.allocator_2m_map)
            &&&
            allocator_free_page_ptrs_wf(self.allocator_1g_map)
        }
    }

}