use vstd::prelude::*;
use crate::*;

verus! {

    pub const KERNEL_DEFAULT_PCID:Pcid = 0; 
    pub struct Kernel{
        pub pagetable_dom: PageTableDom,
        pub page_array: PageArray,
        pub cpu_array: CpuArray,

        pub container_map: LockedMap<RwLockContainerPtr, Container, CONTAINER_HAS_KILL_STATE>,
        pub scheduler_map: LockedMap<RwLockSchedulerPtr, Scheduler, CONTAINER_HAS_KILL_STATE>,
        pub process_map: LockedMap<RwLockProcessPtr, Process, PROCESS_HAS_KILL_STATE>,
        pub thread_map: LockedMap<RwLockThreadPtr, Process, THREAD_HAS_KILL_STATE>,
        pub endpoint_map: LockedMap<RwLockEndpointPtr, Endpoint, ENDPOINT_HAS_KILL_STATE>,


        pub default_pagetable: RwLock<PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>,
    }

    impl Kernel{
        pub open spec fn subsystems_inv(&self) -> bool {
            &&&
            self.default_pagetable_wf()
            &&&
            self.page_array.inv()
            &&&
            self.pagetable_dom.inv()
            &&&
            self.cpu_array.inv()
        }

        pub open spec fn inv(&self) -> bool {
            &&&
            self.subsystems_inv()
            &&&
            self.kernel_page_array_pagetable_dom_inv()
            &&&
            self.kernel_tlb_inv()
        }

        pub open spec fn default_pagetable_wf(&self) -> bool {
            &&&
            self.default_pagetable.inv()
            &&&
            self.default_pagetable@.pcid_or_ioid() == KERNEL_DEFAULT_PCID
        }
    }

}