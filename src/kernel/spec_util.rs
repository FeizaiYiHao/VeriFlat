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
        self.container_map.spec_index(container_ptr).view().quota_4k.view()
    }
}

}