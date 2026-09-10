use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn container_cpu_set_wf(
    container_map: ContainerLockedMap,
    cpu_set_map: CpuSetLockedMap,
) -> bool {
    // Container -> CPU set.
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger container_map.dom().contains(c_ptr)]
        container_map.dom().contains(c_ptr)
        ==>
        {
            let cpu_set_ptr = container_map.spec_index(c_ptr).view_rodata().view().cpu_set;
            &&& cpu_set_map.dom().contains(cpu_set_ptr)
            &&& cpu_set_map.spec_index(cpu_set_ptr).view().owning_container.view() == c_ptr
            &&& cpu_set_map.spec_index(cpu_set_ptr).view().container_depth.view() == container_map.spec_index(c_ptr).view_rodata().view().depth
        }
    // CPU set -> container.
    &&& forall|cpu_set_ptr: RwLockCpuSetPtr|
        #![trigger cpu_set_map.dom().contains(cpu_set_ptr)]
        cpu_set_map.dom().contains(cpu_set_ptr)
        ==>
        {
            let c_ptr = cpu_set_map.spec_index(cpu_set_ptr).view().owning_container.view();
            &&& container_map.dom().contains(c_ptr)
            &&& container_map.spec_index(c_ptr).view_rodata().view().cpu_set == cpu_set_ptr
        }
}
}
