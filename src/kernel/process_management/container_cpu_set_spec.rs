use vstd::prelude::*;
use crate::*;

verus! {
/// Each container owns exactly its cpu set, tagged with its depth.
#[verifier::opaque]
pub open spec fn container_cpu_set_wf(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap) -> bool {
    // Container -> CPU set.
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c) ==> {
            let cpu_set_ptr = ctn_mp.spec_index(c).view_rodata().view().cpu_set;
            &&& cpu_set_mp.dom().contains(cpu_set_ptr)
            &&& cpu_set_mp.spec_index(cpu_set_ptr).view().owning_container.view() == c
            &&& cpu_set_mp.spec_index(cpu_set_ptr).view().container_depth.view() == ctn_mp.spec_index(c).view_rodata().view().depth
        }
    // CPU set -> container.
    &&& forall|cpu_set_ptr: RwLockCpuSetPtr|
        #![trigger cpu_set_mp.dom().contains(cpu_set_ptr)]
        cpu_set_mp.dom().contains(cpu_set_ptr) ==> {
            let ctn_ptr = cpu_set_mp.spec_index(cpu_set_ptr).view().owning_container.view();
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
        }
}

pub proof fn container_cpu_set_wf_container_at(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_cpu_set_wf(ctn_mp, cpu_set_mp),
    ensures
        ctn_mp.dom().contains(ctn_ptr) ==> ({
            let cpu_set_ptr = ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set;
            &&& cpu_set_mp.dom().contains(cpu_set_ptr)
            &&& cpu_set_mp.spec_index(cpu_set_ptr).view().owning_container.view() == ctn_ptr
            &&& cpu_set_mp.spec_index(cpu_set_ptr).view().container_depth.view() == ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth
        }),
{ reveal(container_cpu_set_wf); }

pub proof fn container_cpu_set_wf_cpu_set_at(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        container_cpu_set_wf(ctn_mp, cpu_set_mp),
    ensures
        cpu_set_mp.dom().contains(cpu_set_ptr) ==> ({
            let ctn_ptr = cpu_set_mp.spec_index(cpu_set_ptr).view().owning_container.view();
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set == cpu_set_ptr
        }),
{ reveal(container_cpu_set_wf); }
}
