use vstd::prelude::*;
use crate::*;

verus! {
/// Each container owns exactly the offline request table in the second 4K of its 2M page.
#[verifier::opaque]
pub open spec fn container_cpu_offline_flags_wf(container_map: ContainerLockedMap, flags_map: CpuOfflineFlagsUnLockedMap) -> bool {
    &&& forall|c_ptr: RwLockContainerPtr| #![trigger container_map.dom().contains(c_ptr)] container_map.dom().contains(c_ptr) ==> {
        &&& flags_map.dom().contains(cpu_offline_flags_ptr(c_ptr))
        &&& flags_map.spec_index(cpu_offline_flags_ptr(c_ptr)).owning_container.view() == c_ptr
    }
    &&& forall|flags_ptr: RwLockCpuOfflineFlagsPtr| #![trigger flags_map.dom().contains(flags_ptr)] flags_map.dom().contains(flags_ptr) ==> {
        let c_ptr = flags_map.spec_index(flags_ptr).owning_container.view();
        &&& container_map.dom().contains(c_ptr)
        &&& cpu_offline_flags_ptr(c_ptr) == flags_ptr
    }
}

pub proof fn container_cpu_offline_flags_wf_container_at(container_map: ContainerLockedMap, flags_map: CpuOfflineFlagsUnLockedMap, c_ptr: RwLockContainerPtr)
    requires
        container_cpu_offline_flags_wf(container_map, flags_map),
    ensures
        container_map.dom().contains(c_ptr) ==> ({
            &&& flags_map.dom().contains(cpu_offline_flags_ptr(c_ptr))
            &&& flags_map.spec_index(cpu_offline_flags_ptr(c_ptr)).owning_container.view() == c_ptr
        }),
{ reveal(container_cpu_offline_flags_wf); }

pub proof fn container_cpu_offline_flags_wf_flags_at(container_map: ContainerLockedMap, flags_map: CpuOfflineFlagsUnLockedMap, flags_ptr: RwLockCpuOfflineFlagsPtr)
    requires
        container_cpu_offline_flags_wf(container_map, flags_map),
    ensures
        flags_map.dom().contains(flags_ptr) ==> ({
            let c_ptr = flags_map.spec_index(flags_ptr).owning_container.view();
            &&& container_map.dom().contains(c_ptr)
            &&& cpu_offline_flags_ptr(c_ptr) == flags_ptr
        }),
{ reveal(container_cpu_offline_flags_wf); }
}
