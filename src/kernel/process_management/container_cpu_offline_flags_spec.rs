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
}
