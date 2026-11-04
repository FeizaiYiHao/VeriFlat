use vstd::prelude::*;
use crate::*;

verus! {
/// Each container owns exactly the offline request table in the second 4K of its 2M page, tagged with its depth.
#[verifier::opaque]
pub open spec fn container_cpu_offline_flags_wf(ctn_mp: ContainerLockedMap, cpu_offline_mp: CpuOfflineFlagsUnLockedMap) -> bool {
    // Container -> offline flags.
    &&& forall|c: RwLockContainerPtr|
        #![trigger ctn_mp.dom().contains(c)]
        ctn_mp.dom().contains(c) ==> {
            &&& cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(c))
            &&& cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c)).owning_container.view() == c
            &&& cpu_offline_mp.spec_index(cpu_offline_flags_ptr(c)).container_depth.view() == ctn_mp.spec_index(c).view_rodata().view().depth
        }
    // Offline flags -> container.
    &&& forall|flags_ptr: RwLockCpuOfflineFlagsPtr|
        #![trigger cpu_offline_mp.dom().contains(flags_ptr)]
        cpu_offline_mp.dom().contains(flags_ptr) ==> {
            let ctn_ptr = cpu_offline_mp.spec_index(flags_ptr).owning_container.view();
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& cpu_offline_flags_ptr(ctn_ptr) == flags_ptr
        }
}

pub proof fn container_cpu_offline_flags_wf_container_at(ctn_mp: ContainerLockedMap, cpu_offline_mp: CpuOfflineFlagsUnLockedMap, ctn_ptr: RwLockContainerPtr)
    requires
        container_cpu_offline_flags_wf(ctn_mp, cpu_offline_mp),
    ensures
        ctn_mp.dom().contains(ctn_ptr) ==> ({
            &&& cpu_offline_mp.dom().contains(cpu_offline_flags_ptr(ctn_ptr))
            &&& cpu_offline_mp.spec_index(cpu_offline_flags_ptr(ctn_ptr)).owning_container.view() == ctn_ptr
            &&& cpu_offline_mp.spec_index(cpu_offline_flags_ptr(ctn_ptr)).container_depth.view() == ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth
        }),
{ reveal(container_cpu_offline_flags_wf); }

pub proof fn container_cpu_offline_flags_wf_flags_at(ctn_mp: ContainerLockedMap, cpu_offline_mp: CpuOfflineFlagsUnLockedMap, flags_ptr: RwLockCpuOfflineFlagsPtr)
    requires
        container_cpu_offline_flags_wf(ctn_mp, cpu_offline_mp),
    ensures
        cpu_offline_mp.dom().contains(flags_ptr) ==> ({
            let ctn_ptr = cpu_offline_mp.spec_index(flags_ptr).owning_container.view();
            &&& ctn_mp.dom().contains(ctn_ptr)
            &&& cpu_offline_flags_ptr(ctn_ptr) == flags_ptr
        }),
{ reveal(container_cpu_offline_flags_wf); }
}
