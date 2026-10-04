use vstd::prelude::*;
use crate::*;

verus! {
/// Every offline request table is well formed, each cell is pinned to its slot, and a pending
/// request names a non-Off cpu that the table's container currently owns.
#[verifier::opaque]
pub open spec fn cpu_offline_flags_wf(flags_map: CpuOfflineFlagsUnLockedMap, cpu_array: CpuLockedArray) -> bool {
    &&& flags_map.perms_wf()
    &&& forall|flags_ptr: RwLockCpuOfflineFlagsPtr| #![trigger flags_map.spec_index(flags_ptr)] flags_map.dom().contains(flags_ptr) ==> flags_map.spec_index(flags_ptr).inv()
    &&& forall|flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId|
        #![trigger flags_map.spec_index(flags_ptr).flags.spec_index(cpu_id)]
        flags_map.dom().contains(flags_ptr) && index_valid(NUM_CPUS, cpu_id) ==> {
            let cell = flags_map.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view();
            let cpu = cpu_array.spec_index(cpu_id).view().view().view();
            &&& cell.index() == (flags_ptr, cpu_id)
            &&& cell.requested ==> cpu.owning_container == flags_map.spec_index(flags_ptr).owning_container.view() && !(cpu.state is Off)
        }
}
}
