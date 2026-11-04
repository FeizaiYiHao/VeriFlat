use vstd::prelude::*;
use crate::*;

verus! {
/// Every offline request table is well formed, each cell is pinned to its slot, and a pending
/// request names a non-Off cpu that the table's container currently owns.
#[verifier::opaque]
pub open spec fn cpu_offline_flags_wf(cpu_offline_mp: CpuOfflineFlagsUnLockedMap, cpu_arr: CpuLockedArray) -> bool {
    &&& cpu_offline_mp.perms_wf()
    &&& forall|flags_ptr: RwLockCpuOfflineFlagsPtr|
        #![trigger cpu_offline_mp.spec_index(flags_ptr)]
        cpu_offline_mp.dom().contains(flags_ptr) ==> cpu_offline_mp.spec_index(flags_ptr).inv()
    &&& forall|flags_ptr: RwLockCpuOfflineFlagsPtr, cpu_id: CpuId|
        #![trigger cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id)]
        cpu_offline_mp.dom().contains(flags_ptr) && index_valid(NUM_CPUS, cpu_id) ==> {
            let cell = cpu_offline_mp.spec_index(flags_ptr).flags.spec_index(cpu_id).view().view();
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            &&& cell.index() == (flags_ptr, cpu_id)
            &&& cell.requested ==> cpu.owning_container == cpu_offline_mp.spec_index(flags_ptr).owning_container.view() && !(cpu.state is Off)
        }
}

pub proof fn cpu_offline_flags_wf_implies_perms_wf(cpu_offline_mp: CpuOfflineFlagsUnLockedMap, cpu_arr: CpuLockedArray)
    requires cpu_offline_flags_wf(cpu_offline_mp, cpu_arr)
    ensures cpu_offline_mp.perms_wf()
{ reveal(cpu_offline_flags_wf); }

/// Table `flags_ptr` is well formed.
pub proof fn cpu_offline_flags_wf_at(cpu_offline_mp: CpuOfflineFlagsUnLockedMap, cpu_arr: CpuLockedArray, flags_ptr: RwLockCpuOfflineFlagsPtr)
    requires
        cpu_offline_flags_wf(cpu_offline_mp, cpu_arr),
        cpu_offline_mp.dom().contains(flags_ptr),
    ensures cpu_offline_mp.spec_index(flags_ptr).inv()
{ reveal(cpu_offline_flags_wf); }
}
