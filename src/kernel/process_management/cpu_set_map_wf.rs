use vstd::prelude::*;
use crate::*;

verus! {
/// The cpu set map's permissions are well formed and every cpu set satisfies its own invariant.
#[verifier::opaque]
pub open spec fn cpu_set_perms_wf(cpu_set_mp: CpuSetLockedMap) -> bool {
    &&& cpu_set_mp.perms_wf()
    &&& forall|cpu_set_ptr: RwLockCpuSetPtr|
        #![trigger cpu_set_mp.dom().contains(cpu_set_ptr)]
        cpu_set_mp.dom().contains(cpu_set_ptr) ==> cpu_set_mp.spec_index(cpu_set_ptr).inv()
}

pub proof fn cpu_set_perms_wf_at(cpu_set_mp: CpuSetLockedMap, cpu_set_ptr: RwLockCpuSetPtr)
    requires
        cpu_set_perms_wf(cpu_set_mp),
    ensures
        cpu_set_mp.dom().contains(cpu_set_ptr) ==> cpu_set_mp.spec_index(cpu_set_ptr).inv(),
{ reveal(cpu_set_perms_wf); }

pub proof fn cpu_set_perms_wf_map(cpu_set_mp: CpuSetLockedMap)
    requires cpu_set_perms_wf(cpu_set_mp)
    ensures cpu_set_mp.perms_wf()
{ reveal(cpu_set_perms_wf); }
}
