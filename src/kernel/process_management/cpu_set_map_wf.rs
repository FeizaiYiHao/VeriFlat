use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn cpu_set_perms_wf(
    cpu_set_map: CpuSetLockedMap,
) -> bool {
    &&& cpu_set_map.perms_wf()
    &&& forall|cpu_set_ptr: RwLockCpuSetPtr|
        #![trigger cpu_set_map.dom().contains(cpu_set_ptr)]
        cpu_set_map.dom().contains(cpu_set_ptr)
        ==> cpu_set_map.spec_index(cpu_set_ptr).inv()
}
}
