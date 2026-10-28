use vstd::prelude::*;
use crate::*;

verus! {
#[verifier::opaque]
pub open spec fn pcid_needflush_wf(array: PcidNeedFlushArray) -> bool {
    forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger array.spec_index(cpu_id, pcid)]
        index_valid(NUM_CPUS, cpu_id) && pcid_valid(pcid) ==> {
            let entry = array.spec_index(cpu_id, pcid);
            &&& entry.inv()
            &&& entry.view().index() == (cpu_id, pcid)
            &&& entry.wlocked() == (entry.view_ghost() is Some)
            &&& (entry.view_ghost() is Some ==> index_valid(NUM_CPUS, entry.view_ghost().unwrap()))
        }
}

/// Entry `(cpu_id, pcid)` is well formed, pinned to its slot, and write-held exactly when it names a valid holder cpu.
pub proof fn pcid_needflush_wf_at(array: PcidNeedFlushArray, cpu_id: CpuId, pcid: Pcid)
    requires
        pcid_needflush_wf(array),
        index_valid(NUM_CPUS, cpu_id),
        pcid_valid(pcid),
    ensures
        ({
            let entry = array.spec_index(cpu_id, pcid);
            &&& entry.inv()
            &&& entry.view().index() == (cpu_id, pcid)
            &&& entry.wlocked() == (entry.view_ghost() is Some)
            &&& (entry.view_ghost() is Some ==> index_valid(NUM_CPUS, entry.view_ghost().unwrap()))
        }),
{ reveal(pcid_needflush_wf); }

#[verifier::opaque]
pub open spec fn cpu_hw_cr3_pcid_wf(hw_cr3_pcid: CpuHwCr3PcidArray, cpus: CpuLockedArray, needflush: PcidNeedFlushArray) -> bool {
    forall|cpu_id: CpuId|
        #![trigger hw_cr3_pcid[cpu_id as int].view()]
        #![trigger hw_cr3_pcid[cpu_id as int].owner_cpu()]
        #![trigger cpus.spec_index(cpu_id).view().view().view()]
        index_valid(NUM_CPUS, cpu_id) ==> {
            let hardware = cpus.spec_index(cpu_id).view().view().view();
            let entry = needflush.spec_index(cpu_id, hardware.current_pcid);
            &&& hw_cr3_pcid[cpu_id as int].owner_cpu() == cpu_id
            &&& hw_cr3_pcid[cpu_id as int].inv()
            &&& page_ptr_valid(hardware.current_cr3)
            &&& pcid_valid(hardware.current_pcid)
            &&& (hw_cr3_pcid[cpu_id as int].view() != (hardware.current_cr3, hardware.current_pcid) ==> {
                &&& cpus.spec_index(cpu_id).view().wlocked()
                &&& entry.wlocked()
                &&& entry.view_ghost() == Some(cpu_id)
            })
        }
}

pub proof fn cpu_hw_cr3_pcid_wf_at(hw_cr3_pcid: CpuHwCr3PcidArray, cpus: CpuLockedArray, needflush: PcidNeedFlushArray, cpu_id: CpuId)
    requires
        cpu_hw_cr3_pcid_wf(hw_cr3_pcid, cpus, needflush),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        ({
            let hardware = cpus.spec_index(cpu_id).view().view().view();
            let entry = needflush.spec_index(cpu_id, hardware.current_pcid);
            &&& hw_cr3_pcid[cpu_id as int].owner_cpu() == cpu_id
            &&& hw_cr3_pcid[cpu_id as int].inv()
            &&& page_ptr_valid(hardware.current_cr3)
            &&& pcid_valid(hardware.current_pcid)
            &&& (hw_cr3_pcid[cpu_id as int].view() != (hardware.current_cr3, hardware.current_pcid) ==> {
                &&& cpus.spec_index(cpu_id).view().wlocked()
                &&& entry.wlocked()
                &&& entry.view_ghost() == Some(cpu_id)
            })
        }),
{ reveal(cpu_hw_cr3_pcid_wf); }
}
