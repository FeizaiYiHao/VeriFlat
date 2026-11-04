use vstd::prelude::*;
use crate::*;

verus! {
/// A cpu's current process is live, and the cpu mirrors its page table, pcid, cr3, depth, and container.
#[verifier::opaque]
pub open spec fn process_cpu_wf(prc_mp: ProcessLockedMap, cpu_arr: CpuLockedArray) -> bool {
    &&& forall|cpu_id: CpuId|
        #![trigger cpu_arr.spec_index(cpu_id).view().view().view().current_process]
        #![trigger cpu_arr.spec_index(cpu_id).view().view().view().current_pagetable]
        index_valid(NUM_CPUS, cpu_id) && cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some ==> {
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            let prc_ptr = cpu.current_process.unwrap();
            let slot = cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(cpu.current_pcid);
            &&& prc_mp.dom().contains(prc_ptr)
            &&& !prc_mp.spec_index(prc_ptr).view().zombie
            &&& cpu.current_pagetable == Some(prc_mp.spec_index(prc_ptr).view().pagetable)
            &&& cpu.current_pcid == prc_mp.spec_index(prc_ptr).view().pcid
            &&& cpu.current_cr3 == prc_mp.spec_index(prc_ptr).view_rodata().view().cr3
            &&& cpu.process_depth == prc_mp.spec_index(prc_ptr).view_rodata().view().depth
            &&& cpu.owning_container == prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container
            // the current pcid's TLB slot names this process and page table
            &&& slot is Some
            &&& slot.unwrap().process_ptr == prc_ptr
            &&& Some(slot.unwrap().pagetable_ptr) == cpu.current_pagetable
        }
}

pub proof fn process_cpu_wf_at(prc_mp: ProcessLockedMap, cpu_arr: CpuLockedArray, cpu_id: CpuId)
    requires
        process_cpu_wf(prc_mp, cpu_arr),
    ensures
        index_valid(NUM_CPUS, cpu_id) && cpu_arr.spec_index(cpu_id).view().view().view().current_process is Some ==> ({
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            let prc_ptr = cpu.current_process.unwrap();
            let slot = cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(cpu.current_pcid);
            &&& prc_mp.dom().contains(prc_ptr)
            &&& !prc_mp.spec_index(prc_ptr).view().zombie
            &&& cpu.current_pagetable == Some(prc_mp.spec_index(prc_ptr).view().pagetable)
            &&& cpu.current_pcid == prc_mp.spec_index(prc_ptr).view().pcid
            &&& cpu.current_cr3 == prc_mp.spec_index(prc_ptr).view_rodata().view().cr3
            &&& cpu.process_depth == prc_mp.spec_index(prc_ptr).view_rodata().view().depth
            &&& cpu.owning_container == prc_mp.spec_index(prc_ptr).view_rodata().view().owning_container
            &&& slot is Some
            &&& slot.unwrap().process_ptr == prc_ptr
            &&& Some(slot.unwrap().pagetable_ptr) == cpu.current_pagetable
        }),
{ reveal(process_cpu_wf); }
}
