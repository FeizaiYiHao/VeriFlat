use vstd::prelude::*;
use crate::*;
verus! {
/// Every cpu lock is well formed, and a cpu without a current page table runs the kernel cr3 with the kernel PCID.
#[verifier::opaque]
pub open spec fn cpu_array_wf(cpu_arr: CpuLockedArray, dflt_pt: PageTable<PT_TYPE>) -> bool {
    &&& cpu_arr.inv()
    &&& forall|cpu_id: CpuId|
        #![trigger cpu_arr.spec_index(cpu_id)]
        index_valid(NUM_CPUS, cpu_id) ==> {
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            &&& cpu_arr.spec_index(cpu_id).view().inv()
            &&& cpu.current_pagetable is None ==> cpu.current_cr3 == dflt_pt.cr3 && cpu.current_pcid == KERNEL_DEFAULT_PCID
        }
}

/// Cpu `cpu_id`'s lock is well formed, and without a current page table the cpu runs the kernel cr3 with the kernel PCID.
pub proof fn cpu_array_wf_at(cpu_arr: CpuLockedArray, dflt_pt: PageTable<PT_TYPE>, cpu_id: CpuId)
    requires
        cpu_array_wf(cpu_arr, dflt_pt),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        ({
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            &&& cpu_arr.spec_index(cpu_id).view().inv()
            &&& cpu.current_pagetable is None ==> cpu.current_cr3 == dflt_pt.cr3 && cpu.current_pcid == KERNEL_DEFAULT_PCID
        }),
{ reveal(cpu_array_wf); }

pub proof fn cpu_array_wf_implies_array_inv(cpu_arr: CpuLockedArray, dflt_pt: PageTable<PT_TYPE>)
    requires cpu_array_wf(cpu_arr, dflt_pt)
    ensures cpu_arr.inv()
{ reveal(cpu_array_wf); }

/// Point fact at one cpu: when cpu `cpu_id` runs `pcid` and its dirty bitmap maps `pcid` to `pt_ptr`, it runs that page
/// table's process with the table's cr3.
pub proof fn cpu_current_pcid_pagetable_match_at(cpu_arr: CpuLockedArray, dflt_pt: PageTable<PT_TYPE>, prc_mp: ProcessLockedMap,
    pt_mp: PageTableLockedMap, cpu_id: CpuId, pcid: Pcid, pt_ptr: RwLockPageTableRoot)
    requires
        cpu_array_wf(cpu_arr, dflt_pt),
        process_cpu_wf(prc_mp, cpu_arr),
        process_pagetable_wf(prc_mp, pt_mp),
        index_valid(NUM_CPUS, cpu_id),
        pcid != KERNEL_DEFAULT_PCID,
    ensures
        cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid
            && cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap().pagetable_ptr == pt_ptr
            ==>
            cpu_arr.spec_index(cpu_id).view().view().view().current_process == Some(pt_mp.spec_index(pt_ptr).view().proc_ptr)
            && cpu_arr.spec_index(cpu_id).view().view().view().current_cr3 == pt_mp.spec_index(pt_ptr).view().cr3,
{ reveal(cpu_array_wf); reveal(process_cpu_wf); reveal(process_pagetable_wf); }

/// Each cpu owns its hardware cr3/pcid word, which equals the cpu's recorded (current_cr3, current_pcid) except while
/// the cpu and that PCID's needflush entry are write-held by the cpu itself.
#[verifier::opaque]
pub open spec fn cpu_hw_cr3_pcid_wf(cpu_hw_cr3_pcid: CpuHwCr3PcidArray, cpu_arr: CpuLockedArray, pcid_needflush: PcidNeedFlushArray) -> bool {
    forall|cpu_id: CpuId|
        #![trigger cpu_hw_cr3_pcid[cpu_id as int].view()]
        #![trigger cpu_hw_cr3_pcid[cpu_id as int].owner_cpu()]
        #![trigger cpu_arr.spec_index(cpu_id).view().view().view()]
        index_valid(NUM_CPUS, cpu_id) ==> {
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            let entry = pcid_needflush.spec_index(cpu_id, cpu.current_pcid);
            &&& cpu_hw_cr3_pcid[cpu_id as int].owner_cpu() == cpu_id
            &&& cpu_hw_cr3_pcid[cpu_id as int].inv()
            &&& page_ptr_valid(cpu.current_cr3)
            &&& pcid_valid(cpu.current_pcid)
            &&& (cpu_hw_cr3_pcid[cpu_id as int].view() != (cpu.current_cr3, cpu.current_pcid) ==> {
                &&& cpu_arr.spec_index(cpu_id).view().wlocked()
                &&& entry.wlocked()
                &&& entry.view_ghost() == Some(cpu_id)
            })
        }
}

pub proof fn cpu_hw_cr3_pcid_wf_at(cpu_hw_cr3_pcid: CpuHwCr3PcidArray, cpu_arr: CpuLockedArray, pcid_needflush: PcidNeedFlushArray, cpu_id: CpuId)
    requires
        cpu_hw_cr3_pcid_wf(cpu_hw_cr3_pcid, cpu_arr, pcid_needflush),
        index_valid(NUM_CPUS, cpu_id),
    ensures
        ({
            let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
            let entry = pcid_needflush.spec_index(cpu_id, cpu.current_pcid);
            &&& cpu_hw_cr3_pcid[cpu_id as int].owner_cpu() == cpu_id
            &&& cpu_hw_cr3_pcid[cpu_id as int].inv()
            &&& page_ptr_valid(cpu.current_cr3)
            &&& pcid_valid(cpu.current_pcid)
            &&& (cpu_hw_cr3_pcid[cpu_id as int].view() != (cpu.current_cr3, cpu.current_pcid) ==> {
                &&& cpu_arr.spec_index(cpu_id).view().wlocked()
                &&& entry.wlocked()
                &&& entry.view_ghost() == Some(cpu_id)
            })
        }),
{ reveal(cpu_hw_cr3_pcid_wf); }
}
