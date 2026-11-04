use vstd::prelude::*;
use crate::*;
verus! {
/// The dirty bitmap of every cpu is consistent: each live dirty entry names a process of the cpu's container and that
/// process's page table, both carrying the entry's PCID, and every user PCID with a nonempty TLB or structure cache has
/// a dirty entry.
pub open spec fn cpu_dirty_map_wf(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, prc_mp: ProcessLockedMap, cpu_arr: CpuLockedArray,
    cpu_tlb: CpuTLB, pt_mp: PageTableLockedMap, pcid_needflush: PcidNeedFlushArray) -> bool
{
    &&& cpu_dirty_map_process_in_cpu_container(ctn_mp, cpu_set_mp, cpu_arr, pcid_needflush, cpu_tlb)
    &&& cpu_dirty_map_proc_pcid_match(prc_mp, cpu_arr, pcid_needflush, cpu_tlb)
    &&& cpu_dirty_map_covers_nonempty_tlb(cpu_arr, cpu_tlb)
    &&& cpu_dirty_map_pagetable_pcid_match(pt_mp, cpu_arr, pcid_needflush, cpu_tlb)
}

/// The process of every live dirty entry belongs to the cpu's container.
// Proof dependency: `container_cpu_wf`, which relates each cpu to its owning container.
#[verifier::opaque]
pub open spec fn cpu_dirty_map_process_in_cpu_container(ctn_mp: ContainerLockedMap, cpu_set_mp: CpuSetLockedMap, cpu_arr: CpuLockedArray,
    pcid_needflush: PcidNeedFlushArray, cpu_tlb: CpuTLB) -> bool
    recommends
        container_cpu_wf(ctn_mp, cpu_set_mp, cpu_arr),
{
    // Live dirty entry: `pcid` is current on the cpu, or its TLB or structure cache is nonempty with no flush pending.
    &&& forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid)]
        index_valid(NUM_CPUS, cpu_id)
            && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID
            && cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && ((!pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                && (!cpu_tlb.spec_index((cpu_id, pcid)).is_empty() || !cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()))
                || cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)
            ==> {
                let cpu = cpu_arr.spec_index(cpu_id).view().view().view();
                let dirty = cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap();
                &&& ctn_mp.spec_index(cpu.owning_container).view_ghost().owned_processes.contains(dirty.process_ptr)
            }
}

/// The page table of every live dirty entry is in the page-table map and carries the entry's PCID.
#[verifier::opaque]
pub open spec fn cpu_dirty_map_pagetable_pcid_match(pt_mp: PageTableLockedMap, cpu_arr: CpuLockedArray, pcid_needflush: PcidNeedFlushArray,
    cpu_tlb: CpuTLB) -> bool
{
    // Live dirty entry: `pcid` is current on the cpu, or its TLB or structure cache is nonempty with no flush pending.
    &&& forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid)]
        index_valid(NUM_CPUS, cpu_id)
            && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID
            && cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && ((!pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                && (!cpu_tlb.spec_index((cpu_id, pcid)).is_empty() || !cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()))
                || cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)
            ==> {
                let dirty = cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap();
                &&& pt_mp.dom().contains(dirty.pagetable_ptr)
                &&& pt_mp.spec_index(dirty.pagetable_ptr).view().pcid_value() == pcid
            }
}

/// Every user PCID whose TLB or structure cache on a cpu is nonempty has a dirty entry on that cpu.
#[verifier::opaque]
pub open spec fn cpu_dirty_map_covers_nonempty_tlb(cpu_arr: CpuLockedArray, cpu_tlb: CpuTLB) -> bool {
    &&& forall|cpu_id: CpuId, pcid: Pcid|
        #![auto]
        index_valid(NUM_CPUS, cpu_id)
            && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID
            && !cpu_tlb.spec_index((cpu_id, pcid)).is_empty()
            ==>
            cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
    &&& forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger cpu_tlb.structure_cache((cpu_id, pcid))]
        index_valid(NUM_CPUS, cpu_id)
            && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID
            && !cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()
            ==>
            cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
}

/// The process of every live dirty entry is in the process map, carries the entry's PCID, and owns the entry's page table.
#[verifier::opaque]
pub open spec fn cpu_dirty_map_proc_pcid_match(prc_mp: ProcessLockedMap, cpu_arr: CpuLockedArray, pcid_needflush: PcidNeedFlushArray,
    cpu_tlb: CpuTLB) -> bool
    recommends
        process_cpu_wf(prc_mp, cpu_arr)
{
    // Live dirty entry: `pcid` is current on the cpu, or its TLB or structure cache is nonempty with no flush pending.
    &&& forall|cpu_id: CpuId, pcid: Pcid|
        #![trigger cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid)]
        index_valid(NUM_CPUS, cpu_id)
            && pcid_valid(pcid)
            && pcid != KERNEL_DEFAULT_PCID
            && cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid) is Some
            && ((!pcid_needflush.spec_index(cpu_id, pcid).view().needflush
                && (!cpu_tlb.spec_index((cpu_id, pcid)).is_empty() || !cpu_tlb.structure_cache((cpu_id, pcid)).is_empty()))
                || cpu_arr.spec_index(cpu_id).view().view().view().current_pcid == pcid)
            ==> {
                let dirty = cpu_arr.spec_index(cpu_id).view().view().tlb_dirty_bitmap().spec_index(pcid).unwrap();
                &&& prc_mp.dom().contains(dirty.process_ptr)
                &&& prc_mp.spec_index(dirty.process_ptr).view().pcid == pcid
                &&& prc_mp.spec_index(dirty.process_ptr).view().pagetable == dirty.pagetable_ptr
            }
}
}
