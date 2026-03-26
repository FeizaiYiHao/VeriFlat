use vstd::prelude::*;
use crate::*;
verus! {
    pub proof fn cpu_pagetable_wf_proof()
        ensures
            forall|pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>|
                cpu_pagetable_wf_inner(pagetable_map, cpu_array) == cpu_pagetable_wf(pagetable_map, cpu_array)
    {}
    pub closed spec fn cpu_pagetable_wf(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        cpu_pagetable_wf_inner(pagetable_map, cpu_array)
    }
    pub open spec fn cpu_pagetable_wf_inner(pagetable_map: LockedMap<RwLockPageTableRoot, PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>, cpu_array: LockedArray<Cpu, NUM_CPUS, CPU_HAS_KILL_STATE>) -> bool {
        &&&
        forall|cpu_i:CpuId, pcid: Pcid|
            #![trigger cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid]]
            cpu_id_valid(cpu_i)
            &&
            pcid_valid(pcid)
            &&
            pcid != KERNEL_DEFAULT_PCID
            &&
            cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid] is Some
            &&
            cpu_array.spec_index(cpu_i).view().wlocked() == false
            ==>
            pagetable_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap())
            &&
            {
                write_locked_by_same_thread(cpu_array.spec_index(cpu_i).view(), pagetable_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap()))
                ||
                pagetable_map.spec_index(cpu_array.spec_index(cpu_i).view().view().tlb_dirty_bitmap()[pcid].unwrap()).view().pcid_or_ioid() == pcid
            }
    }
}