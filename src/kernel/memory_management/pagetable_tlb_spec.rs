use vstd::prelude::*;
use crate::*;
use super::*;
verus! {

// pub open spec fn spec_tlb_entry_equal_to_map_entry(tlb_entry:TLBEntry, map_entry: MapEntry) -> bool{
//     &&&
//     tlb_entry.addr == map_entry.addr
//     &&&
//     tlb_entry.execute_disable == map_entry.execute_disable
//     &&&
//     tlb_entry.write == map_entry.write
// }

// /// if the pagetable is Acquired, the TLB can have entry in which the entry is not present
// /// otherwise TLB has to be a strict submap.
// pub open spec fn single_cpu_single_pcid_tlb_subset_of_pagetable(cpu_tlb: SingleTLB, pagetable: RwLock<PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>) -> bool
// {
//     &&&
//     forall|va: VAddr|
//         #![trigger pagetable@.mapping_4k().dom().contains(va)]
//         #![trigger cpu_tlb.tlb_4k()[va]]
//         va_4k_valid(va) && pagetable@.mapping_4k().dom().contains(va)
//         ==>
//         cpu_tlb.tlb_4k().dom().contains(va) 
//             ==> 
//             (pagetable.wlocked() ||  pagetable@.mapping_4k()[va].present)
//             &&
//             spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_4k()[va], pagetable@.mapping_4k()[va])
//     &&&
//     forall|va: VAddr|
//         #![trigger pagetable@.mapping_2m().dom().contains(va)]
//         #![trigger cpu_tlb.tlb_2m()[va]]
//         va_2m_valid(va) && pagetable@.mapping_2m().dom().contains(va)
//         ==>
//          cpu_tlb.tlb_2m().dom().contains(va) 
//             ==> 
//             (pagetable.wlocked() ||  pagetable@.mapping_2m()[va].present)
//             &&
//             spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_2m()[va], pagetable@.mapping_2m()[va])
//     &&&
//     forall|va: VAddr|
//         #![trigger pagetable@.mapping_1g().dom().contains(va)]
//         #![trigger cpu_tlb.tlb_1g()[va]]
//         va_1g_valid(va) && pagetable@.mapping_1g().dom().contains(va)
//         ==>
//         cpu_tlb.tlb_1g().dom().contains(va) 
//             ==> 
//             (pagetable.wlocked() ||  pagetable@.mapping_1g()[va].present)
//             &&
//             spec_tlb_entry_equal_to_map_entry(cpu_tlb.tlb_1g()[va], pagetable@.mapping_1g()[va])
// }

// pub open spec fn tlb_subset_of_pagetable(cpu_tlb: CpuTLB, pagetable: RwLock<PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>) -> bool
//     recommends
//         cpu_tlb.inv(),
//         pagetable@.pcid is Some,
// {
//     &&&
//     forall|cpu_id:CpuId|
//         #![auto] 
//         cpu_id_valid(cpu_id)
//         ==>
//         single_cpu_single_pcid_tlb_subset_of_pagetable(cpu_tlb[(cpu_id, pagetable@.pcid.unwrap())], pagetable)
// }

// impl KernelK{
//     pub open spec fn kernel_tlb_inv(&self) -> bool{
//         &&&
//         self.cpu_pagetable_pointers_wf()
//         &&&
//         self.cpu_dirty_map_contains_only_alive_pagetable()
//         &&&
//         self.cpu_tlb_submap_of_dirty_pagetable()
//     }

//     pub open spec fn cpu_pagetable_pointers_wf(&self) -> bool{
//         &&&
//         forall|cpu_id: CpuId|
//         #![auto]
//         cpu_id_valid(cpu_id)
//         ==>
//         {
//             &&&
//             self.get_pagetable_map().contains(self.get_cpu(cpu_id).view().current_pagetable)
//             &&&
//             {
//                 |||
//                 write_locked_by_same_thread(self.get_pagetable(self.get_cpu(cpu_id).view().current_pagetable), self.get_cpu(cpu_id))
//                 |||
//                 {
//                     &&&
//                     self.get_pagetable(self.get_cpu(cpu_id).view().current_pagetable).view().cr3 == self.get_cpu(cpu_id).view().current_cr3
//                     &&&
//                     self.get_pagetable(self.get_cpu(cpu_id).view().current_pagetable).view().pcid_or_ioid() == self.get_cpu(cpu_id).view().current_pcid
//                 }
//             }
            
//         }
//     }

//     pub open spec fn cpu_dirty_map_contains_only_alive_pagetable(&self) -> bool{
//         &&&
//         forall|cpu_id: CpuId, pcid:Pcid|
//         #![auto]
//         cpu_id_valid(cpu_id) && usize_in_range::<PCID_MAX>(pcid) && self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid] is Some
//         ==>
//         self.get_pagetable_map().contains(self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap())
//         &&
//         self.get_pagetable(self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap()).view().pcid_or_ioid() == pcid
//     }

//     pub open spec fn cpu_tlb_submap_of_dirty_pagetable(&self) -> bool{
//         &&&
//         forall|cpu_id: CpuId, pcid:Pcid|
//         #![trigger self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid]]
//         cpu_id_valid(cpu_id) && usize_in_range::<PCID_MAX>(pcid) && self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid] is Some
//         ==> 
//         single_cpu_single_pcid_tlb_subset_of_pagetable(self.cpu_array.get_tlb(cpu_id, pcid), self.get_pagetable(self.get_cpu(cpu_id).view().tlb_dirty_bitmap()[pcid].unwrap()))

//     }
// }

}