use cpu_tlb_management::cpu_array_wf;
use vstd::prelude::*;
use crate::*;

verus! {
    pub trait UserViewHasKillState{
        spec fn killed(&self) -> bool;
    }

    /// This is a sound capture of the kernel user-level view because 
    /// LocalContext does not provide any interface that allow Lock, Operate, Unlock, Lock on user visible objects
    /// Therefore, all operations on the user view can be seen as atomic.
    pub ghost struct KernelU{
        pub cpu_array: Seq<CpuU>,
        pub process_map: Map<RwLockProcessPtr, ProcessU>,
    }

    pub open spec fn map_kernel_to_user_view(kernel_k: Kernel, kernel_u: KernelU) -> bool{
        &&&
        kernel_k.cpu_array.view().len() == kernel_u.cpu_array.len()
        &&&
        forall|i:int|
            #![auto]
            0 <= i < kernel_k.cpu_array.view().len()
            ==>
            kernel_k.cpu_array.view()[i].view().owning_container == kernel_u.cpu_array[i].owning_container
            &&
            kernel_k.cpu_array.view()[i].view().state == kernel_u.cpu_array[i].state
            &&
            kernel_k.cpu_array.view()[i].view().current_process == kernel_u.cpu_array[i].current_process
            &&
            kernel_k.cpu_array.view()[i].view().current_thread == kernel_u.cpu_array[i].current_thread

        &&&
        kernel_k.process_map.dom() == kernel_u.process_map.dom()
        &&&
        forall|ptr:usize|
            #![auto]
            kernel_k.process_map.dom().contains(ptr)
            ==>
            kernel_k.process_map.spec_index(ptr).view().owning_container == kernel_u.process_map.spec_index(ptr).owning_container
            &&
            kernel_k.get_process_pagetable(ptr) == kernel_u.process_map.spec_index(ptr).pagetable
            &&
            kernel_k.process_map.spec_index(ptr).view().parent == kernel_u.process_map.spec_index(ptr).parent
            &&
            kernel_k.process_map.spec_index(ptr).view().children.view() == kernel_u.process_map.spec_index(ptr).children
            &&
            kernel_k.process_map.spec_index(ptr).view().depth == kernel_u.process_map.spec_index(ptr).depth
            &&
            kernel_k.process_map.spec_index(ptr).view().uppertree_seq.view() == kernel_u.process_map.spec_index(ptr).uppertree_seq
            &&
            kernel_k.process_map.spec_index(ptr).view().subtree_set.view() == kernel_u.process_map.spec_index(ptr).subtree_set
            &&
            kernel_k.process_map.spec_index(ptr).view().owned_threads.view() == kernel_u.process_map.spec_index(ptr).owned_threads
            &&
            kernel_k.process_map.spec_index(ptr).being_killed() == kernel_u.process_map.spec_index(ptr).killed()

    }

    pub open spec fn record_map_change<K,V>(old_map: Map<K,V>, new_map: Map<K,V>, old_total: Map<K,V>, new_total: Map<K,V>) -> bool{
        // Killed elements
        &&&
        forall|k:K|
            #![auto]
            old_map.contains_key(k) && !new_map.contains_key(k)
            ==>
            new_total.contains_key(k) == false
        // New elements
        &&&
        forall|k:K|
            #![auto]
            !old_map.contains_key(k) && new_map.contains_key(k)
            ==>
            new_total.contains_key(k)
            &&
            new_total.spec_index(k) == new_map.spec_index(k)
        // Untouched elements
        &&&
        forall|k:K|
            #![auto]
            old_map.contains_key(k) == new_map.contains_key(k)
            ==>
            new_total.contains_key(k) == old_total.contains_key(k)
            &&
            new_total.spec_index(k) == new_map.spec_index(k)
    }

    pub open spec fn record_seq_change<V>(old_seq: Seq<V>, new_seq: Seq<V>, old_total: Seq<V>, new_total: Seq<V>) -> bool{
        // Len change
        &&&
        old_total.len() - new_total.len() == old_seq.len() - new_seq.len() 
    }
}