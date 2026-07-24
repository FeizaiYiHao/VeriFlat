use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn thread_cpu_wf(thread_map: ThreadLockedMap, cpu_array:CpuLockedArray) -> bool {
        &&&
        forall|cpu_i:CpuId|
            #![trigger cpu_array.spec_index(cpu_i).view().view().current_thread]
            cpu_id_valid(cpu_i)
            &&
            cpu_array.spec_index(cpu_i).view().view().state is Running
            ==>
            {
                &&&
                cpu_array.spec_index(cpu_i).view().view().current_thread is Some
                &&&
                thread_map.dom().contains(cpu_array.spec_index(cpu_i).view().view().current_thread.unwrap())
                &&&
                thread_map.spec_index(cpu_array.spec_index(cpu_i).view().view().current_thread.unwrap()).view().state == (ThreadState::RUNNING{cpu_id: cpu_i})
            }
        &&&
        forall|t_ptr:RwLockThreadPtr|
            #![trigger thread_map.spec_index(t_ptr).view().state]
            thread_map.dom().contains(t_ptr)
            &&
            thread_map.spec_index(t_ptr).view().state is RUNNING
            ==>
            {
                &&&
                cpu_id_valid(thread_map.spec_index(t_ptr).view().state->RUNNING_cpu_id)
                &&&
                cpu_array.spec_index(thread_map.spec_index(t_ptr).view().state->RUNNING_cpu_id).view().view().state is Running
                &&&
                cpu_array.spec_index(thread_map.spec_index(t_ptr).view().state->RUNNING_cpu_id).view().view().current_thread == Some(t_ptr)
            }
    }
}
