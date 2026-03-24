use core::slice;

use vstd::prelude::*;
use crate::*;

verus! {
    impl Kernel{
        pub proof fn container_process_wf_proof()
            ensures
                forall|s:Self|
                    s.container_process_wf() <==> s.container_process_wf_inner(),
        {}

        pub closed spec fn container_process_wf(&self) -> bool{
            self.container_process_wf_inner()
        }

        pub open spec fn container_process_wf_inner(&self) -> bool{
            &&&
            forall|c_ptr:RwLockContainerPtr|
                #![trigger self.container_map.spec_index(c_ptr).view().root_process]
                #![trigger self.container_map.spec_index(c_ptr).view().owned_processes]
                self.container_map.dom().contains(c_ptr)
                ==>
                self.container_map.spec_index(c_ptr).wlocked()
                ||
                {
                    &&&
                    self.process_map.dom().contains(self.container_map.spec_index(c_ptr).view().root_process)
                    &&&
                    self.container_map.spec_index(c_ptr).view().owned_processes.view().contains(self.container_map.spec_index(c_ptr).view().root_process)
                    &&&
                    self.container_map.spec_index(c_ptr).view().owned_processes.view().subset_of(self.process_map.dom())
                }
            &&&
            forall|c_ptr:RwLockContainerPtr, p_ptr:RwLockProcessPtr|
                #![trigger self.container_map.spec_index(c_ptr).view().owned_processes, self.process_map.spec_index(p_ptr).view().owning_container]
                #![trigger self.container_map.spec_index(c_ptr).view().owned_processes.view().contains(p_ptr)]
                self.container_map.dom().contains(c_ptr) && self.container_map.spec_index(c_ptr).view().owned_processes.view().contains(p_ptr)
                ==>
                write_locked_by_same_thread(self.container_map.spec_index(c_ptr), self.process_map.spec_index(p_ptr))
                ||
                {
                    &&&
                    self.process_map.spec_index(p_ptr).view().owning_container == c_ptr
                }
            &&&
            forall|p_ptr:RwLockProcessPtr|
                #![trigger self.process_map.spec_index(p_ptr).view().owning_container]
                self.process_map.dom().contains(p_ptr)
                ==>
                self.process_map.spec_index(p_ptr).wlocked()
                ||
                {
                    &&&
                    self.container_map.dom().contains(self.process_map.spec_index(p_ptr).view().owning_container)
                    &&&
                    {
                        |||
                        write_locked_by_same_thread(self.container_map.spec_index(self.process_map.spec_index(p_ptr).view().owning_container), self.process_map.spec_index(p_ptr))
                        |||
                        self.container_map.spec_index(self.process_map.spec_index(p_ptr).view().owning_container).view().owned_processes.view().contains(p_ptr)
                    }
                }
        }

        pub proof fn process_tree_wf_proof()
            ensures 
                forall|s:Self|
                    s.process_tree_wf() <==> s.process_tree_wf_inner()
        {

        }

        pub closed spec fn process_tree_wf(&self) -> bool{
            self.process_tree_wf_inner()
        } 

        pub open spec fn process_tree_wf_inner(&self) -> bool
            recommends
                self.container_process_wf_inner(),
        {
            &&&
            forall|c_ptr:RwLockContainerPtr|
                #![trigger self.container_map.spec_index(c_ptr).view().root_process]
                #![trigger self.container_map.spec_index(c_ptr).view().owned_processes]
                self.container_map.dom().contains(c_ptr)
                ==>
                self.container_map.spec_index(c_ptr).wlocked()
                ||
                {
                    &&&
                    process_tree_wf(self.container_map.spec_index(c_ptr).view().root_process, self.container_map.spec_index(c_ptr).view().owned_processes@, self.process_map)
                }
        }
    }
}