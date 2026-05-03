use vstd::prelude::*;
verus! {

use crate::*;

pub struct Thread {
    pub state: ThreadState,

    pub owning_container: RwLockContainerPtr,
    pub container_allocator_4k: RwLockPageAllocatorPtr,
    pub container_allocator_2m: RwLockPageAllocatorPtr,
    pub container_allocator_1g: RwLockPageAllocatorPtr,
    pub container_scheduler: RwLockSchedulerPtr,
    pub scheduler_linkedlist_node: ExternalNode<RwLockThreadPtr>,

    pub owning_proc: RwLockProcessPtr,
    pub proc_pagetable_ptr: RwLockPageTableRoot,
    pub proc_linkedlist_node: ExternalNode<RwLockThreadPtr>,

    pub endpoint_descriptors: Array<Option<RwLockEndpointPtr>, MAX_NUM_ENDPOINT_DESCRIPTORS>,
    pub blocking_endpoint_ptr: Option<RwLockEndpointPtr>,
    pub blocking_endpoint_index: Option<EndpointIdx>,
    pub endpoint_linkedlist_node: ExternalNode<RwLockThreadPtr>,
    pub ipc_payload: IPCPayLoad,

    pub running_cpu: Option<CpuId>,
    pub error_code: Option<RetValueType>,  //this will only be set when it comes out of endpoint and goes to scheduler.
    pub trap_frame: TrapFrameOption,
}

impl LockInvTrait for Thread {
    open spec fn inv(&self) -> bool {
        &&&
        self.endpoint_descriptors.wf()
        &&&
        self.state is RUNNING == self.running_cpu is Some
        &&&
        self.error_code is Some ==> self.state is SCHEDULED
        &&&
        self.state is RUNNING ==> self.trap_frame.is_none()
    }
}

#[derive(Clone, Copy)]
#[allow(inconsistent_fields)]
pub enum IPCPayLoad {
    Message { va: VAddr, len: usize },
    Pages { va_range: VaRange4K },
    Endpoint { endpoint_index: EndpointIdx },
    Pci { bus: u8, dev: u8, fun: u8 },
    // TODO @Xiangdong add this when adding demand paging
    // PageFault { vaddr: VAddr },
    Empty,
}

impl IPCPayLoad {
    pub open spec fn is_some(&self) -> bool {
        match self {
            IPCPayLoad::Empty => false,
            _ => true,
        }
    }

    pub open spec fn is_none(&self) -> bool {
        match self {
            IPCPayLoad::Empty => true,
            _ => false,
        }
    }

    pub open spec fn spec_get_payload_as_message(&self) -> Option<(VAddr, usize)> {
        match self {
            IPCPayLoad::Message { va: va, len: len } => Some((*va, *len)),
            _ => None,
        }
    }

    #[verifier(when_used_as_spec(spec_get_payload_as_message))]
    pub fn get_payload_as_message(&self) -> (ret: Option<(VAddr, usize)>)
        ensures
            ret == self.spec_get_payload_as_message(),
    {
        match self {
            IPCPayLoad::Message { va: va, len: len } => Some((*va, *len)),
            _ => None,
        }
    }

    pub open spec fn spec_get_payload_as_va_range(&self) -> Option<VaRange4K> {
        match self {
            IPCPayLoad::Pages { va_range: va_range } => Some(*va_range),
            _ => None,
        }
    }

    #[verifier(when_used_as_spec(spec_get_payload_as_va_range))]
    pub fn get_payload_as_va_range(&self) -> (ret: Option<VaRange4K>)
        ensures
            ret == self.spec_get_payload_as_va_range(),
    {
        match self {
            IPCPayLoad::Pages { va_range: va_range } => Some(*va_range),
            _ => None,
        }
    }

    pub open spec fn spec_get_payload_as_endpoint(&self) -> Option<EndpointIdx> {
        match self {
            IPCPayLoad::Endpoint { endpoint_index: endpoint_index } => Some(*endpoint_index),
            _ => None,
        }
    }

    #[verifier(when_used_as_spec(spec_get_payload_as_endpoint))]
    pub fn get_payload_as_endpoint(&self) -> (ret: Option<EndpointIdx>)
        ensures
            ret == self.spec_get_payload_as_endpoint(),
    {
        match self {
            IPCPayLoad::Endpoint { endpoint_index: endpoint_index } => Some(*endpoint_index),
            _ => None,
        }
    }

    pub open spec fn spec_get_payload_as_pci(&self) -> Option<(u8, u8, u8)> {
        match self {
            IPCPayLoad::Pci { bus: bus, dev: dev, fun: fun } => Some((*bus, *dev, *fun)),
            _ => None,
        }
    }

    #[verifier(when_used_as_spec(spec_get_payload_as_pci))]
    pub fn get_payload_as_pci(&self) -> (ret: Option<(u8, u8, u8)>)
        ensures
            ret == self.spec_get_payload_as_pci(),
    {
        match self {
            IPCPayLoad::Pci { bus: bus, dev: dev, fun: fun } => Some((*bus, *dev, *fun)),
            _ => None,
        }
    }

    // pub open spec fn spec_get_payload_as_page_fault(&self) -> Option<VAddr> {
    //     match self {
    //         IPCPayLoad::PageFault { vaddr: vaddr } => Some(*vaddr),
    //         _ => None,
    //     }
    // }

    // #[verifier(when_used_as_spec(spec_get_payload_as_page_fault))]
    // pub fn get_payload_as_page_fault(&self) -> (ret: Option<VAddr>)
    //     ensures
    //         ret == self.spec_get_payload_as_page_fault(),
    // {
    //     match self {
    //         IPCPayLoad::PageFault { vaddr: vaddr } => Some(*vaddr),
    //         _ => None,
    //     }
    // }
}
impl LockMajorTrait for Thread {
    open spec fn lock_major_1(&self) -> LockMajorId {
        PROCESS_LOCK_MAJOR
    }

    open spec fn lock_major_2(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_3(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_default(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_1_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_2_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_3_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_default_predicate(&self) -> bool {
        true
    }
}

} // verus!
