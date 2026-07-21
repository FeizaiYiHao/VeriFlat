use vstd::prelude::*;
verus! {

use crate::*;

pub struct Thread {
    pub state: ThreadState,

    pub owning_container: RwLockContainerPtr,
    pub container_depth: usize,
    pub scheduler_linkedlist_node: ExternalNode<RwLockThreadPtr>,

    pub owning_proc: RwLockProcessPtr,
    pub process_depth: usize,
    pub proc_pagetable_ptr: RwLockPageTableRoot,
    pub proc_linkedlist_node: ExternalNode<RwLockThreadPtr>,

    pub endpoint_descriptors: Array<Option<RwLockEndpointPtr>, MAX_NUM_ENDPOINT_DESCRIPTORS>,
    pub blocking_endpoint_ptr: Option<RwLockEndpointPtr>,
    pub blocking_endpoint_index: Option<EndpointIdx>,
    pub endpoint_linkedlist_node: ExternalNode<RwLockThreadPtr>,
    pub ipc_payload: IPCPayLoad,

    pub error_code: Option<RetValueType>,  //this will only be set when it comes out of endpoint and goes to scheduler.
    pub trap_frame: TrapFrameOption,

    pub upper_container_seq: Ghost<Seq<RwLockContainerPtr>>,

    /// Pages freed to the direct container whose quota has not yet been
    /// batch-returned (free path; batched on wunlock).
    pub direct_free_quota_pending_4k: Ghost<usize>,
    pub direct_free_quota_pending_2m: Ghost<usize>,
    pub direct_free_quota_pending_1g: Ghost<usize>,

    /// Per upper-container depth: pages freed to indirect containers whose
    /// quota has not yet been batch-returned.
    pub indirect_free_quota_pending_4k: Ghost<Seq<usize>>,
    pub indirect_free_quota_pending_2m: Ghost<Seq<usize>>,
    pub indirect_free_quota_pending_1g: Ghost<Seq<usize>>,
}

pub type ThreadRwLock = RwLock<Thread, (), (), (), THREAD_HAS_KILL_STATE>;
pub type ThreadLockedMap = LockedMap<RwLockThreadPtr, Thread, (), (), (), THREAD_HAS_KILL_STATE>;

impl Thread{
    pub open spec fn free_quota_pending_clean(&self) -> bool{
        &&& self.direct_free_quota_pending_4k.view() == 0
        &&& self.direct_free_quota_pending_2m.view() == 0
        &&& self.direct_free_quota_pending_1g.view() == 0
        &&&
        forall|i:int|
            #![trigger self.indirect_free_quota_pending_4k.view().spec_index(i)]
            0 <= i < self.indirect_free_quota_pending_4k.view().len()
            ==>
            self.indirect_free_quota_pending_4k.view().spec_index(i) == 0
        &&&
        forall|i:int|
            #![trigger self.indirect_free_quota_pending_2m.view().spec_index(i)]
            0 <= i < self.indirect_free_quota_pending_2m.view().len()
            ==>
            self.indirect_free_quota_pending_2m.view().spec_index(i) == 0
        &&&
        forall|i:int|
            #![trigger self.indirect_free_quota_pending_1g.view().spec_index(i)]
            0 <= i < self.indirect_free_quota_pending_1g.view().len()
            ==>
            self.indirect_free_quota_pending_1g.view().spec_index(i) == 0
    }
}

/// Free-quota pending counters must be zero unless the thread is write-locked.
/// Syscalls accumulate pending frees only under wlock; flushed before wunlock.
#[verifier::opaque]
pub open spec fn thread_free_quota_pending_empty_unless_wlocked(
    thread_map: ThreadLockedMap,
) -> bool {
    forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr).locking_thread()]
        thread_map.dom().contains(t_ptr)
        ==>
        !(thread_map.spec_index(t_ptr).locking_thread() is Write) ==>
            thread_map.spec_index(t_ptr).view().free_quota_pending_clean()
}

impl LockInvTrait for Thread {
    open spec fn inv(&self) -> bool {
        &&&
        self.endpoint_descriptors.wf()
        &&&
        self.error_code is Some ==> self.state is SCHEDULED
        &&&
        self.state is RUNNING ==> self.trap_frame.is_none()
        &&&
        self.state is BLOCKED == self.blocking_endpoint_ptr is Some
        &&&
        self.state is BLOCKED == self.blocking_endpoint_index is Some
        &&&
        self.state is BLOCKED ==> self.endpoint_descriptors.spec_index(self.blocking_endpoint_index.unwrap()) is Some
        &&&
        self.state is BLOCKED ==> self.endpoint_descriptors.spec_index(self.blocking_endpoint_index.unwrap()).unwrap() == self.blocking_endpoint_ptr.unwrap()
        &&&
        self.state is BLOCKED == !self.endpoint_linkedlist_node.is_init()
        &&&
        self.state is SCHEDULED == !self.scheduler_linkedlist_node.is_init()
        &&&
        self.upper_container_seq.view().len() == self.container_depth
        &&&
        self.upper_container_seq.view().len() == self.indirect_free_quota_pending_4k.view().len()
        &&&
        self.upper_container_seq.view().len() == self.indirect_free_quota_pending_2m.view().len()
        &&&
        self.upper_container_seq.view().len() == self.indirect_free_quota_pending_1g.view().len()
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
        THREAD_LOCK_MAJOR
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

impl LockOwnerIdTrait for Thread {
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.container_depth)
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.process_depth)
    }
}

impl LockUserVisibilityTrait for Thread {
    open spec fn is_user_visible() -> bool {
        false
    }
}

} // verus!
