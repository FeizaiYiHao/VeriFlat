use vstd::prelude::*;
use vstd::simple_pptr::*;
verus! {

use crate::*;

pub struct Thread {
    pub state: ThreadState,
    /// The upstream caller currently served by this thread, if any.
    pub caller: Option<RwLockThreadPtr>,
    /// The downstream callee while this thread is waiting for a reply.
    pub callee: Option<RwLockThreadPtr>,

    pub owning_container: RwLockContainerPtr,
    pub container_depth: usize,
    pub scheduler_linkedlist_node: ExternalNode<RwLockThreadPtr>,

    pub owning_proc: RwLockProcessPtr,
    pub process_depth: usize,
    pub proc_pagetable_ptr: RwLockPageTableRoot,
    pub proc_linkedlist_node: ExternalNode<RwLockThreadPtr>,

    /// Thread-local quota is independent from the owning process's quota.
    /// A future transfer syscall moves quota between the two tiers.
    pub quota_4k: usize,
    pub quota_2m: usize,
    pub quota_1g: usize,

    /// Pages pulled from the allocator but not yet retyped. These caches may
    /// be non-empty only while this thread is write-locked.
    pub temp_alloc_cache_4k: Ghost<Set<PagePtr>>,
    pub temp_alloc_cache_2m: Ghost<Set<PagePtr>>,
    pub temp_alloc_cache_1g: Ghost<Set<PagePtr>>,

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

pub type ThreadRwLock = RwLock<Thread, (), (), THREAD_HAS_KILL_STATE>;
pub type ThreadLockedMap = LockedMap<RwLockThreadPtr, Thread, (), (), THREAD_HAS_KILL_STATE>;

impl Thread{
    #[verifier::opaque]
    pub open spec fn stable_allocation_root_equal(&self, other: &Self) -> bool {
        &&& self.owning_container == other.owning_container
        &&& self.upper_container_seq == other.upper_container_seq
        &&& self.state == other.state
        &&& self.blocking_endpoint_ptr == other.blocking_endpoint_ptr
    }

    pub open spec fn ipc_framed_fields_equal(&self, other: &Self) -> bool {
        &&& self.owning_container == other.owning_container
        &&& self.container_depth == other.container_depth
        &&& self.scheduler_linkedlist_node.addr()
            == other.scheduler_linkedlist_node.addr()
        &&& self.owning_proc == other.owning_proc
        &&& self.process_depth == other.process_depth
        &&& self.proc_pagetable_ptr == other.proc_pagetable_ptr
        &&& self.proc_linkedlist_node.addr() == other.proc_linkedlist_node.addr()
        &&& self.quota_4k == other.quota_4k
        &&& self.quota_2m == other.quota_2m
        &&& self.quota_1g == other.quota_1g
        &&& self.temp_alloc_cache_4k == other.temp_alloc_cache_4k
        &&& self.temp_alloc_cache_2m == other.temp_alloc_cache_2m
        &&& self.temp_alloc_cache_1g == other.temp_alloc_cache_1g
        &&& self.endpoint_descriptors == other.endpoint_descriptors
        &&& self.endpoint_linkedlist_node.addr()
            == other.endpoint_linkedlist_node.addr()
        &&& self.upper_container_seq == other.upper_container_seq
        &&& self.free_quota_pending_fields_equal(other)
    }

    pub open spec fn free_quota_pending_fields_equal(&self, other: &Self) -> bool {
        &&& self.direct_free_quota_pending_4k
            == other.direct_free_quota_pending_4k
        &&& self.direct_free_quota_pending_2m
            == other.direct_free_quota_pending_2m
        &&& self.direct_free_quota_pending_1g
            == other.direct_free_quota_pending_1g
        &&& self.indirect_free_quota_pending_4k
            == other.indirect_free_quota_pending_4k
        &&& self.indirect_free_quota_pending_2m
            == other.indirect_free_quota_pending_2m
        &&& self.indirect_free_quota_pending_1g
            == other.indirect_free_quota_pending_1g
    }

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

    /// Construct a fresh Thread for retype operations.
    /// State is RUNNING{cpu_id: 0} (not waiting, not SCHEDULED).
    /// All endpoint fields are None/empty, all pending quotas are 0,
    /// caller/callee are None, linkedlist nodes are init, trap_frame is None.
    #[verifier::external_body]
    pub fn new_fresh(
        owning_container: RwLockContainerPtr,
        container_depth: usize,
        owning_proc: RwLockProcessPtr,
        process_depth: usize,
        proc_pagetable_ptr: RwLockPageTableRoot,
        upper_container_seq: Ghost<Seq<RwLockContainerPtr>>,
    ) -> (ret: Self)
        ensures
            ret.inv(),
            ret.state == (ThreadState::RUNNING { cpu_id: 0 }),
            ret.current_lock_major() == THREAD_LOCK_MAJOR,
            ret.owning_container == owning_container,
            ret.container_depth == container_depth,
            ret.owning_proc == owning_proc,
            ret.process_depth == process_depth,
            ret.proc_pagetable_ptr == proc_pagetable_ptr,
            ret.upper_container_seq.view() == upper_container_seq.view(),
            !ret.state.is_endpoint_waiting(),
            (ret.state is WAITING_REPLY) == false,
            (ret.state is SCHEDULED) == false,
            ret.caller is None,
            ret.callee is None,
            ret.proc_linkedlist_node.is_init(),
            ret.scheduler_linkedlist_node.is_init(),
            ret.blocking_endpoint_ptr is None,
            ret.blocking_endpoint_index is None,
            forall|edp_index: EndpointIdx| #![auto]
                ret.endpoint_descriptors.view().spec_index(edp_index as int) is None,
            ret.free_quota_pending_clean(),
            ret.temp_alloc_clean(),
            ret.quota_4k == 0,
            ret.quota_2m == 0,
            ret.quota_1g == 0,
    {
        unimplemented!()
    }
}

impl Thread {
    /// Move the running thread into an endpoint wait queue and hand its
    /// intrusive endpoint node to the queue owner.
    pub fn block_on_endpoint(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        endpoint_ptr: RwLockEndpointPtr,
        endpoint_index: EndpointIdx,
        waiting_state: ThreadState,
        payload: IPCPayLoad,
        pt_regs: &Registers,
    ) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state is RUNNING,
            waiting_state.is_endpoint_waiting(),
            waiting_state is RECEIVING_CALL ==> old(self).caller is None,
            payload.wf(),
            edp_idx_valid(endpoint_index),
            old(self).endpoint_descriptors.spec_index(endpoint_index)
                == Some(endpoint_ptr),
        ensures
            final(self).inv(),
            final(self).ipc_framed_fields_equal(old(self)),
            final(self).state == waiting_state,
            final(self).blocking_endpoint_ptr == Some(endpoint_ptr),
            final(self).blocking_endpoint_index == Some(endpoint_index),
            final(self).ipc_payload =~= payload,
            final(self).trap_frame.is_some(),
            final(self).trap_frame.get_some_0() =~= pt_regs,
            final(self).caller == old(self).caller,
            final(self).callee == old(self).callee,
            final(self).owning_container == old(self).owning_container,
            final(self).container_depth == old(self).container_depth,
            final(self).scheduler_linkedlist_node.addr()
                == old(self).scheduler_linkedlist_node.addr(),
            final(self).owning_proc == old(self).owning_proc,
            final(self).process_depth == old(self).process_depth,
            final(self).proc_pagetable_ptr == old(self).proc_pagetable_ptr,
            final(self).proc_linkedlist_node.addr()
                == old(self).proc_linkedlist_node.addr(),
            final(self).endpoint_descriptors == old(self).endpoint_descriptors,
            final(self).upper_container_seq == old(self).upper_container_seq,
            final(self).endpoint_linkedlist_node.addr()
                == old(self).endpoint_linkedlist_node.addr(),
            ret.0 == final(self).endpoint_linkedlist_node.addr(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == thread_ptr,
    {
        let (node_addr, mut node_perm) = self.endpoint_linkedlist_node.take();
        node_update_value(node_addr, &mut node_perm, thread_ptr);
        self.blocking_endpoint_ptr = Some(endpoint_ptr);
        self.blocking_endpoint_index = Some(endpoint_index);
        self.ipc_payload = payload;
        self.trap_frame.set_self(pt_regs);
        self.state = waiting_state;
        (node_addr, node_perm)
    }

    /// Remove an ordinary sender/receiver from its endpoint and prepare its
    /// scheduler node. The saved trap frame remains available for dispatch.
    pub fn endpoint_waiter_to_scheduled(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        result: RetValueType,
        endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    ) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state.is_endpoint_waiting(),
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr()
                == old(self).endpoint_linkedlist_node.addr(),
            endpoint_node_perm.view().value().view() == thread_ptr,
        ensures
            final(self).inv(),
            final(self).ipc_framed_fields_equal(old(self)),
            final(self).state is SCHEDULED,
            final(self).blocking_endpoint_ptr is None,
            final(self).blocking_endpoint_index is None,
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node.is_init() == false,
            final(self).error_code == Some(result),
            final(self).ipc_payload is Empty,
            final(self).trap_frame == old(self).trap_frame,
            final(self).caller == old(self).caller,
            final(self).callee == old(self).callee,
            ret.0 == final(self).scheduler_linkedlist_node.addr(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == thread_ptr,
    {
        self.endpoint_linkedlist_node.put(endpoint_node_perm);
        let (node_addr, mut node_perm) = self.scheduler_linkedlist_node.take();
        node_update_value(node_addr, &mut node_perm, thread_ptr);
        self.blocking_endpoint_ptr = None;
        self.blocking_endpoint_index = None;
        self.ipc_payload = IPCPayLoad::Empty;
        self.error_code = Some(result);
        self.state = ThreadState::SCHEDULED;
        (node_addr, node_perm)
    }

    /// Remove a matched endpoint sender/receiver from the channel while its
    /// endpoint descriptor is kept stable by the thread write lock.
    pub fn endpoint_waiter_to_endpoint_transit(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    )
        requires
            old(self).inv(),
            old(self).state is SENDING || old(self).state is RECEIVING,
            old(self).ipc_payload is Endpoint,
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr()
                == old(self).endpoint_linkedlist_node.addr(),
            endpoint_node_perm.view().value().view() == thread_ptr,
        ensures
            final(self).inv(),
            final(self).ipc_framed_fields_equal(old(self)),
            final(self).state is IPC_ENDPOINT_TRANSIT,
            final(self).blocking_endpoint_ptr is None,
            final(self).blocking_endpoint_index is None,
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node
                == old(self).scheduler_linkedlist_node,
            final(self).ipc_payload == old(self).ipc_payload,
            final(self).error_code == old(self).error_code,
            final(self).trap_frame == old(self).trap_frame,
            final(self).caller == old(self).caller,
            final(self).callee == old(self).callee,
    {
        self.endpoint_linkedlist_node.put(endpoint_node_perm);
        self.blocking_endpoint_ptr = None;
        self.blocking_endpoint_index = None;
        self.state = ThreadState::IPC_ENDPOINT_TRANSIT;
    }

    /// Prepare an endpoint-transit peer for its scheduler with the rendezvous
    /// result that the current thread also receives.
    pub fn endpoint_transit_to_scheduled(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        result: RetValueType,
    ) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state is IPC_ENDPOINT_TRANSIT,
        ensures
            final(self).inv(),
            final(self).ipc_framed_fields_equal(old(self)),
            final(self).state is SCHEDULED,
            final(self).blocking_endpoint_ptr is None,
            final(self).blocking_endpoint_index is None,
            final(self).endpoint_linkedlist_node
                == old(self).endpoint_linkedlist_node,
            final(self).scheduler_linkedlist_node.is_init() == false,
            final(self).error_code == Some(result),
            final(self).ipc_payload is Empty,
            final(self).trap_frame == old(self).trap_frame,
            final(self).caller == old(self).caller,
            final(self).callee == old(self).callee,
            ret.0 == final(self).scheduler_linkedlist_node.addr(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == thread_ptr,
    {
        let (node_addr, mut node_perm) = self.scheduler_linkedlist_node.take();
        node_update_value(node_addr, &mut node_perm, thread_ptr);
        self.ipc_payload = IPCPayLoad::Empty;
        self.error_code = Some(result);
        self.state = ThreadState::SCHEDULED;
        (node_addr, node_perm)
    }

    /// A queued caller has met a receive-call thread. It leaves the endpoint
    /// but stays blocked until its callee replies.
    pub fn endpoint_caller_to_waiting_reply(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        callee_ptr: RwLockThreadPtr,
        endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
    )
        requires
            old(self).inv(),
            old(self).state is CALLING,
            thread_ptr != callee_ptr,
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr()
                == old(self).endpoint_linkedlist_node.addr(),
            endpoint_node_perm.view().value().view() == thread_ptr,
        ensures
            final(self).inv(),
            final(self).ipc_framed_fields_equal(old(self)),
            final(self).state is WAITING_REPLY,
            final(self).callee == Some(callee_ptr),
            final(self).caller == old(self).caller,
            final(self).blocking_endpoint_ptr is None,
            final(self).blocking_endpoint_index is None,
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node
                == old(self).scheduler_linkedlist_node,
            final(self).trap_frame == old(self).trap_frame,
    {
        self.endpoint_linkedlist_node.put(endpoint_node_perm);
        self.blocking_endpoint_ptr = None;
        self.blocking_endpoint_index = None;
        self.callee = Some(callee_ptr);
        self.state = ThreadState::WAITING_REPLY;
    }

    /// The currently running receive-call thread accepts a queued caller.
    pub fn accept_queued_caller(
        &mut self,
        caller_ptr: RwLockThreadPtr,
        self_ptr: RwLockThreadPtr,
    )
        requires
            old(self).inv(),
            old(self).state is RUNNING,
            old(self).caller is None,
            old(self).callee is None,
            caller_ptr != self_ptr,
        ensures
            final(self).inv(),
            final(self).ipc_framed_fields_equal(old(self)),
            final(self).state == old(self).state,
            final(self).caller == Some(caller_ptr),
            final(self).callee is None,
            final(self).trap_frame == old(self).trap_frame,
    {
        self.caller = Some(caller_ptr);
    }

    /// The running caller waits for a reply while a previously blocked
    /// receive-call thread takes over its CPU.
    pub fn running_caller_to_waiting_reply(
        &mut self,
        callee_ptr: RwLockThreadPtr,
        self_ptr: RwLockThreadPtr,
        pt_regs: &Registers,
    )
        requires
            old(self).inv(),
            old(self).state is RUNNING,
            old(self).callee is None,
            callee_ptr != self_ptr,
        ensures
            final(self).inv(),
            final(self).ipc_framed_fields_equal(old(self)),
            final(self).state is WAITING_REPLY,
            final(self).callee == Some(callee_ptr),
            final(self).caller == old(self).caller,
            final(self).trap_frame.is_some(),
            final(self).trap_frame.get_some_0() =~= pt_regs,
    {
        self.trap_frame.set_self(pt_regs);
        self.callee = Some(callee_ptr);
        self.state = ThreadState::WAITING_REPLY;
    }

    /// A blocked receive-call thread becomes the running callee and restores
    /// the register image it saved when entering the endpoint.
    pub fn endpoint_receiver_to_running(
        &mut self,
        thread_ptr: RwLockThreadPtr,
        caller_ptr: RwLockThreadPtr,
        cpu_id: CpuId,
        endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>,
        pt_regs: &mut Registers,
    )
        requires
            old(self).inv(),
            old(self).state is RECEIVING_CALL,
            old(self).caller is None,
            old(self).callee is None,
            thread_ptr != caller_ptr,
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr()
                == old(self).endpoint_linkedlist_node.addr(),
            endpoint_node_perm.view().value().view() == thread_ptr,
        ensures
            final(self).inv(),
            final(self).ipc_framed_fields_equal(old(self)),
            final(self).state == (ThreadState::RUNNING { cpu_id }),
            final(self).caller == Some(caller_ptr),
            final(self).callee is None,
            final(self).blocking_endpoint_ptr is None,
            final(self).blocking_endpoint_index is None,
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node
                == old(self).scheduler_linkedlist_node,
            final(self).trap_frame.is_none(),
            *final(pt_regs) =~= *old(self).trap_frame.get_some_0(),
    {
        self.endpoint_linkedlist_node.put(endpoint_node_perm);
        self.trap_frame.set_dst(pt_regs);
        self.trap_frame.set_to_none();
        self.blocking_endpoint_ptr = None;
        self.blocking_endpoint_index = None;
        self.caller = Some(caller_ptr);
        self.state = ThreadState::RUNNING { cpu_id };
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
        self.ipc_payload.wf()
        &&&
        self.error_code is Some ==> self.state is SCHEDULED
        &&&
        self.state is RUNNING ==> self.trap_frame.is_none()
        &&&
        (self.state.is_endpoint_waiting()
            || self.state is WAITING_REPLY
            || self.state is IPC_ENDPOINT_TRANSIT)
            ==> self.trap_frame.is_some()
        &&&
        self.state is IPC_ENDPOINT_TRANSIT ==> self.ipc_payload is Endpoint
        &&&
        self.state.is_endpoint_waiting() == self.blocking_endpoint_ptr is Some
        &&&
        self.state.is_endpoint_waiting() == self.blocking_endpoint_index is Some
        &&&
        self.state.is_endpoint_waiting()
            ==> edp_idx_valid(self.blocking_endpoint_index.unwrap())
        &&&
        self.state.is_endpoint_waiting()
            ==> self.endpoint_descriptors.spec_index(
                self.blocking_endpoint_index.unwrap(),
            ) is Some
        &&&
        self.state.is_endpoint_waiting()
            ==> self.endpoint_descriptors.spec_index(
                self.blocking_endpoint_index.unwrap(),
            ).unwrap() == self.blocking_endpoint_ptr.unwrap()
        &&&
        self.state.is_endpoint_waiting()
            == !self.endpoint_linkedlist_node.is_init()
        &&&
        self.state is SCHEDULED == !self.scheduler_linkedlist_node.is_init()
        &&&
        (self.state is WAITING_REPLY) == (self.callee is Some)
        &&&
        self.state is RECEIVING_CALL ==> self.caller is None
        &&&
        self.upper_container_seq.view().len() == self.container_depth
        &&&
        self.upper_container_seq.view().len() == self.indirect_free_quota_pending_4k.view().len()
        &&&
        self.upper_container_seq.view().len() == self.indirect_free_quota_pending_2m.view().len()
        &&&
        self.upper_container_seq.view().len() == self.indirect_free_quota_pending_1g.view().len()
        &&&
        self.quota_within_bound()
    }

}

impl Thread {
    pub open spec fn temp_alloc_clean(&self) -> bool {
        &&& self.temp_alloc_cache_4k.view().len() == 0
        &&& self.temp_alloc_cache_2m.view().len() == 0
        &&& self.temp_alloc_cache_1g.view().len() == 0
    }

    pub open spec fn quota_within_bound(&self) -> bool {
        &&& self.quota_4k >= self.temp_alloc_cache_4k.view().len()
        &&& self.quota_2m >= self.temp_alloc_cache_2m.view().len()
        &&& self.quota_1g >= self.temp_alloc_cache_1g.view().len()
    }
}

pub open spec fn thread_effective_quota_4k(thread_lock: ThreadRwLock) -> int {
    thread_lock.view().quota_4k as int
        - thread_lock.view().temp_alloc_cache_4k.view().len() as int
}

pub open spec fn thread_effective_quota_2m(thread_lock: ThreadRwLock) -> int {
    thread_lock.view().quota_2m as int
        - thread_lock.view().temp_alloc_cache_2m.view().len() as int
}

pub open spec fn thread_effective_quota_1g(thread_lock: ThreadRwLock) -> int {
    thread_lock.view().quota_1g as int
        - thread_lock.view().temp_alloc_cache_1g.view().len() as int
}

#[verifier::opaque]
pub open spec fn thread_temp_alloc_empty_unless_wlocked(
    thread_map: ThreadLockedMap,
) -> bool {
    forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr).locking_thread()]
        thread_map.dom().contains(t_ptr)
        ==> !(thread_map.spec_index(t_ptr).locking_thread() is Write)
        ==> thread_map.spec_index(t_ptr).view().temp_alloc_clean()
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
    pub open spec fn wf(&self) -> bool {
        match self {
            IPCPayLoad::Pages { va_range } => va_range.wf(),
            IPCPayLoad::Endpoint { endpoint_index } =>
                edp_idx_valid(*endpoint_index),
            _ => true,
        }
    }

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
        THREAD_BLOCKED_LOCK_MAJOR
    }

    open spec fn lock_major_3(&self) -> LockMajorId {
        THREAD_SCHEDULED_LOCK_MAJOR
    }

    open spec fn lock_major_default(&self) -> LockMajorId {
        THREAD_IPC_TRANSIT_LOCK_MAJOR
    }

    open spec fn lock_major_1_predicate(&self) -> bool {
        self.state is RUNNING
    }

    open spec fn lock_major_2_predicate(&self) -> bool {
        self.state.is_endpoint_waiting() || self.state is WAITING_REPLY
    }

    open spec fn lock_major_3_predicate(&self) -> bool {
        self.state is SCHEDULED
    }

    open spec fn lock_major_default_predicate(&self) -> bool {
        self.state is IPC_ENDPOINT_TRANSIT
    }
}

impl LockOwnerIdTrait for Thread {
    open spec fn container_depth(&self) -> LockOwnerId {
        if self.state.is_endpoint_waiting()
            || self.state is WAITING_REPLY
            || self.state is IPC_ENDPOINT_TRANSIT
        {
            LockOwnerId::NotApp
        } else {
            LockOwnerId::Some(self.container_depth)
        }
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        if self.state.is_endpoint_waiting()
            || self.state is WAITING_REPLY
            || self.state is IPC_ENDPOINT_TRANSIT
        {
            LockOwnerId::NotApp
        } else {
            LockOwnerId::Some(self.process_depth)
        }
    }
}

impl LockUserVisibilityTrait for Thread {
    open spec fn is_user_visible() -> bool {
        false
    }
}

} // verus!
