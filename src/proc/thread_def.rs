use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::simple_pptr::*;
verus! {
use crate::*;

/// Deepest page-table level installed so far for the 4K page being mapped.
pub ghost enum Mmap4kDirectory { None, L4, L3, L2 }

/// Page-table lock mode of a 4K mapping: big lock read, small locks filling, or small locks after filling.
pub ghost enum Mmap4kPhase { Read, Fill, Filled }

/// Page-table lock state of a pages rendezvous: unlocked, big lock read, small locks filling, or small locks after filling.
pub ghost enum IpcPagesTables { Unlocked, Read, Fill, Filled }

/// Process creation: the shared `range`, the child's initial registers and endpoint, whether it
/// gets an IOMMU table, and the child once it is published.
pub ghost struct NewProcessProgress {
    pub range: VaRange4K, pub regs: Registers, pub endpoint_index: Option<EndpointIdx>, pub with_iommu: bool,
    pub child: Option<RwLockProcessPtr>,
}

/// Container creation: the shared `range`, the quotas, the donated cpu, the root process's initial
/// registers, the caller's descriptor whose endpoint seeds the root thread, and the child container
/// once it is published.
pub ghost struct NewContainerProgress {
    pub range: VaRange4K, pub funding: usize, pub process_quota: usize, pub transfer_cpu: CpuId, pub regs: Registers,
    pub endpoint_index: Option<EndpointIdx>, pub child_container: Option<RwLockContainerPtr>,
}

/// The syscall a share belongs to, with the objects and arguments its later steps need.
pub ghost enum Share4kOrigin {
    NewProcess(NewProcessProgress),
    NewContainer(NewContainerProgress),
    IpcPages { peer: RwLockThreadPtr },
}

/// Where a kill stands at the marked process it works on.
pub ghost enum KillStage {
    /// No thread of the process is marked: the kill descends into a child, marks a thread, or reclaims the process.
    Walk,
    /// The process's first thread `thread` is marked and write-held until it leaves the process.
    Thread { thread: RwLockThreadPtr },
    /// The process's page table and IOMMU table are write-locked while its leaves are reclaimed; `flushed` records that
    /// the released translations are gone from every cpu.
    Reclaim { flushed: bool },
    /// The process's quota of size `returned` and of every smaller size went back to its container.
    Quota { returned: PageSize },
    /// The process's tables are empty and unlocked.
    Zombie,
    /// The process is a zombie whose table structure is being retired.
    Retire,
}

/// Where a container kill stands at the marked container it works on.
pub ghost enum ContainerKillStage {
    /// The kill descends into a child container, marks the container's root process, or moves on to its cpus.
    Walk,
    /// The kill works on the marked process `process` of the container at `stage`.
    Process { process: RwLockProcessPtr, stage: KillStage },
    /// The container owns neither children nor processes: its cpus move to the killer's container.
    Cpus,
    /// No cpu belongs to the container: its free pages move to the killer's container.
    Pages,
    /// The container has no free page left and is being retired.
    Retire,
}

/// Progress of a multi-step syscall owned by the write-locked thread.
#[allow(inconsistent_fields)]
pub ghost enum SyscallProgress {
    Mmap4k { range: VaRange4K, mapped: usize, directory: Mmap4kDirectory, phase: Mmap4kPhase },
    Unmap4k { range: VaRange4K, unmapped: usize, flushed: bool },
    /// IOMMU mapping of the caller's pages at `va_range` into its IOMMU table at `iova_range`; the first `mapped` pages are done.
    IommuMap4k { va_range: VaRange4K, iova_range: VaRange4K, mapped: usize, directory: Mmap4kDirectory },
    /// IOMMU unmapping of `iova_range`; the first `unmapped` pages are done, and `flushed` records the IOTLB flush.
    IommuUnmap4k { iova_range: VaRange4K, unmapped: usize, flushed: bool },
    /// Process creation before its range is shared into the child.
    NewProcess(NewProcessProgress),
    /// Container creation before its range is shared into the child container's root process.
    NewContainer(NewContainerProgress),
    /// Sharing the first `shared` pages of `source_range` into `target_range` for `origin`.
    Share4k { source_range: VaRange4K, target_range: VaRange4K, shared: usize, origin: Share4kOrigin },
    /// A pages rendezvous with `peer` before its checks, with both page tables locked as `tables`, or
    /// after its page tables are released with the recorded result.
    IpcPages { source_range: VaRange4K, target_range: VaRange4K, peer: RwLockThreadPtr, tables: IpcPagesTables, released: Option<RetValueType> },
    /// An endpoint rendezvous whose `peer` is in transit; the caller sends when `caller_sends`, and its
    /// own payload names descriptor `payload_index`.
    IpcEndpoint { peer: RwLockThreadPtr, caller_sends: bool, payload_index: EndpointIdx },
    /// Thread creation that starts the new thread with `regs` and the optional endpoint at `endpoint_index`.
    NewThread { regs: Registers, endpoint_index: Option<EndpointIdx> },
    /// Endpoint creation that installs the new endpoint at descriptor `slot`.
    NewEndpoint { slot: EndpointIdx },
    /// Thread exit that has released every descriptor below `next`.
    ThreadExit { next: EndpointIdx },
    /// Exit of a process's last thread while its page table is write-locked: 4k leaves are being unmapped,
    /// and `flushed` records that the released translations are gone from every cpu.
    ThreadExitReclaim { flushed: bool },
    /// Exit of a process's last thread after the thread's and the process's quota of size `returned` and of every
    /// smaller size went back to their container.
    ThreadExitQuota { returned: PageSize },

    /// Exit of a process's last thread after its page table is empty and unlocked, before the thread is destroyed.
    ThreadExitZombie,
    /// Kill of a child's subtree while the killer works on the marked process `process`.
    KillProcess { process: RwLockProcessPtr, stage: KillStage },
    /// Kill of a child container's subtree while the killer works on the marked container `container`.
    KillContainer { container: RwLockContainerPtr, stage: ContainerKillStage },
}

/// The peer of the IPC rendezvous that `progress` records in flight.
pub open spec fn progress_peer_of(progress: Option<SyscallProgress>) -> Option<RwLockThreadPtr> {
    match progress {
        Some(SyscallProgress::IpcPages { peer, .. }) => Some(peer),
        Some(SyscallProgress::IpcEndpoint { peer, .. }) => Some(peer),
        Some(SyscallProgress::Share4k { origin: Share4kOrigin::IpcPages { peer }, .. }) => Some(peer),
        _ => None,
    }
}

pub struct Thread {
    pub state: ThreadState,
    /// The upstream caller currently served by this thread, if any.
    pub caller: Option<RwLockThreadPtr>,
    /// The downstream callee while this thread is waiting for a reply.
    pub callee: Option<RwLockThreadPtr>,
    /// Position in the IPC call chain: one more than its caller's.
    pub call_depth: Ghost<nat>,

    pub owning_container: RwLockContainerPtr,
    pub container_depth: usize,
    pub scheduler_linkedlist_node: ExternalNode<RwLockThreadPtr>,
    /// The cpu this thread last ran on; a cross-container wakeup queues it on that cpu's shard.
    pub last_cpu: CpuId,

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

    /// Some only while this thread is write-locked by its running syscall.
    pub syscall_progress: Ghost<Option<SyscallProgress>>,
}

/// Proof-only state of a thread lock; kernel-internal and not projected to the user view.
pub ghost struct ThreadGhost {
    /// For a dangling thread, the live thread of its container at the end of its call chain that owes the chain a reply.
    pub chain_end: Option<RwLockThreadPtr>,
    /// Set once by the exit of its process's last thread, after the process's tables were released; never cleared.
    pub exited: bool,
}

pub type ThreadRwLock = RwLock<Thread, (), ThreadGhost, THREAD_HAS_KILL_STATE>;
pub type ThreadLockedMap = LockedMap<RwLockThreadPtr, Thread, (), ThreadGhost, THREAD_HAS_KILL_STATE>;

pub ghost struct ThreadU {
    pub lock_state: LockStateU,
    pub state: ThreadState,
    pub caller: Option<RwLockThreadPtr>,
    pub callee: Option<RwLockThreadPtr>,
    pub owning_container: RwLockContainerPtr,
    pub owning_proc: RwLockProcessPtr,
    pub last_cpu: CpuId,
    pub quota_4k: usize,
    pub quota_2m: usize,
    pub quota_1g: usize,
    pub endpoint_descriptors: Seq<Option<RwLockEndpointPtr>>,
    pub blocking_endpoint_ptr: Option<RwLockEndpointPtr>,
    pub ipc_payload: IPCPayLoad,
    pub error_code: Option<RetValueType>,
    pub trap_frame: Option<Registers>,
    pub syscall_progress: Option<SyscallProgress>,
    pub killed: bool,
}

impl UserViewHasKillState for ThreadU {
    open spec fn killed(&self) -> bool { self.killed }
}

impl Thread {
    /// Boot-only fresh root thread: RUNNING on CPU 0 with endpoint 0 set. The
    /// caller retypes it into its page before taking any intrusive node.
    pub fn new_boot_root(owning_container: RwLockContainerPtr, owning_proc: RwLockProcessPtr, proc_pagetable_ptr: RwLockPageTableRoot, endpoint_ptr: RwLockEndpointPtr) -> (ret: Self)
        ensures
            ret.inv(),
            ret.state == (ThreadState::RUNNING { cpu_id: 0 }),
            ret.last_cpu == 0,
            ret.current_lock_major() == THREAD_LOCK_MAJOR,
            ret.owning_container == owning_container,
            ret.container_depth == 0,
            ret.owning_proc == owning_proc,
            ret.process_depth == 0,
            ret.proc_pagetable_ptr == proc_pagetable_ptr,
            ret.upper_container_seq.view() == Seq::<RwLockContainerPtr>::empty(),
            ret.endpoint_descriptors.spec_index(0) == Some(endpoint_ptr),
            forall|endpoint_index: EndpointIdx|
                #![trigger ret.endpoint_descriptors.spec_index(endpoint_index)]
                edp_idx_valid(endpoint_index) && endpoint_index != 0 ==> ret.endpoint_descriptors.spec_index(endpoint_index) is None,
            ret.ipc_payload is Empty,
            ret.error_code is None,
            ret.caller is None,
            ret.callee is None,
            ret.trap_frame.is_none(),
            ret.blocking_endpoint_ptr is None,
            ret.blocking_endpoint_index is None,
            ret.free_quota_pending_clean(),
            ret.syscall_progress.view() is None,
            ret.temp_alloc_clean(),
            ret.quota_4k == 0,
            ret.quota_2m == 0,
            ret.quota_1g == 0,
            ret.endpoint_linkedlist_node.is_init(),
            ret.scheduler_linkedlist_node.is_init(),
            ret.proc_linkedlist_node.is_init(),
    {
        let mut thread = Self::new_fresh(owning_container, 0, owning_proc, 0, proc_pagetable_ptr, Ghost(Seq::empty()));
        thread.endpoint_descriptors.set(0, Some(endpoint_ptr));
        thread
    }

    pub open spec fn non_ipc_fields_unchanged(&self, other: &Self) -> bool {
        &&& self.owning_container == other.owning_container
        &&& self.call_depth == other.call_depth
        &&& self.syscall_progress == other.syscall_progress
        &&& self.container_depth == other.container_depth
        &&& self.scheduler_linkedlist_node.addr() == other.scheduler_linkedlist_node.addr()
        &&& self.last_cpu == other.last_cpu
        &&& self.owning_proc == other.owning_proc
        &&& self.process_depth == other.process_depth
        &&& self.proc_pagetable_ptr == other.proc_pagetable_ptr
        &&& self.proc_linkedlist_node.addr() == other.proc_linkedlist_node.addr()
        &&& self.proc_linkedlist_node.is_init() == other.proc_linkedlist_node.is_init()
        &&& self.quota_4k == other.quota_4k
        &&& self.quota_2m == other.quota_2m
        &&& self.quota_1g == other.quota_1g
        &&& self.temp_alloc_cache_4k == other.temp_alloc_cache_4k
        &&& self.temp_alloc_cache_2m == other.temp_alloc_cache_2m
        &&& self.temp_alloc_cache_1g == other.temp_alloc_cache_1g
        &&& self.endpoint_descriptors == other.endpoint_descriptors
        &&& self.endpoint_linkedlist_node.addr() == other.endpoint_linkedlist_node.addr()
        &&& self.upper_container_seq == other.upper_container_seq
        &&& self.free_quota_pending_fields_unchanged(other)
    }

    pub open spec fn free_quota_pending_fields_unchanged(&self, other: &Self) -> bool {
        &&& self.direct_free_quota_pending_4k == other.direct_free_quota_pending_4k
        &&& self.direct_free_quota_pending_2m == other.direct_free_quota_pending_2m
        &&& self.direct_free_quota_pending_1g == other.direct_free_quota_pending_1g
        &&& self.indirect_free_quota_pending_4k == other.indirect_free_quota_pending_4k
        &&& self.indirect_free_quota_pending_2m == other.indirect_free_quota_pending_2m
        &&& self.indirect_free_quota_pending_1g == other.indirect_free_quota_pending_1g
    }

    pub open spec fn free_quota_pending_clean(&self) -> bool {
        &&& self.direct_free_quota_pending_4k.view() == 0
        &&& self.direct_free_quota_pending_2m.view() == 0
        &&& self.direct_free_quota_pending_1g.view() == 0
        &&& forall|i: int|
            #![trigger self.indirect_free_quota_pending_4k.view().spec_index(i)]
            0 <= i < self.indirect_free_quota_pending_4k.view().len() ==> self.indirect_free_quota_pending_4k.view().spec_index(i) == 0
        &&& forall|i: int|
            #![trigger self.indirect_free_quota_pending_2m.view().spec_index(i)]
            0 <= i < self.indirect_free_quota_pending_2m.view().len() ==> self.indirect_free_quota_pending_2m.view().spec_index(i) == 0
        &&& forall|i: int|
            #![trigger self.indirect_free_quota_pending_1g.view().spec_index(i)]
            0 <= i < self.indirect_free_quota_pending_1g.view().len() ==> self.indirect_free_quota_pending_1g.view().spec_index(i) == 0
    }

    /// Construct a fresh Thread for retype operations.
    /// State is RUNNING{cpu_id: 0} (not waiting, not SCHEDULED).
    /// All endpoint fields are None/empty, all pending quotas are 0,
    /// caller/callee are None, linkedlist nodes are init, trap_frame is None.
    pub fn new_fresh(owning_container: RwLockContainerPtr, container_depth: usize, owning_proc: RwLockProcessPtr, process_depth: usize, proc_pagetable_ptr: RwLockPageTableRoot, upper_container_seq: Ghost<Seq<RwLockContainerPtr>>) -> (ret: Self)
        requires
            upper_container_seq.view().len() == container_depth,
        ensures
            ret.inv(),
            ret.state == (ThreadState::RUNNING { cpu_id: 0 }),
            ret.last_cpu == 0,
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
            forall|edp_index: EndpointIdx|
                #![trigger ret.endpoint_descriptors.spec_index(edp_index)]
                edp_idx_valid(edp_index) ==> ret.endpoint_descriptors.spec_index(edp_index) is None,
            ret.endpoint_descriptors.view() == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| None),
            ret.ipc_payload is Empty,
            ret.error_code is None,
            ret.trap_frame.is_none(),
            ret.free_quota_pending_clean(),
            ret.syscall_progress.view() is None,
            ret.temp_alloc_clean(),
            ret.quota_4k == 0,
            ret.quota_2m == 0,
            ret.quota_1g == 0,
    {
        let mut endpoint_descriptors: Array<Option<RwLockEndpointPtr>, MAX_NUM_ENDPOINT_DESCRIPTORS> = Array::new();
        endpoint_descriptors.init2none();
        proof { assert_seqs_equal!(endpoint_descriptors.view() == Seq::new(MAX_NUM_ENDPOINT_DESCRIPTORS as nat, |i: int| None), i => {}); }
        let ret = Self {
            state: ThreadState::RUNNING { cpu_id: 0 }, caller: None, callee: None, call_depth: Ghost(0), owning_container, container_depth,
            scheduler_linkedlist_node: ExternalNode::new(0), last_cpu: 0, owning_proc, process_depth, proc_pagetable_ptr,
            proc_linkedlist_node: ExternalNode::new(0), quota_4k: 0, quota_2m: 0, quota_1g: 0, temp_alloc_cache_4k: Ghost(Set::empty()),
            temp_alloc_cache_2m: Ghost(Set::empty()), temp_alloc_cache_1g: Ghost(Set::empty()), endpoint_descriptors, blocking_endpoint_ptr: None,
            blocking_endpoint_index: None, endpoint_linkedlist_node: ExternalNode::new(0), ipc_payload: IPCPayLoad::Empty, error_code: None,
            trap_frame: TrapFrameOption::zeroed_none(), upper_container_seq, direct_free_quota_pending_4k: Ghost(0), direct_free_quota_pending_2m: Ghost(0),
            direct_free_quota_pending_1g: Ghost(0), indirect_free_quota_pending_4k: Ghost(Seq::new(container_depth as nat, |i: int| 0usize)),
            indirect_free_quota_pending_2m: Ghost(Seq::new(container_depth as nat, |i: int| 0usize)),
            indirect_free_quota_pending_1g: Ghost(Seq::new(container_depth as nat, |i: int| 0usize)), syscall_progress: Ghost(None),
        };
        ret
    }

    /// In-place RUNNING -> SCHEDULED transition for a freshly retyped thread. Both
    /// intrusive nodes are taken here so their addresses are the in-page ones.
    pub fn fresh_to_scheduled(&mut self, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, initial_regs: &Registers) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>, usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state is RUNNING,
            old(self).scheduler_linkedlist_node.is_init(),
            old(self).proc_linkedlist_node.is_init(),
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).inv(),
            *final(self) == (Thread {
                state: final(self).state, last_cpu: final(self).last_cpu, trap_frame: final(self).trap_frame,
                scheduler_linkedlist_node: final(self).scheduler_linkedlist_node, proc_linkedlist_node: final(self).proc_linkedlist_node,
                ..*old(self)
            }),
            final(self).state == (ThreadState::SCHEDULED { cpu_id }),
            final(self).last_cpu == cpu_id,
            final(self).current_lock_major() == THREAD_SCHEDULED_LOCK_MAJOR,
            final(self).trap_frame.is_some(),
            *final(self).trap_frame.get_some_0() == *initial_regs,
            !final(self).scheduler_linkedlist_node.is_init(),
            !final(self).proc_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node.addr() == old(self).scheduler_linkedlist_node.addr(),
            final(self).proc_linkedlist_node.addr() == old(self).proc_linkedlist_node.addr(),
            ret.0 == final(self).scheduler_linkedlist_node.addr(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == thread_ptr,
            ret.2 == final(self).proc_linkedlist_node.addr(),
            ret.3.view().is_init(),
            ret.3.view().addr() == ret.2,
            ret.3.view().value().view() == thread_ptr,
    {
        let (sched_node_addr, mut sched_node_perm) = self.scheduler_linkedlist_node.take();
        node_update_value(sched_node_addr, &mut sched_node_perm, thread_ptr);
        let (process_node_addr, mut process_node_perm) = self.proc_linkedlist_node.take();
        node_update_value(process_node_addr, &mut process_node_perm, thread_ptr);
        self.trap_frame.set_self(initial_regs);
        self.state = ThreadState::SCHEDULED { cpu_id };
        self.last_cpu = cpu_id;
        (sched_node_addr, sched_node_perm, process_node_addr, process_node_perm)
    }
}

impl Thread {
    pub fn consume_staged_4k(&mut self, page_ptr: PagePtr)
        requires
            old(self).temp_alloc_cache_4k.view().contains(page_ptr),
            old(self).quota_4k >= 1,
        ensures
            old(self).inv() ==> final(self).inv(),
            *final(self) == (Thread { quota_4k: final(self).quota_4k, temp_alloc_cache_4k: final(self).temp_alloc_cache_4k, ..*old(self) }),
            final(self).temp_alloc_cache_4k.view() == old(self).temp_alloc_cache_4k.view().remove(page_ptr),
            final(self).temp_alloc_cache_4k.view().len() == old(self).temp_alloc_cache_4k.view().len() - 1,
            final(self).quota_4k == old(self).quota_4k - 1,
    {
        let ghost old_cache = self.temp_alloc_cache_4k.view();
        self.temp_alloc_cache_4k = Ghost(old_cache.remove(page_ptr));
        self.quota_4k = self.quota_4k - 1;
    }

    pub fn running_to_scheduled(&mut self, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, pt_regs: &Registers) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state is RUNNING,
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).inv(),
            *final(self) == (Thread { state: final(self).state, error_code: final(self).error_code, trap_frame: final(self).trap_frame, scheduler_linkedlist_node: final(self).scheduler_linkedlist_node, ..*old(self) }),
            final(self).scheduler_linkedlist_node.addr() == old(self).scheduler_linkedlist_node.addr(),
            final(self).error_code is None,
            final(self).state == (ThreadState::SCHEDULED { cpu_id }),
            final(self).trap_frame.is_some(),
            *final(self).trap_frame.get_some_0() == *pt_regs,
            ret.0 == final(self).scheduler_linkedlist_node.addr(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == thread_ptr,
    {
        self.trap_frame.set_self(pt_regs);
        let (node_addr, mut node_perm) = self.scheduler_linkedlist_node.take();
        node_update_value(node_addr, &mut node_perm, thread_ptr);
        self.state = ThreadState::SCHEDULED { cpu_id };
        (node_addr, node_perm)
    }

    pub fn scheduled_to_running(&mut self, cpu_id: CpuId, node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>, pt_regs: &mut Registers) -> (ret: Option<RetValueType>)
        requires
            old(self).inv(),
            old(self).state is SCHEDULED,
            index_valid(NUM_CPUS, cpu_id),
            node_perm.view().is_init(),
            node_perm.view().addr() == old(self).scheduler_linkedlist_node.addr(),
        ensures
            final(self).inv(),
            *final(self) == (Thread {
                state: final(self).state, error_code: final(self).error_code, trap_frame: final(self).trap_frame, scheduler_linkedlist_node: final(self).scheduler_linkedlist_node,
                last_cpu: cpu_id, ..*old(self)
            }),
            final(self).scheduler_linkedlist_node.addr() == old(self).scheduler_linkedlist_node.addr(),
            final(self).error_code is None,
            ret == old(self).error_code,
            final(self).state == (ThreadState::RUNNING { cpu_id }),
            final(self).trap_frame.is_none(),
            *final(pt_regs) == *old(self).trap_frame.get_some_0(),
    {
        self.scheduler_linkedlist_node.put(node_perm);
        self.trap_frame.set_dst(pt_regs);
        self.trap_frame.set_to_none();
        let ret = self.error_code;
        self.error_code = None;
        self.state = ThreadState::RUNNING { cpu_id };
        self.last_cpu = cpu_id;
        ret
    }

    /// Retargets a queued thread to shard `cpu_id`; its scheduler node stays with the run queue.
    pub fn move_scheduled(&mut self, cpu_id: CpuId)
        requires
            old(self).inv(),
            old(self).state is SCHEDULED,
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).inv(),
            *final(self) == (Thread { state: ThreadState::SCHEDULED { cpu_id }, ..*old(self) }),
    { self.state = ThreadState::SCHEDULED { cpu_id }; }

    /// Move the running thread into an endpoint wait queue and hand its
    /// intrusive endpoint node to the queue owner.
    pub fn block_on_endpoint(&mut self, thread_ptr: RwLockThreadPtr, endpoint_ptr: RwLockEndpointPtr, endpoint_index: EndpointIdx, waiting_state: ThreadState, payload: IPCPayLoad, pt_regs: &Registers) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state is RUNNING,
            waiting_state.is_endpoint_waiting(),
            waiting_state is RECEIVING_CALL ==> old(self).caller is None,
            payload.wf(),
            edp_idx_valid(endpoint_index),
            old(self).endpoint_descriptors.spec_index(endpoint_index) == Some(endpoint_ptr),
        ensures
            final(self).inv(),
            final(self).non_ipc_fields_unchanged(old(self)),
            *final(self) == (Thread {
                state: waiting_state, blocking_endpoint_ptr: Some(endpoint_ptr), blocking_endpoint_index: Some(endpoint_index), ipc_payload: payload,
                trap_frame: final(self).trap_frame, endpoint_linkedlist_node: final(self).endpoint_linkedlist_node, ..*old(self)
            }),
            !final(self).endpoint_linkedlist_node.is_init(),
            final(self).state == waiting_state,
            final(self).blocking_endpoint_ptr == Some(endpoint_ptr),
            final(self).blocking_endpoint_index == Some(endpoint_index),
            final(self).ipc_payload =~= payload,
            final(self).trap_frame.is_some(),
            final(self).trap_frame.get_some_0() =~= pt_regs,
            final(self).caller == old(self).caller,
            final(self).syscall_progress == old(self).syscall_progress,
            final(self).callee == old(self).callee,
            final(self).error_code == old(self).error_code,
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
    pub fn endpoint_waiter_to_scheduled(&mut self, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, result: RetValueType, endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state.is_endpoint_waiting(),
            index_valid(NUM_CPUS, cpu_id),
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr() == old(self).endpoint_linkedlist_node.addr(),
            endpoint_node_perm.view().value().view() == thread_ptr,
        ensures
            final(self).inv(),
            final(self).non_ipc_fields_unchanged(old(self)),
            final(self).state == (ThreadState::SCHEDULED { cpu_id }),
            final(self).blocking_endpoint_ptr is None,
            final(self).blocking_endpoint_index is None,
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node.is_init() == false,
            final(self).error_code == Some(result),
            final(self).ipc_payload is Empty,
            final(self).trap_frame == old(self).trap_frame,
            final(self).proc_linkedlist_node == old(self).proc_linkedlist_node,
            final(self).caller == old(self).caller,
            final(self).syscall_progress == old(self).syscall_progress,
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
        self.state = ThreadState::SCHEDULED { cpu_id };
        (node_addr, node_perm)
    }

    /// Remove a matched sender/receiver from its endpoint into transit with the rendezvous thread `partner`, recording whether it was sending.
    pub fn endpoint_waiter_to_ipc_transit(&mut self, thread_ptr: RwLockThreadPtr, partner: RwLockThreadPtr, endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
        requires
            old(self).inv(),
            old(self).state is SENDING || old(self).state is RECEIVING,
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr() == old(self).endpoint_linkedlist_node.addr(),
            endpoint_node_perm.view().value().view() == thread_ptr,
        ensures
            final(self).inv(),
            final(self).non_ipc_fields_unchanged(old(self)),
            final(self).state == (ThreadState::IPC_TRANSIT { partner, wait: if old(self).state is SENDING { IpcWait::Send } else { IpcWait::Receive } }),
            final(self).blocking_endpoint_ptr is None,
            final(self).blocking_endpoint_index is None,
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node == old(self).scheduler_linkedlist_node,
            final(self).ipc_payload == old(self).ipc_payload,
            final(self).error_code == old(self).error_code,
            final(self).trap_frame == old(self).trap_frame,
            final(self).caller == old(self).caller,
            final(self).syscall_progress == old(self).syscall_progress,
            final(self).callee == old(self).callee,
    {
        let wait = match self.state { ThreadState::SENDING => IpcWait::Send, _ => IpcWait::Receive };
        self.endpoint_linkedlist_node.put(endpoint_node_perm);
        self.blocking_endpoint_ptr = None;
        self.blocking_endpoint_index = None;
        self.state = ThreadState::IPC_TRANSIT { partner, wait };
    }

    /// Prepare a peer in IPC transit for its scheduler with the rendezvous result that the current thread also receives.
    pub fn ipc_transit_to_scheduled(&mut self, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, result: RetValueType) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state is IPC_TRANSIT,
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).inv(),
            final(self).non_ipc_fields_unchanged(old(self)),
            final(self).state == (ThreadState::SCHEDULED { cpu_id }),
            final(self).blocking_endpoint_ptr is None,
            final(self).blocking_endpoint_index is None,
            final(self).endpoint_linkedlist_node == old(self).endpoint_linkedlist_node,
            final(self).scheduler_linkedlist_node.is_init() == false,
            final(self).error_code == Some(result),
            final(self).ipc_payload is Empty,
            final(self).trap_frame == old(self).trap_frame,
            final(self).caller == old(self).caller,
            final(self).syscall_progress == old(self).syscall_progress,
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
        self.state = ThreadState::SCHEDULED { cpu_id };
        (node_addr, node_perm)
    }

    /// A queued caller has met a receive-call thread. It leaves the endpoint
    /// but stays blocked until its callee replies.
    pub fn endpoint_caller_to_waiting_reply(&mut self, thread_ptr: RwLockThreadPtr, callee_ptr: RwLockThreadPtr, endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
        requires
            old(self).inv(),
            old(self).state is CALLING,
            thread_ptr != callee_ptr,
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr() == old(self).endpoint_linkedlist_node.addr(),
            endpoint_node_perm.view().value().view() == thread_ptr,
        ensures
            final(self).inv(),
            final(self).non_ipc_fields_unchanged(old(self)),
            *final(self) == (Thread {
                state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), blocking_endpoint_ptr: None, blocking_endpoint_index: None,
                endpoint_linkedlist_node: final(self).endpoint_linkedlist_node, ..*old(self)
            }),
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).endpoint_linkedlist_node.addr() == old(self).endpoint_linkedlist_node.addr(),
    {
        self.endpoint_linkedlist_node.put(endpoint_node_perm);
        self.blocking_endpoint_ptr = None;
        self.blocking_endpoint_index = None;
        self.callee = Some(callee_ptr);
        self.state = ThreadState::WAITING_REPLY;
    }

    /// The currently running receive-call thread accepts a queued caller.
    pub fn accept_queued_caller(&mut self, caller_ptr: RwLockThreadPtr, self_ptr: RwLockThreadPtr, caller_depth: Ghost<nat>)
        requires
            old(self).inv(),
            old(self).state is RUNNING,
            old(self).caller is None,
            old(self).callee is None,
            caller_ptr != self_ptr,
        ensures
            final(self).inv(),
            *final(self) == (Thread { caller: Some(caller_ptr), call_depth: Ghost(caller_depth.view() + 1), ..*old(self) }),
    {
        self.caller = Some(caller_ptr);
        self.call_depth = Ghost(caller_depth.view() + 1);
    }

    /// The running caller waits for a reply while a previously blocked
    /// receive-call thread takes over its CPU.
    pub fn running_caller_to_waiting_reply(&mut self, callee_ptr: RwLockThreadPtr, self_ptr: RwLockThreadPtr, pt_regs: &Registers)
        requires
            old(self).inv(),
            old(self).state is RUNNING,
            old(self).callee is None,
            callee_ptr != self_ptr,
        ensures
            final(self).inv(),
            *final(self) == (Thread { state: ThreadState::WAITING_REPLY, callee: Some(callee_ptr), trap_frame: final(self).trap_frame, ..*old(self) }),
            final(self).trap_frame.is_some(),
            final(self).trap_frame.get_some_0() =~= pt_regs,
    {
        self.trap_frame.set_self(pt_regs);
        self.callee = Some(callee_ptr);
        self.state = ThreadState::WAITING_REPLY;
    }

    /// A blocked receive-call thread becomes the running callee and restores
    /// the register image it saved when entering the endpoint.
    pub fn endpoint_receiver_to_running(&mut self, thread_ptr: RwLockThreadPtr, caller_ptr: RwLockThreadPtr, caller_depth: Ghost<nat>, cpu_id: CpuId, endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>, pt_regs: &mut Registers)
        requires
            old(self).inv(),
            old(self).state is RECEIVING_CALL,
            old(self).caller is None,
            old(self).callee is None,
            thread_ptr != caller_ptr,
            index_valid(NUM_CPUS, cpu_id),
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr() == old(self).endpoint_linkedlist_node.addr(),
            endpoint_node_perm.view().value().view() == thread_ptr,
        ensures
            final(self).inv(),
            *final(self) == (Thread {
                state: ThreadState::RUNNING { cpu_id }, caller: Some(caller_ptr), call_depth: Ghost(caller_depth.view() + 1), blocking_endpoint_ptr: None,
                blocking_endpoint_index: None, endpoint_linkedlist_node: final(self).endpoint_linkedlist_node, last_cpu: cpu_id, trap_frame: final(self).trap_frame, ..*old(self)
            }),
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).endpoint_linkedlist_node.addr() == old(self).endpoint_linkedlist_node.addr(),
            final(self).trap_frame.is_none(),
            *final(pt_regs) =~= *old(self).trap_frame.get_some_0(),
    {
        self.endpoint_linkedlist_node.put(endpoint_node_perm);
        self.trap_frame.set_dst(pt_regs);
        self.trap_frame.set_to_none();
        self.blocking_endpoint_ptr = None;
        self.blocking_endpoint_index = None;
        self.caller = Some(caller_ptr);
        self.call_depth = Ghost(caller_depth.view() + 1);
        self.last_cpu = cpu_id;
        self.state = ThreadState::RUNNING { cpu_id };
    }

    /// A caller waiting for its reply takes over the replying callee's CPU and restores the register image it
    /// saved when it called.
    pub fn waiting_reply_to_running(&mut self, cpu_id: CpuId, pt_regs: &mut Registers)
        requires
            old(self).inv(),
            old(self).state is WAITING_REPLY,
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).inv(),
            *final(self) == (Thread { state: ThreadState::RUNNING { cpu_id }, callee: None, last_cpu: cpu_id, trap_frame: final(self).trap_frame, ..*old(self) }),
            final(self).trap_frame.is_none(),
            *final(pt_regs) =~= *old(self).trap_frame.get_some_0(),
    {
        self.trap_frame.set_dst(pt_regs);
        self.trap_frame.set_to_none();
        self.callee = None;
        self.last_cpu = cpu_id;
        self.state = ThreadState::RUNNING { cpu_id };
    }

    /// A caller waiting for its reply is woken on shard `cpu_id` with `result` because its callee exited.
    pub fn waiting_reply_to_scheduled(&mut self, thread_ptr: RwLockThreadPtr, cpu_id: CpuId, result: RetValueType) -> (ret: (usize, Tracked<PointsTo<Node<RwLockThreadPtr>>>))
        requires
            old(self).inv(),
            old(self).state is WAITING_REPLY,
            index_valid(NUM_CPUS, cpu_id),
        ensures
            final(self).inv(),
            *final(self) == (Thread {
                state: ThreadState::SCHEDULED { cpu_id }, callee: None, error_code: Some(result), scheduler_linkedlist_node: final(self).scheduler_linkedlist_node, ..*old(self)
            }),
            !final(self).scheduler_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node.addr() == old(self).scheduler_linkedlist_node.addr(),
            ret.0 == final(self).scheduler_linkedlist_node.addr(),
            ret.1.view().is_init(),
            ret.1.view().addr() == ret.0,
            ret.1.view().value().view() == thread_ptr,
    {
        let (node_addr, mut node_perm) = self.scheduler_linkedlist_node.take();
        node_update_value(node_addr, &mut node_perm, thread_ptr);
        self.callee = None;
        self.error_code = Some(result);
        self.state = ThreadState::SCHEDULED { cpu_id };
        (node_addr, node_perm)
    }

    /// The running callee drops its recorded caller after replying to it; a killed callee, or a callee being turned into a
    /// dangling thread, drops it once the caller is woken or reclaimed.
    pub fn release_caller(&mut self)
        requires
            old(self).inv(),
            old(self).state is RUNNING || old(self).state is KILLED || old(self).state is WAITING_REPLY,
            old(self).caller is Some,
        ensures
            final(self).inv(),
            *final(self) == (Thread { caller: None, ..*old(self) }),
    {
        self.caller = None;
    }

    /// A killer took this thread off its scheduler shard.
    pub fn scheduled_to_killed(&mut self, scheduler_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
        requires
            old(self).inv(),
            old(self).state is SCHEDULED,
            scheduler_node_perm.view().is_init(),
            scheduler_node_perm.view().addr() == old(self).scheduler_linkedlist_node.addr(),
        ensures
            final(self).inv(),
            *final(self) == (Thread { state: ThreadState::KILLED, error_code: None, scheduler_linkedlist_node: final(self).scheduler_linkedlist_node, ..*old(self) }),
            final(self).scheduler_linkedlist_node.is_init(),
            final(self).scheduler_linkedlist_node.addr() == old(self).scheduler_linkedlist_node.addr(),
    {
        self.scheduler_linkedlist_node.put(scheduler_node_perm);
        self.error_code = None;
        self.state = ThreadState::KILLED;
    }

    /// A killer took this thread out of its blocking endpoint's queue.
    pub fn endpoint_waiter_to_killed(&mut self, endpoint_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
        requires
            old(self).inv(),
            old(self).state.is_endpoint_waiting(),
            endpoint_node_perm.view().is_init(),
            endpoint_node_perm.view().addr() == old(self).endpoint_linkedlist_node.addr(),
        ensures
            final(self).inv(),
            *final(self) == (Thread {
                state: ThreadState::KILLED, blocking_endpoint_ptr: None, blocking_endpoint_index: None, endpoint_linkedlist_node: final(self).endpoint_linkedlist_node, ..*old(self)
            }),
            final(self).endpoint_linkedlist_node.is_init(),
            final(self).endpoint_linkedlist_node.addr() == old(self).endpoint_linkedlist_node.addr(),
    {
        self.endpoint_linkedlist_node.put(endpoint_node_perm);
        self.blocking_endpoint_ptr = None;
        self.blocking_endpoint_index = None;
        self.state = ThreadState::KILLED;
    }

    /// A killer evicted this thread from its CPU.
    pub fn running_to_killed(&mut self)
        requires
            old(self).inv(),
            old(self).state is RUNNING,
        ensures
            final(self).inv(),
            *final(self) == (Thread { state: ThreadState::KILLED, ..*old(self) }),
    {
        self.state = ThreadState::KILLED;
    }

    /// A killed thread waiting for a reply leaves its process as a dangling thread that its callee reclaims: its quota went back
    /// to the process and its process node returns to the thread page; it keeps its descriptors and its caller.
    pub fn waiting_reply_to_dangling(&mut self, proc_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
        requires
            old(self).inv(),
            old(self).state is WAITING_REPLY,
            old(self).temp_alloc_clean(),
            !old(self).proc_linkedlist_node.is_init(),
            proc_node_perm.view().is_init(),
            proc_node_perm.view().addr() == old(self).proc_linkedlist_node.addr(),
        ensures
            final(self).inv(),
            *final(self) == (Thread { state: ThreadState::DANGLING, quota_4k: 0, quota_2m: 0, quota_1g: 0, proc_linkedlist_node: final(self).proc_linkedlist_node, ..*old(self) }),
            final(self).proc_linkedlist_node.is_init(),
            final(self).proc_linkedlist_node.addr() == old(self).proc_linkedlist_node.addr(),
    {
        self.proc_linkedlist_node.put(proc_node_perm);
        self.quota_4k = 0;
        self.quota_2m = 0;
        self.quota_1g = 0;
        self.state = ThreadState::DANGLING;
    }

    /// A killed dangling thread being destroyed hands back the process node it holds.
    pub fn take_proc_node(&mut self) -> (ret: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
        requires
            old(self).inv(),
            old(self).state is KILLED,
            old(self).proc_linkedlist_node.is_init(),
        ensures
            final(self).inv(),
            *final(self) == (Thread { proc_linkedlist_node: final(self).proc_linkedlist_node, ..*old(self) }),
            !final(self).proc_linkedlist_node.is_init(),
            final(self).proc_linkedlist_node.addr() == old(self).proc_linkedlist_node.addr(),
            ret.view().is_init(),
            ret.view().addr() == old(self).proc_linkedlist_node.addr(),
    {
        let (_node_addr, node_perm) = self.proc_linkedlist_node.take();
        node_perm
    }

    /// A killed thread leaving its process gives its quota to the process and takes back its process node.
    pub fn killed_leave_process(&mut self, proc_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>)
        requires
            old(self).inv(),
            old(self).state is KILLED,
            old(self).temp_alloc_clean(),
            !old(self).proc_linkedlist_node.is_init(),
            proc_node_perm.view().is_init(),
            proc_node_perm.view().addr() == old(self).proc_linkedlist_node.addr(),
        ensures
            final(self).inv(),
            *final(self) == (Thread { quota_4k: 0, quota_2m: 0, quota_1g: 0, proc_linkedlist_node: final(self).proc_linkedlist_node, ..*old(self) }),
            final(self).proc_linkedlist_node.is_init(),
            final(self).proc_linkedlist_node.addr() == old(self).proc_linkedlist_node.addr(),
    {
        self.proc_linkedlist_node.put(proc_node_perm);
        self.quota_4k = 0;
        self.quota_2m = 0;
        self.quota_1g = 0;
    }

    /// The callee reclaiming a dangling thread takes it over as a killed thread, and the dangling thread drops its callee.
    pub fn dangling_to_killed(&mut self)
        requires
            old(self).inv(),
            old(self).state is DANGLING,
        ensures
            final(self).inv(),
            *final(self) == (Thread { state: ThreadState::KILLED, callee: None, ..*old(self) }),
    {
        self.callee = None;
        self.state = ThreadState::KILLED;
    }
}

/// A killed caller's dangling thread has left its process and container and holds its own process node: it either waits for its
/// callee (DANGLING) or is being reclaimed by it (KILLED). A thread a killer marked is still linked into its process.
pub open spec fn thread_is_dangling(thread_lock: ThreadRwLock) -> bool {
    thread_lock.view().state is DANGLING || (thread_lock.view().state is KILLED && thread_lock.view().proc_linkedlist_node.is_init())
}

/// Free-quota pending counters must be zero unless the thread is write-locked.
/// Syscalls accumulate pending frees only under wlock; flushed before wunlock.
#[verifier::opaque]
pub open spec fn thread_free_quota_pending_empty_unless_wlocked(thread_map: ThreadLockedMap) -> bool {
    forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr).locking_thread()]
        thread_map.dom().contains(t_ptr) ==> !(thread_map.spec_index(t_ptr).locking_thread() is Write) ==> thread_map.spec_index(t_ptr).view().free_quota_pending_clean()
}

impl LockInvTrait for Thread {
    open spec fn inv(&self) -> bool {
        &&& self.endpoint_descriptors.wf()
        &&& self.ipc_payload.wf()
        &&& self.error_code is Some ==> self.state is SCHEDULED
        &&& self.state is RUNNING ==> self.trap_frame.is_none()
        &&& self.state is SCHEDULED ==> self.trap_frame.is_some()
        &&& self.state is SCHEDULED ==> index_valid(NUM_CPUS, self.state->SCHEDULED_cpu_id)
        &&& index_valid(NUM_CPUS, self.last_cpu)
        &&& (self.state.is_endpoint_waiting() || self.state is WAITING_REPLY || self.state is IPC_TRANSIT) ==> self.trap_frame.is_some()
        &&& self.state.is_endpoint_waiting() == self.blocking_endpoint_ptr is Some
        &&& self.state.is_endpoint_waiting() == self.blocking_endpoint_index is Some
        &&& self.state.is_endpoint_waiting() ==> edp_idx_valid(self.blocking_endpoint_index.unwrap())
        &&& self.state.is_endpoint_waiting() ==> self.endpoint_descriptors.spec_index(self.blocking_endpoint_index.unwrap()) is Some
        &&& self.state.is_endpoint_waiting() ==> self.endpoint_descriptors.spec_index(self.blocking_endpoint_index.unwrap()).unwrap() == self.blocking_endpoint_ptr.unwrap()
        &&& self.state.is_endpoint_waiting() == !self.endpoint_linkedlist_node.is_init()
        &&& self.state is SCHEDULED == !self.scheduler_linkedlist_node.is_init()
        &&& self.state.is_reply_waiting() == (self.callee is Some)
        &&& self.state is DANGLING ==> self.quota_4k == 0 && self.quota_2m == 0 && self.quota_1g == 0 && self.proc_linkedlist_node.is_init()
        &&& self.state is RECEIVING_CALL ==> self.caller is None
        &&& self.upper_container_seq.view().len() == self.container_depth
        &&& self.upper_container_seq.view().len() == self.indirect_free_quota_pending_4k.view().len()
        &&& self.upper_container_seq.view().len() == self.indirect_free_quota_pending_2m.view().len()
        &&& self.upper_container_seq.view().len() == self.indirect_free_quota_pending_1g.view().len()
        &&& self.quota_within_bound()
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
    thread_lock.view().quota_4k as int - thread_lock.view().temp_alloc_cache_4k.view().len() as int
}

pub open spec fn thread_effective_quota_2m(thread_lock: ThreadRwLock) -> int {
    thread_lock.view().quota_2m as int - thread_lock.view().temp_alloc_cache_2m.view().len() as int
}

pub open spec fn thread_effective_quota_1g(thread_lock: ThreadRwLock) -> int {
    thread_lock.view().quota_1g as int - thread_lock.view().temp_alloc_cache_1g.view().len() as int
}

#[verifier::opaque]
pub open spec fn thread_temp_alloc_empty_unless_wlocked(thread_map: ThreadLockedMap) -> bool {
    forall|t_ptr: RwLockThreadPtr|
        #![trigger thread_map.spec_index(t_ptr).locking_thread()]
        thread_map.dom().contains(t_ptr) ==> !(thread_map.spec_index(t_ptr).locking_thread() is Write) ==> thread_map.spec_index(t_ptr).view().temp_alloc_clean()
}

#[derive(Clone, Copy)]
#[allow(inconsistent_fields)]
pub enum IPCPayLoad {
    Message { va: VAddr, len: usize },
    Pages { va_range: VaRange4K },
    Endpoint { endpoint_index: EndpointIdx },
    Cpu { cpu_id: CpuId },
    ReceiveCpu,
    Pci { bus: u8, dev: u8, fun: u8 },
    Usize { value: usize },
    // TODO @Xiangdong add a `PageFault { vaddr: VAddr }` payload when adding demand paging
    Empty,
}

impl IPCPayLoad {
    pub open spec fn wf(&self) -> bool {
        match self {
            IPCPayLoad::Pages { va_range } => va_range.wf(),
            IPCPayLoad::Cpu { cpu_id } => index_valid(NUM_CPUS, *cpu_id),
            IPCPayLoad::Endpoint { endpoint_index } => edp_idx_valid(*endpoint_index),
            IPCPayLoad::Pci { bus, dev, fun } => pci_bdf_valid(*bus as usize, *dev as usize, *fun as usize),
            _ => true,
        }
    }
}
impl LockMajorTrait for Thread {
    open spec fn lock_major_1(&self) -> LockMajorId { THREAD_LOCK_MAJOR }
    open spec fn lock_major_2(&self) -> LockMajorId { THREAD_BLOCKED_LOCK_MAJOR }
    open spec fn lock_major_3(&self) -> LockMajorId { THREAD_SCHEDULED_LOCK_MAJOR }
    open spec fn lock_major_default(&self) -> LockMajorId { if self.state is KILLED { THREAD_KILLED_LOCK_MAJOR } else { THREAD_IPC_TRANSIT_LOCK_MAJOR } }
    open spec fn lock_major_1_predicate(&self) -> bool { self.state is RUNNING }
    open spec fn lock_major_2_predicate(&self) -> bool { self.state.is_endpoint_waiting() || self.state.is_reply_waiting() }
    open spec fn lock_major_3_predicate(&self) -> bool { self.state is SCHEDULED }
    open spec fn lock_major_default_predicate(&self) -> bool { self.state is IPC_TRANSIT || self.state is KILLED }
}

impl LockOwnerIdTrait for Thread {
    // Only a running thread and an unmarked killed thread carry their container; only a running thread its process.
    open spec fn container_depth(&self) -> LockOwnerId {
        if self.state is RUNNING || self.state is KILLED { LockOwnerId::Some(self.container_depth) } else { LockOwnerId::None }
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        if self.state is RUNNING { LockOwnerId::Some(self.process_depth) } else { LockOwnerId::None }
    }
}
} // verus!
