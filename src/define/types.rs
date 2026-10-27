use vstd::prelude::*;

verus! {
use vstd::simple_pptr::*;

use crate::*;

// -------------------- Begin of Types --------------------
pub type EndpointIdx = usize;
pub type CpuId = usize;
pub type PagePtr = usize;
pub type PageIndex = usize;
pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4K]>;
pub type PagePerm2m = PointsTo<[u8; PAGE_SZ_2M]>;
pub type PagePerm1g = PointsTo<[u8; PAGE_SZ_1G]>;
pub type VAddr = usize;
pub type PAddr = usize;
pub type PageMapPtr = usize;
pub type PageTableRoot = usize;
pub type RwLockPageTableRoot = usize;
pub type RwLockContainerPtr = usize;
pub type RwLockProcessPtr = usize;
pub type RwLockThreadPtr = usize;
pub type RwLockEndpointPtr = usize;
pub type RwLockPageAllocatorPtr = usize;
pub type RwLockSchedulerPtr = usize;
pub type RwLockPcidAllocatorPtr = usize;
pub type RwLockCpuSetPtr = usize;
pub type RwLockCpuOfflineFlagsPtr = usize;
pub type PciBdf = (usize, usize, usize);
pub type Pcid = usize;
pub type L4Index = usize;
pub type L3Index = usize;
pub type L2Index = usize;
pub type L1Index = usize;

/// Whether a thread dequeued by a rendezvous was sending or receiving.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IpcWait {
    Send,
    Receive,
}

#[derive(Clone, Copy, Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum ThreadState {
    /// Queued on the `cpu_id` shard of its container's scheduler.
    SCHEDULED { cpu_id: CpuId },
    /// Dequeued from its endpoint by the running rendezvous thread `partner`, which write-holds it until it schedules it; `wait` says whether it was sending or receiving.
    IPC_TRANSIT { partner: RwLockThreadPtr, wait: IpcWait },
    SENDING,
    RECEIVING,
    CALLING,
    RECEIVING_CALL,
    WAITING_REPLY,
    RUNNING { cpu_id: CpuId },
    /// Write-held by a killer, or by the callee reclaiming a killed caller's dangling thread, until the thread is destroyed or left dangling.
    KILLED,
    /// Dangling thread of a killed caller: detached from its process, and left in its container's thread sets until its callee reclaims it.
    DANGLING,
}

impl ThreadState {
    pub open spec fn is_endpoint_waiting(&self) -> bool {
        match self {
            ThreadState::SENDING | ThreadState::RECEIVING | ThreadState::CALLING | ThreadState::RECEIVING_CALL => true,
            _ => false,
        }
    }

    pub open spec fn is_endpoint_send_waiting(&self) -> bool {
        match self {
            ThreadState::SENDING | ThreadState::CALLING => true,
            _ => false,
        }
    }

    pub open spec fn is_endpoint_receive_waiting(&self) -> bool {
        match self {
            ThreadState::RECEIVING | ThreadState::RECEIVING_CALL => true,
            _ => false,
        }
    }

    /// The thread has a callee that still owes it a reply (a live caller or a killed caller's dangling thread).
    pub open spec fn is_reply_waiting(&self) -> bool {
        match self {
            ThreadState::WAITING_REPLY | ThreadState::DANGLING => true,
            _ => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum EndpointState {
    RECEIVE,
    SEND,
}

impl EndpointState {
    pub fn is_send(&self) -> (ret: bool)
        ensures
            ret == (self == EndpointState::SEND),
    {
        match self {
            EndpointState::SEND => true,
            _ => false,
        }
    }
}

#[allow(inconsistent_fields)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Allocated4KPageState {
    AsProcess,
    AsThread,
    AsEndpoint,
    AsScheduler,
    AsCpuSet,
    As4KAllocator,
    As2MAllocator,
    As1GAllocator,
    /// Root object of a CPU (`PT_TYPE`) or IOMMU (`IOMMU_TYPE`) page table.
    AsPageTableRoot { table_type: PTType },
    /// Table-walk page of the page table rooted at `pagetable_root`.
    PageTable { pagetable_root: RwLockPageTableRoot, table_type: PTType },
}
#[allow(inconsistent_fields)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Allocated2MPageState {
    AsContainer,
    AsPcidAllocator,
}
#[allow(inconsistent_fields)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FreePageAllocatorState {
    GlobalList,
    PreCpuCache { cpu_id: CpuId },
}

#[allow(inconsistent_fields)]
#[derive(Clone, Copy)]
pub enum PageState {
    Unavailable,
    Allocated4k { state: Allocated4KPageState },
    Allocated2m { state: Allocated2MPageState },
    Free4k { allocator_ptr: Ghost<RwLockPageAllocatorPtr>, state: FreePageAllocatorState },
    Free2m { allocator_ptr: Ghost<RwLockPageAllocatorPtr>, state: FreePageAllocatorState },
    Free1g { allocator_ptr: Ghost<RwLockPageAllocatorPtr>, state: FreePageAllocatorState },
    /// Freshly allocated from the allocator, staged in `thread_ptr`'s
    /// `temp_alloc_cache` while the thread write-lock is held. Not yet
    /// wired into a page table.
    Owned4k { thread_ptr: RwLockThreadPtr },
    Owned2m { thread_ptr: RwLockThreadPtr },
    Owned1g { thread_ptr: RwLockThreadPtr },
    Mapped4k,
    Mapped2m,
    Mapped1g,
    Merged2m,
    Merged1g,
}

#[derive(Clone, Copy, Debug)]
pub enum PageSize {
    SZ4k,
    SZ2m,
    SZ1g,
}

#[derive(Clone, Copy, Debug)]
pub enum PageTableErrorCode {
    NoError,
    L4EntryNotExist,
    L3EntryNotExist,
    L2EntryNotExist,
    L1EntryNotExist,
    EntryTakenBy4k,
    EntryTakenBy2m,
    EntryTakenBy1g,
}

#[derive(Clone, Copy)]
#[allow(inconsistent_fields)]
pub enum RetValueType {
    SuccessUsize { value: usize },
    SuccessSeqUsize { value: Ghost<Seq<usize>> },
    SuccessPairUsize { value1: usize, value2: usize },
    SuccessThreeUsize { value1: usize, value2: usize, value3: usize },
    Success,
    ErrorNoQuota,
    ErrorVaInUse,
    CpuIdle,
    Error,
    Else,
    NoQuota,
    VaInUse,
    // ---- syscall_alloc_quota_4k failure modes ----
    /// The owning container is being torn down (`being_killed()` set on
    /// the container's RwLock).
    ErrorContainerKilled,
    /// The container's 4k allocator's reservable quota is less than the
    /// requested `alloc_amount`.
    ErrorContainerQuotaInsufficient,
    /// The running process is being torn down (`being_killed()` set on
    /// the process's RwLock).
    ErrorProcessKilled,
    /// The currently running thread is being torn down.
    ErrorThreadKilled,
    /// The container's PCID allocator has no free nonzero PCID.
    ErrorNoPcid,
    // ---- IPC failure modes ----
    ErrorInvalidEndpoint,
    /// The endpoint has no waiting peer.
    ErrorIpcNoPeer,
    /// The endpoint has waiters in the caller's send/receive direction.
    ErrorIpcSameDirection,
    ErrorIpcTypeMismatch,
    ErrorIpcPeerKilled,
    ErrorIpcSameProcess,
    ErrorIpcSameContainer,
    ErrorIpcCpuOwnerMismatch,
    ErrorIpcCpuNotOff,
    /// The sender's process does not own the PCI function named by both sides.
    ErrorIpcPciOwnerMismatch,
    // ---- pci failure modes ----
    /// The PCI function is not owned by the caller's process.
    ErrorPciOwnerMismatch,
    /// The caller's process has no IOMMU table to attach the function to.
    ErrorPciNoIommuTable,
    ErrorPciAlreadyAttached,
    // ---- cpu hotplug failure modes ----
    /// The target cpu is invalid or not owned by the caller's container.
    ErrorCpuOwnerMismatch,
    ErrorCpuAlreadyOff,
    ErrorCpuNotOff,
    ErrorIpcSourceUnmapped,
    ErrorIpcPageOwnerMismatch,
    ErrorIpcEndpointSourceInvalid,
    ErrorIpcEndpointTargetInUse,
    ErrorIpcEndpointOwnerMismatch,
    ErrorCallAcrossContainers,
    ErrorReplyOutOfPhase,
    /// Adding `alloc_amount` to the running process's `quota_4k` would
    /// overflow `usize::MAX`.
    ErrorProcessQuotaOverflow,
    /// Adding `alloc_amount` to the running thread's `quota_4k` would
    /// overflow `usize::MAX`.
    ErrorThreadQuotaOverflow,
    /// The owning container's root process has exited; the container accepts no new resources.
    ErrorContainerZombie,
    /// The callee serving this call exited before replying.
    ErrorIpcCalleeExited,
    /// The caller this reply was for was killed; its dangling thread is reclaimed instead.
    ErrorIpcCallerKilled,
    /// The running process has no child at the requested position.
    ErrorInvalidChild,
    // ---- iommu map failure modes ----
    /// An IOVA page of the requested range already has an IOMMU mapping.
    ErrorIommuIovaAlreadyMapped,
    /// An IOVA page of the requested range has no IOMMU mapping.
    ErrorIommuIovaNotMapped,
    /// A source VA page of the requested range is not mapped in the caller's page table.
    ErrorIommuVaNotMapped,
    /// The caller's container is write-held by a live dynamic owner below the caller's requested process owner.
    ErrorContainerLockOrderConflict,
}
pub type PTType = bool;

// -------------------- End of Types --------------------
// -------------------- Begin of Structs --------------------

#[derive(Clone, Copy)]
pub struct VaRange4K {
    pub start: VAddr,
    pub len: usize,
    pub view: Ghost<Seq<VAddr>>,
}

impl VaRange4K {
    pub proof fn va_range_lemma(&self)
        requires
            self.wf(),
        ensures
            forall|i: usize|
                0 <= i < self.len ==> self.view().spec_index(i as int) == spec_va_add_range(self.start, i),
    {
    }

    pub closed spec fn view(&self) -> Seq<VAddr> { self.view.view() }

    pub open spec fn wf(&self) -> bool {
        &&& self.len <= usize::MAX / 4096
        &&& self.start < usize::MAX - self.len * 4096
        &&& spec_va_4k_valid(self.start)
        &&& self.view().len() == self.len
        &&& self.view().no_duplicates()
        &&& forall|i: int| #![trigger self.view().spec_index(i)] 0 <= i < self.len ==> spec_va_4k_valid(self.view().spec_index(i))
        &&& self.view_match_spec()
    }

    pub closed spec fn view_match_spec(&self) -> bool {
        &&& forall|i: usize|
            #![trigger spec_va_add_range(self.start, i)]
            0 <= i < self.len ==> spec_va_add_range(self.start, i) == self.view().spec_index(i as int)
    }

    pub fn new(va: VAddr, len: usize) -> (ret: Self)
        requires
            spec_va_4k_valid(va),
            va_4k_range_valid(va, len),
            len <= usize::MAX / 4096,
            va < usize::MAX - len * 4096,
        ensures
            ret.wf(),
            ret == (Self { start: va, len, view: Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize))) }),
    {
        let seq = Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize)));
        Self { start: va, len: len, view: seq }
    }

    pub fn index(&self, i: usize) -> (ret: VAddr)
        requires
            self.wf(),
            0 <= i < self.len,
        ensures
            ret == self.view().spec_index(i as int),
    {
        va_add_range(self.start, i)
    }
}

// -------------------- End of Structs -------------------
} // verus!
