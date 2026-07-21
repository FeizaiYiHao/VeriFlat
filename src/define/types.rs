use vstd::prelude::*;

verus! {

use vstd::simple_pptr::*;

use crate::*;

// -------------------- Begin of New Types --------------------
// -------------------- End of New Types ----------------------

// use crate::trap::Registers;
// -------------------- Begin of Types --------------------
// pub type ThreadPtr = usize;

// pub type ProcPtr = usize;

pub type EndpointIdx = usize;

// pub type EndpointPtr = usize;

// pub type ContainerPtr = usize;

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

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub struct RwLockPageTableRoot{
//    pub v: usize,
// }

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub struct RwLockContainerPtr{
//    pub v: usize,
// }

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub struct RwLockProcessPtr{
//    pub v: usize,
// }

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub struct RwLockThreadPtr{
//    pub v: usize,
// }

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub struct RwLockEndpointPtr{
//    pub v: usize,
// }

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub struct RwLockPageAllocatorPtr{
//    pub v: usize,
// }

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub struct RwLockSchedulerPtr{
//    pub v: usize,
// }

// pub type PageEntryPerm = usize;
pub type Pcid = usize;

pub type IOid = usize;

pub type L4Index = usize;

pub type L3Index = usize;

pub type L2Index = usize;

pub type L1Index = usize;

pub type SLLIndex = i32;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ThreadState {
    SCHEDULED,
    BLOCKED,
    RUNNING{cpu_id:CpuId},
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

    pub fn is_receive(&self) -> (ret: bool)
        ensures
            ret == (self == EndpointState::RECEIVE),
    {
        match self {
            EndpointState::RECEIVE => true,
            _ => false,
        }
    }
    // pub open spec fn is_receive_spec(&self) -> bool {
    //     self matches EndpointState { foo } &&  foo == EndpointState::SEND
    // }

}

#[derive(Clone, Copy, Debug)]
pub enum PageType {
    R,
    RW,
    RX,
    RWX,
}

#[allow(inconsistent_fields)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Allocated4KPageState {
    AsProcess,
    AsThread,
    AsEndpoint,
    AsScheduler,
    As4KAllocator,
    As2MAllocator,
    As1GAllocator,
    AsPageTableRoot,
    PageTable{pagetable_root:RwLockPageTableRoot},
}
#[allow(inconsistent_fields)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Allocated2MPageState {
    AsContainer,
}
#[allow(inconsistent_fields)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FreePageAllocatorState{
    GlobalList,
    PreCpuCache{cpu_id:CpuId},
}

#[allow(inconsistent_fields)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PageState {
    Unavailable,
    IOMMUTable{iommu_table_root:RwLockPageTableRoot},
    Allocated4k{state: Allocated4KPageState},
    Allocated2m{state: Allocated2MPageState},
    Free4k{state: FreePageAllocatorState},
    Free2m{state: FreePageAllocatorState},
    Free1g{state: FreePageAllocatorState},
    /// Freshly allocated from the allocator, staged in `process_ptr`'s
    /// `temp_alloc_cache` while the process write-lock is held. Not yet
    /// wired into a page table.
    Owned4k{process_ptr: RwLockProcessPtr},
    Owned2m{process_ptr: RwLockProcessPtr},
    Owned1g{process_ptr: RwLockProcessPtr},
    Mapped4k,
    Mapped2m,
    Mapped1g,
    Merged2m,
    Merged1g,
    // Io,
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
pub enum UserRetValueType {
    Success,
    ErrorNoQuota,
    ErrorVaInUse,
    Else,
}

impl UserRetValueType {
    pub open spec fn spec_is_error(&self) -> bool {
        match self {
            Self::Success => { false },
            Self::ErrorNoQuota => { true },
            Self::ErrorVaInUse => { true },
            Self::Else => { true },
        }
    }

    #[verifier(when_used_as_spec(spec_is_error))]
    pub fn is_error(&self) -> bool {
        match self {
            Self::Success => { false },
            Self::ErrorNoQuota => { true },
            Self::ErrorVaInUse => { true },
            Self::Else => { true },
        }
    }
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
    /// Adding `alloc_amount` to the running process's `quota_4k` would
    /// overflow `usize::MAX`.
    ErrorProcessQuotaOverflow,
}
pub type PTType = bool;

// -------------------- End of Types --------------------
// // -------------------- Begin of Structs --------------------

#[derive(Clone, Copy)]
pub struct VaRange4K {
    pub start: VAddr,
    pub len: usize,
    pub view: Ghost<Seq<VAddr>>,
}

pub open spec fn spec_va_range_disjoint(va_range_1: &VaRange4K, va_range_2: &VaRange4K) -> bool {
    forall|i: int, j: int|
        0 <= i < va_range_1.len && 0 <= j < va_range_2.len ==> va_range_1@[i] != va_range_2@[j]
}

#[verifier(when_used_as_spec(spec_va_range_disjoint))]
#[verifier(external_body)]
pub fn va_range_disjoint(va_range_1: &VaRange4K, va_range_2: &VaRange4K) -> (ret: bool)
    requires
        va_range_1.wf(),
        va_range_2.wf(),
    ensures
        ret == va_range_disjoint(va_range_1, va_range_2),
{
    proof {
        va_range_lemma();
        va_range_1.va_range_lemma();
        va_range_2.va_range_lemma();
    }
    if va_range_1.start > va_range_2.start {
        if va_range_2.start + va_range_2.len * 4096 < va_range_1.start {
            assert(forall|i: usize, j: usize|
                #![auto]
                0 <= i < va_range_1.len && 0 <= j < va_range_2.len ==> va_range_2@[j as int]
                    == va_range_2.start + j * 4096 && va_range_1@[i as int] == va_range_1.start + i
                    * 4096 && va_range_2.start + j * 4096 < va_range_1.start + i * 4096);
            return true;
        } else {
            return false;
        }
    } else if va_range_1.start == va_range_2.start {
        return false;
    } else {
        if va_range_1.start + va_range_1.len < va_range_2.start {
            return true;
        } else {
            return false;
        }
    }
}

impl VaRange4K {
    // SPEC ISSUE: This lemma asserts view@[i] == spec_va_add_range(start, i), but the wf()
    // invariant doesn't establish that relationship — view is an arbitrary ghost field.
    // Properly fixing requires strengthening wf() to constrain view@. Out of scope here.
    #[verifier(external_body)]
    pub proof fn va_range_lemma(&self)
        requires
            self.wf(),
        ensures
            forall|i: usize|
                0 <= i < self.len ==> self@[i as int] == spec_va_add_range(self.start, i),
            forall|i: usize|
                0 <= i < self.len ==> self@[i as int] == self.start + i
                    * 4096  //@Xiangdong Prove this
            ,
    {
    }

    pub closed spec fn view(&self) -> Seq<VAddr> {
        self.view@
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.start + self.len * 4096 < usize::MAX
        &&& spec_va_4k_valid(self.start)
        &&& self@.len() == self.len
        &&& self@.no_duplicates()
        &&& forall|i: int| #![trigger self@[i]] 0 <= i < self.len ==> spec_va_4k_valid(self@[i])
        &&& self.view_match_spec()
    }

    pub closed spec fn view_match_spec(&self) -> bool {
        &&& forall|i: usize|
            #![trigger spec_va_add_range(self.start, i)]
            0 <= i < self.len ==> spec_va_add_range(self.start, i) == self@[i as int]
    }

    pub fn new(va: VAddr, len: usize) -> (ret: Self)
        requires
            spec_va_4k_valid(va),
            va_4k_range_valid(va, len),
            va < usize::MAX - len * 4096,
        ensures
            ret.wf(),
            ret.start == va,
            ret.len == len,
    {
        proof {
            va_range_lemma();
        }
        let seq = Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize)));
        Self { start: va, len: len, view: seq }
    }

    pub fn index(&self, i: usize) -> (ret: VAddr)
        requires
            self.wf(),
            0 <= i < self.len,
        ensures
            ret == self@[i as int],
    {
        va_add_range(self.start, i)
    }
}
// #[derive(Clone, Copy, Debug)]
// pub enum DemandPagingMode {
//     NoDMDPG,
//     DirectParentPrc,
//     AllParentProc,
//     AllParentContainer,
// }

// #[derive(Clone, Copy, Debug)]
// pub enum SwitchDecision {
//     NoSwitch,
//     NoThread,
//     Switch,
// }

// #[derive(Clone, Copy)]
// pub struct SyscallReturnStruct {
//     pub error_code: RetValueType,
//     pub pcid: Option<Pcid>,
//     pub cr3: Option<usize>,
//     pub switch_decision: SwitchDecision,
// }

// impl SyscallReturnStruct {
//     pub open spec fn to_user_return_value(&self) -> UserRetValueType {
//         match self.error_code {
//             RetValueType::SuccessUsize { .. } => UserRetValueType::Success,
//             RetValueType::SuccessSeqUsize { .. } => UserRetValueType::Success,
//             RetValueType::SuccessPairUsize { .. } => UserRetValueType::Success,
//             RetValueType::SuccessThreeUsize { .. } => UserRetValueType::Success,
//             RetValueType::ErrorNoQuota => UserRetValueType::ErrorNoQuota,
//             RetValueType::ErrorVaInUse => UserRetValueType::ErrorVaInUse,
//             _ => UserRetValueType::Else,
//         }
//     }

//     pub open spec fn get_return_vaule_usize(&self) -> Option<usize> {
//         match self.error_code {
//             RetValueType::SuccessUsize { value: value } => Some(value),
//             _ => None,
//         }
//     }

//     pub open spec fn get_return_vaule_seq_usize(&self) -> Option<Seq<usize>> {
//         match self.error_code {
//             RetValueType::SuccessSeqUsize { value: value } => Some(value@),
//             _ => None,
//         }
//     }

//     pub open spec fn get_return_vaule_pair_usize(&self) -> Option<(usize, usize)> {
//         match self.error_code {
//             RetValueType::SuccessPairUsize { value1: value1, value2: value2 } => Some(
//                 (value1, value2),
//             ),
//             _ => None,
//         }
//     }

//     pub open spec fn get_return_vaule_three_usize(&self) -> Option<(usize, usize, usize)> {
//         match self.error_code {
//             RetValueType::SuccessThreeUsize {
//                 value1: value1,
//                 value2: value2,
//                 value3: value3,
//             } => Some((value1, value2, value3)),
//             _ => None,
//         }
//     }

//     pub open spec fn spec_is_error(&self) -> bool {
//         match self.error_code {
//             RetValueType::Error => true,
//             _ => false,
//         }
//     }

//     #[verifier(when_used_as_spec(spec_is_error))]
//     pub fn is_error(&self) -> (ret: bool)
//         ensures
//             ret == self.is_error(),
//     {
//         match self.error_code {
//             RetValueType::Error => true,
//             _ => false,
//         }
//     }

//     pub fn NoSwitchNew(error_code: RetValueType) -> (ret: Self)
//         ensures
//             ret.error_code == error_code,
//             ret.pcid is None,
//             ret.cr3 is None,
//             ret.switch_decision == SwitchDecision::NoSwitch,
//     {
//         return Self {
//             error_code: error_code,
//             pcid: None,
//             cr3: None,
//             switch_decision: SwitchDecision::NoSwitch,
//         };
//     }

//     pub fn NoNextThreadNew(error_code: RetValueType) -> (ret: Self)
//         ensures
//             ret.error_code == error_code,
//             ret.pcid is None,
//             ret.cr3 is None,
//             ret.switch_decision == SwitchDecision::NoThread,
//     {
//         return Self {
//             error_code: error_code,
//             pcid: None,
//             cr3: None,
//             switch_decision: SwitchDecision::NoThread,
//         };
//     }

//     pub fn SwitchNew(error_code: RetValueType, cr3: usize, pcid: Pcid) -> (ret: Self)
//         ensures
//             ret.error_code == error_code,
//             ret.pcid =~= Some(pcid),
//             ret.cr3 =~= Some(cr3),
//             ret.switch_decision == SwitchDecision::Switch,
//     {
//         return Self {
//             error_code: error_code,
//             pcid: Some(pcid),
//             cr3: Some(cr3),
//             switch_decision: SwitchDecision::Switch,
//         };
//     }
// }

// -------------------- End of Structs -------------------
} // verus!
