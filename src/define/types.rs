use vstd::prelude::*;

verus! {

use vstd::simple_pptr::*;

use super::*;

// -------------------- Begin of New Types --------------------
// -------------------- End of New Types ----------------------

// use crate::trap::Registers;
// -------------------- Begin of Types --------------------
pub type ThreadPtr = usize;

pub type ProcPtr = usize;

pub type EndpointIdx = usize;

pub type EndpointPtr = usize;

pub type ContainerPtr = usize;

pub type CpuId = usize;

pub type PagePtr = usize;

pub type PageIndex = usize;

pub type PagePerm4k = PointsTo<[u8; PAGE_SZ_4k]>;

pub type PagePerm2m = PointsTo<[u8; PAGE_SZ_2m]>;

pub type PagePerm1g = PointsTo<[u8; PAGE_SZ_1g]>;

pub type VAddr = usize;

pub type PAddr = usize;

pub type PageMapPtr = usize;

pub type PageTableRoot = usize;

pub type RwLockPageTableRoot = usize;

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
    RUNNING,
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
pub enum PageState {
    Unavailable4k,
    Unavailable2m,
    Unavailable1g,
    Pagetable(PageTableRoot),
    Allocated4k,
    Allocated2m,
    Allocated1g,
    Free4k,
    Free2m,
    Free1g,
    Mapped4k,
    Mapped2m,
    Mapped1g,
    Merged2m,
    Merged1g,
    Io,
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
    ErrorNoQuota,
    ErrorVaInUse,
    CpuIdle,
    Error,
    Else,
    NoQuota,
    VaInUse,
}

// -------------------- End of Types --------------------
// // -------------------- Begin of Structs --------------------
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
