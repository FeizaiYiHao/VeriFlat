use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use core::cmp::Ordering;
verus! {
// -------------------- Begin of const ------------------------
pub const PAGE_TABLE_LOCK_MAJOR:usize = 0;
pub const PHY_PAGE_LOCK_MAJOR:usize = 1;
// -------------------- End of const --------------------------


// -------------------- Begin of lock thread id  --------------
pub type LockThreadId = usize;
// -------------------- End of lock thread id  ----------------

// -------------------- Begin of lock id  ---------------------
#[derive(PartialEq)]
#[derive(Eq)]
pub enum LockOwnerId{
    High,
    Some(usize),
    None,
    NA,
}

pub type LockMajorId = usize;
pub type LockMinorId = usize;
#[derive(PartialEq)]
#[derive(Eq)]
pub struct LockId{
    pub container: LockOwnerId,
    pub process: LockOwnerId,
    pub major:LockMajorId,
    pub minor:LockMinorId,
}

impl LockOwnerId{
    pub open spec fn none() -> Self{
        LockOwnerId::None
    }
    pub open spec fn spec_eq(self, other: Self) -> bool {
        |||
        self === other
        |||
        self is NA || other is NA 
    }
    pub open spec fn spec_gt(self, other: Self) -> bool {
        match (self, other){
            (LockOwnerId::NA, _) => false,
            (_, LockOwnerId::NA) => false,
            (LockOwnerId::High, LockOwnerId::High) => false,
            (LockOwnerId::High, LockOwnerId::Some(_)) => true,
            (LockOwnerId::High, LockOwnerId::None) => true,
            (LockOwnerId::Some(_), LockOwnerId::High) => false,
            (LockOwnerId::Some(x), LockOwnerId::Some(y)) => x > y,
            (LockOwnerId::Some(_), LockOwnerId::None) => true,
            (LockOwnerId::None, LockOwnerId::High) => false,
            (LockOwnerId::None, LockOwnerId::Some(_)) => false,
            (LockOwnerId::None, LockOwnerId::None) => false,
        }
    }
    pub open spec fn spec_ge(self, other: Self) -> bool {
        |||
        self == other
        |||
        self > other
    }    
    pub open spec fn spec_lt(self, other: Self) -> bool {
        match (self, other){
            (LockOwnerId::NA, _) => false,
            (_, LockOwnerId::NA) => false,
            (LockOwnerId::High, LockOwnerId::High) => false,
            (LockOwnerId::High, LockOwnerId::Some(_)) => false,
            (LockOwnerId::High, LockOwnerId::None) => false,
            (LockOwnerId::Some(_), LockOwnerId::High) => true,
            (LockOwnerId::Some(x), LockOwnerId::Some(y)) => x < y,
            (LockOwnerId::Some(_), LockOwnerId::None) => false,
            (LockOwnerId::None, LockOwnerId::High) => true,
            (LockOwnerId::None, LockOwnerId::Some(_)) => true,
            (LockOwnerId::None, LockOwnerId::None) => false,
        }
    }
    pub open spec fn spec_le(self, other: Self) -> bool {
        |||
        self == other
        |||
        self < other
    }
}


// // impl LockOwnerId
// impl PartialEq for LockOwnerId {
//     fn eq(&self, other: &LockOwnerId) -> bool {
//         match (self.value, other.value) {
//             (None, None) => true,
//             (Some(x), Some(y)) => x == y,
//             _ => false,
//         }
//     }
// }
// impl PartialEqSpecImpl for LockOwnerId {
//     open spec fn obeys_eq_spec() -> bool {
//         true
//     }

//     open spec fn eq_spec(&self, other: &LockOwnerId) -> bool {
//         match (self.value, other.value) {
//             (None, None) => true,
//             (Some(x), Some(y)) => spec_eq(x,y),
//             _ => false,
//         }
//     }
// }
// impl PartialOrd for LockOwnerId{
//     fn partial_cmp(&self, other: &LockOwnerId) -> Option<core::cmp::Ordering> {
//         match (self.value, other.value) {
//             (None, None) => Some(core::cmp::Ordering::Equal),
//             (None, Some(_)) => Some(core::cmp::Ordering::Greater),
//             (Some(_), None) => Some(core::cmp::Ordering::Less),
//             (Some(x), Some(y)) => y.partial_cmp(&x),
//         }
//     }
// }
// impl PartialOrdSpecImpl for LockOwnerId{
//     open spec fn obeys_partial_cmp_spec() -> bool {
//         true
//     }
//     open spec fn partial_cmp_spec(&self, other: &LockOwnerId) -> Option<core::cmp::Ordering> {
//         match (self.value, other.value) {
//             (None, None) => Some(core::cmp::Ordering::Equal),
//             (None, Some(_)) => Some(core::cmp::Ordering::Greater),
//             (Some(_), None) => Some(core::cmp::Ordering::Less),
//             (Some(x), Some(y)) => vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&y,&x),
//         }
//     }
// }
// impl Ord for LockOwnerId{
//     fn cmp(&self, other: &Self) -> core::cmp::Ordering {
//         match (self.value, other.value) {
//             (None, None) => core::cmp::Ordering::Equal,
//             (None, Some(_)) => core::cmp::Ordering::Greater,
//             (Some(_), None) => core::cmp::Ordering::Less,
//             (Some(x), Some(y)) => y.cmp(&x),
//         }
//     }
// }
// impl OrdSpecImpl for LockOwnerId{
//     open spec fn obeys_cmp_spec() -> bool {
//         true
//     }

//     open spec fn cmp_spec(&self, other: &LockOwnerId) -> core::cmp::Ordering {
//         match (self.value, other.value) {
//             (None, None) => core::cmp::Ordering::Equal,
//             (None, Some(_)) => core::cmp::Ordering::Greater,
//             (Some(_), None) => core::cmp::Ordering::Less,
//             (Some(x), Some(y)) => vstd::std_specs::cmp::OrdSpec::cmp_spec(&y, &x),
//         }
//     }
// }
// // impl LockOwnerId
// impl PartialEq for LockOwnerId {
//     fn eq(&self, other: &LockOwnerId) -> bool {
//         match (self.value, other.value) {
//             (None, None) => true,
//             (Some(x), Some(y)) => x == y,
//             _ => false,
//         }
//     }
// }
// impl PartialEqSpecImpl for LockOwnerId {
//     open spec fn obeys_eq_spec() -> bool {
//         true
//     }

//     open spec fn eq_spec(&self, other: &LockOwnerId) -> bool {
//         match (self.value, other.value) {
//             (None, None) => true,
//             (Some(x), Some(y)) => spec_eq(x,y),
//             _ => false,
//         }
//     }
// }
// impl PartialOrd for LockOwnerId{
//     fn partial_cmp(&self, other: &LockOwnerId) -> Option<core::cmp::Ordering> {
//         match (self.value, other.value) {
//             (None, None) => Some(core::cmp::Ordering::Equal),
//             (None, Some(_)) => Some(core::cmp::Ordering::Greater),
//             (Some(_), None) => Some(core::cmp::Ordering::Less),
//             (Some(x), Some(y)) => y.partial_cmp(&x),
//         }
//     }
// }
// impl PartialOrdSpecImpl for LockOwnerId{
//     open spec fn obeys_partial_cmp_spec() -> bool {
//         true
//     }
//     open spec fn partial_cmp_spec(&self, other: &LockOwnerId) -> Option<core::cmp::Ordering> {
//         match (self.value, other.value) {
//             (None, None) => Some(core::cmp::Ordering::Equal),
//             (None, Some(_)) => Some(core::cmp::Ordering::Greater),
//             (Some(_), None) => Some(core::cmp::Ordering::Less),
//             (Some(x), Some(y)) => vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&y,&x),
//         }
//     }
// }
// impl Ord for LockOwnerId{
//     fn cmp(&self, other: &Self) -> core::cmp::Ordering {
//         match (self.value, other.value) {
//             (None, None) => core::cmp::Ordering::Equal,
//             (None, Some(_)) => core::cmp::Ordering::Greater,
//             (Some(_), None) => core::cmp::Ordering::Less,
//             (Some(x), Some(y)) => y.cmp(&x),
//         }
//     }
// }
// impl OrdSpecImpl for LockOwnerId{
//     open spec fn obeys_cmp_spec() -> bool {
//         true
//     }

//     open spec fn cmp_spec(&self, other: &Self) -> core::cmp::Ordering {
//         match (self.value, other.value) {
//             (None, None) => core::cmp::Ordering::Equal,
//             (None, Some(_)) => core::cmp::Ordering::Greater,
//             (Some(_), None) => core::cmp::Ordering::Less,
//             (Some(x), Some(y)) => vstd::std_specs::cmp::OrdSpec::cmp_spec(&y, &x),
//         }
//     }
// }
// // impl LockId
// impl PartialOrd for LockId{
//     fn partial_cmp(&self, other: &LockId) -> Option<core::cmp::Ordering> {
//         if self.container != other.container {
//             self.container.partial_cmp(&other.container)
//         }else if self.process != other.process{
//             self.process.partial_cmp(&other.process)
//         }else if self.major != other.major {
//             self.major.partial_cmp(&other.major)
//         }else{
//             self.minor.partial_cmp(&other.minor)
//         }
//     }
// }
// impl PartialOrdSpecImpl for LockId{
//     open spec fn obeys_partial_cmp_spec() -> bool {
//         true
//     }
//     open spec fn partial_cmp_spec(&self, other: &LockId) -> Option<core::cmp::Ordering> {
//         if self.container != other.container {
//             vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&self.container, &other.container)
//         }else if self.process != other.process{
//             vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&self.process, &other.process)
//         }else if self.major != other.major {
//             vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&self.major, &other.major)
//         }else{
//             vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&self.minor, &other.minor)
//         }
//     }
// }

// impl Ord for LockId{
//     fn cmp(&self, other: &Self) -> core::cmp::Ordering {
//         if self.container != other.container {
//             self.container.cmp(&other.container)
//         }else if self.process != other.process{
//             self.process.cmp(&other.process)
//         }else if self.major != other.major {
//             self.major.cmp(&other.major)
//         }else{
//             self.minor.cmp(&other.minor)
//         }
//     }
// }
// impl OrdSpecImpl for LockId{
//     open spec fn obeys_cmp_spec() -> bool {
//         true
//     }

//     open spec fn cmp_spec(&self, other: &Self) -> core::cmp::Ordering {
//         if self.container != other.container {
//             vstd::std_specs::cmp::OrdSpec::cmp_spec(&self.container, &other.container)
//         }else if self.process != other.process{
//             vstd::std_specs::cmp::OrdSpec::cmp_spec(&self.process, &other.process)
//         }else if self.major != other.major {
//             vstd::std_specs::cmp::OrdSpec::cmp_spec(&self.major, &other.major)
//         }else{
//             vstd::std_specs::cmp::OrdSpec::cmp_spec(&self.minor, &other.minor)
//         }
//     }
// }

impl LockId{
    pub open spec fn spec_gt(self, other: Self) -> bool {
        if self.container != other.container {
            self.container > other.container
        }else if self.process != other.process{
            self.process > other.process
        }else if self.major != other.major {
            self.major > other.major
        }else{
            self.minor > other.minor
        }
    }
    pub open spec fn spec_ge(self, other: Self) -> bool {
        |||
        self == other
        |||
        self > other
    }
    pub open spec fn spec_lt(self, other: Self) -> bool {
        if self.container != other.container {
            self.container < other.container
        }else if self.process != other.process{
            self.process < other.process
        }else if self.major != other.major {
            self.major < other.major
        }else{
            self.minor < other.minor
        }
    }
    pub open spec fn spec_le(self, other: Self) -> bool {
        |||
        self == other
        |||
        self < other
    }
}

// -------------------- End of lock id  -----------------------


}