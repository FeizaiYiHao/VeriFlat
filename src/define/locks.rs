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
pub struct ContainerDepth{
    pub value: Option<usize>,
}
pub struct ProcessDepth {
    pub value: Option<usize>,
}
pub type LockMajorId = usize;
pub type LockMinorId = usize;
#[derive(PartialEq)]
#[derive(Eq)]
pub struct LockId{
    pub container: ContainerDepth,
    pub process: ProcessDepth,
    pub major:LockMajorId,
    pub minor:LockMinorId,
}

// impl ContainerDepth
impl PartialEq for ContainerDepth {
    fn eq(&self, other: &ContainerDepth) -> bool {
        match (self.value, other.value) {
            (None, None) => true,
            (Some(x), Some(y)) => x == y,
            _ => false,
        }
    }
}
impl PartialEqSpecImpl for ContainerDepth {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &ContainerDepth) -> bool {
        match (self.value, other.value) {
            (None, None) => true,
            (Some(x), Some(y)) => x == y,
            _ => false,
        }
    }
}
impl PartialOrd for ContainerDepth{
    fn partial_cmp(&self, other: &ContainerDepth) -> Option<core::cmp::Ordering> {
        match (self.value, other.value) {
            (None, None) => Some(core::cmp::Ordering::Equal),
            (None, Some(_)) => Some(core::cmp::Ordering::Greater),
            (Some(_), None) => Some(core::cmp::Ordering::Less),
            (Some(x), Some(y)) => y.partial_cmp(&x),
        }
    }
}
impl PartialOrdSpecImpl for ContainerDepth{
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }
    open spec fn partial_cmp_spec(&self, other: &ContainerDepth) -> Option<core::cmp::Ordering> {
        match (self.value, other.value) {
            (None, None) => Some(core::cmp::Ordering::Equal),
            (None, Some(_)) => Some(core::cmp::Ordering::Greater),
            (Some(_), None) => Some(core::cmp::Ordering::Less),
            (Some(x), Some(y)) => vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&y,&x),
        }
    }
}

// impl ProcessDepth
impl PartialEq for ProcessDepth {
    fn eq(&self, other: &ProcessDepth) -> bool {
        match (self.value, other.value) {
            (None, None) => true,
            (Some(x), Some(y)) => x == y,
            _ => false,
        }
    }
}
impl PartialEqSpecImpl for ProcessDepth {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &ProcessDepth) -> bool {
        match (self.value, other.value) {
            (None, None) => true,
            (Some(x), Some(y)) => x == y,
            _ => false,
        }
    }
}
impl PartialOrd for ProcessDepth{
    fn partial_cmp(&self, other: &ProcessDepth) -> Option<core::cmp::Ordering> {
        match (self.value, other.value) {
            (None, None) => Some(core::cmp::Ordering::Equal),
            (None, Some(_)) => Some(core::cmp::Ordering::Greater),
            (Some(_), None) => Some(core::cmp::Ordering::Less),
            (Some(x), Some(y)) => y.partial_cmp(&x),
        }
    }
}
impl PartialOrdSpecImpl for ProcessDepth{
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }
    open spec fn partial_cmp_spec(&self, other: &ProcessDepth) -> Option<core::cmp::Ordering> {
        match (self.value, other.value) {
            (None, None) => Some(core::cmp::Ordering::Equal),
            (None, Some(_)) => Some(core::cmp::Ordering::Greater),
            (Some(_), None) => Some(core::cmp::Ordering::Less),
            (Some(x), Some(y)) => vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&y,&x),
        }
    }
}

// impl LockId
impl PartialOrd for LockId{
    fn partial_cmp(&self, other: &LockId) -> Option<core::cmp::Ordering> {
        if self.container != other.container {
            self.container.partial_cmp(&other.container)
        }else if self.process != other.process{
            self.process.partial_cmp(&other.process)
        }else if self.major != other.major {
            self.major.partial_cmp(&other.major)
        }else{
            self.minor.partial_cmp(&other.minor)
        }
    }
}
impl PartialOrdSpecImpl for LockId{
    open spec fn obeys_partial_cmp_spec() -> bool {
        true
    }
    open spec fn partial_cmp_spec(&self, other: &LockId) -> Option<core::cmp::Ordering> {
        if self.container != other.container {
            vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&self.container, &other.container)
        }else if self.process != other.process{
            vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&self.process, &other.process)
        }else if self.major != other.major {
            vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&self.major, &other.major)
        }else{
            vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(&self.minor, &other.minor)
        }
    }
}

impl Ord for LockId{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        if self.container != other.container {
            self.container.cmp(&other.container)
        }else if self.process != other.process{
            self.process.cmp(&other.process)
        }else if self.major != other.major {
            self.major.cmp(&other.major)
        }else{
            self.minor.cmp(&other.minor)
        }
    }
}
impl OrdSpecImpl for LockId{
}
// impl SpecOrd for LockId{
//     open spec fn spec_lt(self, other:LockId) -> bool {
//         vstd::std_specs::cmp::PartialOrdSpecImpl::partial_cmp_spec(&self, &other) == Some(core::cmp::Ordering::Less)
//     }
//     open spec fn spec_le(self, other:LockId) -> bool { 
//         |||
//         vstd::std_specs::cmp::PartialOrdSpecImpl::partial_cmp_spec(&self, &other) == Some(core::cmp::Ordering::Less)
//         |||
//         vstd::std_specs::cmp::PartialOrdSpecImpl::partial_cmp_spec(&self, &other) == Some(core::cmp::Ordering::Equal)
//     }
//     open spec fn spec_gt(self, other:LockId) -> bool {
//         vstd::std_specs::cmp::PartialOrdSpecImpl::partial_cmp_spec(&self, &other) == Some(core::cmp::Ordering::Greater)
//     }
//     open spec fn spec_ge(self, other:LockId) -> bool {
//         |||
//         vstd::std_specs::cmp::PartialOrdSpecImpl::partial_cmp_spec(&self, &other) == Some(core::cmp::Ordering::Greater)
//         |||
//         vstd::std_specs::cmp::PartialOrdSpecImpl::partial_cmp_spec(&self, &other) == Some(core::cmp::Ordering::Equal)
//     }
// }

// -------------------- End of lock id  -----------------------
}