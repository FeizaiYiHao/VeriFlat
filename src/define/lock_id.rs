use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use core::cmp::Ordering;

use crate::define::*;
verus! {
// -------------------- Begin of const ------------------------
pub const CPU_LOCK_MAJOR:usize = 100;
pub const CONTAINER_LOCK_MAJOR:usize = 101;
pub const PROCESS_LOCK_MAJOR:usize = 102;

pub const ALLOCATED_PAGE_MAJOR:usize = 1000;
pub const Pagetable_PAGE_MAJOR:usize = 1001;

pub const THREAD_RUNNING_LOCK_MAJOR:usize = 10000;
pub const ENDPOINT_LOCK_MAJOR:usize = 10001;
pub const THREAD_BLOCKED_LOCK_MAJOR:usize = 10002;

pub const PAGE_TABLE_LOCK_MAJOR:usize = 10003;
pub const MAPPED_PAGE_LOCK_MAJOR:usize = 10004;

pub const PAGE_ALLOCATOR_MAJOR:usize = 10005;

pub const SCHEDULER_LOCK_MAJOR:usize = 20000;
pub const THREAD_SCHEDULED_LOCK_MAJOR:usize = 20001;

pub const FREE_PAGE_LOCK_MAJOR:usize = 30000;
pub const MERGED_PAGE_LOCK_MAJOR:usize = 30000;
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
    NotApp,
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
        self is NotApp || other is NotApp 
    }
    pub open spec fn spec_gt(self, other: Self) -> bool {
        match (self, other){
            (LockOwnerId::NotApp, _) => false,
            (_, LockOwnerId::NotApp) => false,
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
            (LockOwnerId::NotApp, _) => false,
            (_, LockOwnerId::NotApp) => false,
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

impl LockId{
    pub open spec fn from_pagetable_root(pagetable_root: RwLockPageTableRoot) -> Self{
        LockId{
            container: LockOwnerId::none(),
            process: LockOwnerId::none(),
            major: PAGE_TABLE_LOCK_MAJOR,
            minor:pagetable_root,
        }
    }
}

// -------------------- End of lock id  -----------------------


}