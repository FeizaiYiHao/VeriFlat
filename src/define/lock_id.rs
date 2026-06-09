use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use core::cmp::Ordering;

use crate::define::*;
verus! {
// -------------------- Begin of const ------------------------
pub const CPU_LOCK_MAJOR_RUNNING:LockMajorId = 1;
pub const CPU_LOCK_MAJOR_IDLE:LockMajorId = 2;
pub const CPU_LOCK_MAJOR_OFF:LockMajorId = 3;
pub const CPU_LOCK_MAJOR_DEFAULT:LockMajorId = 4;
pub const CONTAINER_LOCK_MAJOR:LockMajorId = 101;
pub const PROCESS_LOCK_MAJOR:LockMajorId = 105;
pub const THREAD_LOCK_MAJOR:LockMajorId = 106;

pub const ALLOCATOR_INNER_MAJOR:LockMajorId = 1000;

pub const ALLOCATED_PAGE_MAJOR:LockMajorId = 1000;
pub const PAGETABLE_PAGE_MAJOR:LockMajorId = 1001;

pub const THREAD_RUNNING_LOCK_MAJOR:LockMajorId = 10000;
pub const ENDPOINT_LOCK_MAJOR:LockMajorId = 10001;
pub const THREAD_BLOCKED_LOCK_MAJOR:LockMajorId = 10002;

pub const PAGE_TABLE_LOCK_MAJOR:LockMajorId = 10003;
pub const MAPPED_PAGE_LOCK_MAJOR:LockMajorId = 10004;

pub const SCHEDULER_LOCK_MAJOR:LockMajorId = 20000;
pub const THREAD_SCHEDULED_LOCK_MAJOR:LockMajorId = 20001;

pub const FREE_PAGE_LOCK_MAJOR:LockMajorId = 30000;
pub const MERGED_PAGE_LOCK_MAJOR:LockMajorId = 30000;

pub const QUOTA_MAJOR: LockMajorId = 102;
pub const ALLOCATOR_CACHE_MAJOR: LockMajorId = QUOTA_MAJOR + 1;
pub const ALLOCATOR_GLOBAL_POLL_MAJOR: LockMajorId = ALLOCATOR_CACHE_MAJOR + 1;
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

impl LockId{
    pub open spec fn spec_gt(self, other: Self) -> bool {
        if self.container.spec_eq(other.container) == false {
            self.container.spec_gt(other.container)
        }else if self.process.spec_eq(other.process) == false {
            self.process.spec_gt(other.process)
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
    // pub open spec fn from_pagetable_root(pagetable_root: RwLockPageTableRoot) -> Self{
    //     LockId{
    //         container: LockOwnerId::none(),
    //         process: LockOwnerId::none(),
    //         major: PAGE_TABLE_LOCK_MAJOR,
    //         minor:pagetable_root,
    //     }
    // }
}

pub trait ToLockId{
    spec fn to_lock_id(&self) -> LockId;
}

// -------------------- End of lock id  -----------------------

impl ToLockId for RwLockPageTableRoot{
    open spec fn to_lock_id(&self) -> LockId{
        LockId{
            container: LockOwnerId::none(),
            process: LockOwnerId::none(),
            major: PAGE_TABLE_LOCK_MAJOR,
            minor:*self,
        }
    }
}


// -------------------- Begin of kernel obj id ----------------
//
// Ghost identifier of a lockable kernel object. Each variant carries enough
// information to uniquely locate the object in the kernel. Used as a key in
// `LocalContext::lock_map` to associate held lock ids with the objects they
// were taken on, replacing the older `Seq<LockId>` design.
//
// The user passes a `Ghost<KernelObjId>` to every wlock-style call alongside
// the `Ghost<LockId>`. The lock primitive does NOT verify the user-supplied
// `obj_id` matches the physical object — soundness is preserved by the
// `lock_id`'s trait-based pinning to the object, while `obj_id` only acts as
// a fresh map key. The user must prove `obj_id` is not already in the map at
// each acquire (collision check), which prevents a re-used key from silently
// dropping a held lock id from the acyclic check.
pub ghost enum KernelObjId {
    Container(RwLockContainerPtr),
    Process(RwLockProcessPtr),
    Thread(RwLockThreadPtr),
    Endpoint(RwLockEndpointPtr),
    Scheduler(RwLockSchedulerPtr),
    PageTable(RwLockPageTableRoot),
    Page(PageIndex),
    Cpu(CpuId),
    AllocatorQuota(PageSize, RwLockPageAllocatorPtr),
    AllocatorCache(PageSize, RwLockPageAllocatorPtr, CpuId),
    AllocatorGlobalPoll(PageSize, RwLockPageAllocatorPtr),
}
// -------------------- End of kernel obj id ------------------


}