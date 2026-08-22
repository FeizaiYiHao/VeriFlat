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
pub const PCID_ALLOCATOR_LOCK_MAJOR:LockMajorId = CONTAINER_LOCK_MAJOR + 1;
pub const PROCESS_LOCK_MAJOR:LockMajorId = 105;
pub const THREAD_LOCK_MAJOR:LockMajorId = 106;

// A process address space is pinned before allocating the physical pages that
// will populate it.  Allocator cache/pool locks therefore sit above both page
// table kinds, allowing allocation on demand while the target table remains
// write-locked.
pub const PAGE_TABLE_LOCK_MAJOR:LockMajorId = THREAD_LOCK_MAJOR + 1;
pub const IOMMU_TABLE_LOCK_MAJOR:LockMajorId = PAGE_TABLE_LOCK_MAJOR + 1;

pub const ALLOCATOR_INNER_MAJOR:LockMajorId = 1000;

pub const ALLOCATED_PAGE_MAJOR:LockMajorId = 1000;
// Owned pages (Owned4k/Owned2m) are never actually wlock'd — they are retyped
// immediately. Give them a very low major so they don't interfere with real
// lock ordering.
pub const OWNED_PAGE_LOCK_MAJOR:LockMajorId = 1;
pub const PAGETABLE_PAGE_MAJOR:LockMajorId = 1001;

pub const THREAD_RUNNING_LOCK_MAJOR:LockMajorId = 10000;
pub const ENDPOINT_LOCK_MAJOR:LockMajorId = 10001;
pub const THREAD_BLOCKED_LOCK_MAJOR:LockMajorId = 10002;
pub const MAPPED_PAGE_LOCK_MAJOR:LockMajorId = THREAD_BLOCKED_LOCK_MAJOR + 1;

// An endpoint rendezvous discovers the peer only after locking the endpoint
// and that blocked thread. Its owning-container scheduler is therefore locked
// afterward. Keep allocation above the scheduler so new-thread creation can
// still allocate while holding the destination scheduler.
pub const SCHEDULER_LOCK_MAJOR:LockMajorId = MAPPED_PAGE_LOCK_MAJOR + 1;
pub const ALLOCATOR_CACHE_MAJOR: LockMajorId = SCHEDULER_LOCK_MAJOR + 1;
pub const ALLOCATOR_GLOBAL_POLL_MAJOR: LockMajorId = ALLOCATOR_CACHE_MAJOR + 1;
pub const THREAD_SCHEDULED_LOCK_MAJOR:LockMajorId = 20001;

pub const FREE_PAGE_LOCK_MAJOR:LockMajorId = 30000;
pub const MERGED_PAGE_LOCK_MAJOR:LockMajorId = 30000;

pub const QUOTA_MAJOR: LockMajorId = 102;
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
        // Owner-id order (high → low): None > Some(big) > … > Some(small) > High.
        //   - `None` is the MAX: a `None`-owner object (a Free page, pagetable)
        //     is locked LAST in an atomic section — once one is held, nothing
        //     with a concrete (`Some`) owner is acquired afterward.
        //   - `High` is the MIN: an `Owned` object (the intended owner-id for a
        //     page once it leaves the allocator) can only be acquired when NO
        //     `Some`-owner lock is held. Since the protocol always locks the CPU
        //     / process (a `Some` owner) first, a `High`-owner object can never
        //     be locked on top of it — i.e. owned pages are effectively private.
        //   - `NotApp` is a wildcard (spec_eq with anything), so its rows never
        //     decide an ordering — the LockId comparison skips to the next field.
        match (self, other){
            (LockOwnerId::NotApp, _) => false,
            (_, LockOwnerId::NotApp) => false,
            (LockOwnerId::High, LockOwnerId::High) => false,
            (LockOwnerId::High, LockOwnerId::Some(_)) => false,
            (LockOwnerId::High, LockOwnerId::None) => false,
            (LockOwnerId::Some(_), LockOwnerId::High) => true,
            (LockOwnerId::Some(x), LockOwnerId::Some(y)) => x > y,
            (LockOwnerId::Some(_), LockOwnerId::None) => false,
            (LockOwnerId::None, LockOwnerId::High) => true,
            (LockOwnerId::None, LockOwnerId::Some(_)) => true,
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
        // Mirror of spec_gt: a < b iff b > a (NotApp rows stay false). Order
        // high → low is None > Some(big) > Some(small) > High, so `None` is
        // never less than anything and `High` is less than everything.
        match (self, other){
            (LockOwnerId::NotApp, _) => false,
            (_, LockOwnerId::NotApp) => false,
            (LockOwnerId::High, LockOwnerId::High) => false,
            (LockOwnerId::High, LockOwnerId::Some(_)) => true,
            (LockOwnerId::High, LockOwnerId::None) => true,
            (LockOwnerId::Some(_), LockOwnerId::High) => false,
            (LockOwnerId::Some(x), LockOwnerId::Some(y)) => x < y,
            (LockOwnerId::Some(_), LockOwnerId::None) => true,
            (LockOwnerId::None, LockOwnerId::High) => false,
            (LockOwnerId::None, LockOwnerId::Some(_)) => false,
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
// #[derive(PartialEq)]
// #[derive(Eq)]
pub struct LockId{
    pub container: LockOwnerId,
    pub process: LockOwnerId,
    pub major:LockMajorId,
    pub minor:LockMinorId,
}

#[verifier(external_body)]
pub proof fn lock_id_fields_eq_imply_eq()
    ensures 
        forall|lock_id1: LockId, lock_id2: LockId|
            {
                &&& lock_id1.container == lock_id2.container
                &&& lock_id1.process == lock_id2.process
                &&& lock_id1.major == lock_id2.major
                &&& lock_id1.minor == lock_id2.minor
            }
            ==>
            lock_id1 == lock_id2
{}

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
// information to uniquely locate the object in the kernel. It is paired with
// the dynamic `LockId` in `LocalContext::lock_id_set`.
//
// The user passes a `Ghost<KernelObjId>` to every wlock-style call alongside
// the `Ghost<LockId>`. The lock primitive does NOT verify the user-supplied
// `obj_id` matches the physical object — soundness is preserved by the
// `lock_id`'s trait-based pinning to the object. The user must prove `obj_id`
// is not already represented in the held-lock set at each acquire; the kernel
// boundary later checks the exact pair against the physical kernel object.
pub ghost enum KernelObjId {
    Container(RwLockContainerPtr),
    Process(RwLockProcessPtr),
    Thread(RwLockThreadPtr),
    Endpoint(RwLockEndpointPtr),
    Scheduler(RwLockSchedulerPtr),
    PcidAllocator(RwLockPcidAllocatorPtr),
    PageTable(RwLockPageTableRoot),
    IommuTable(RwLockPageTableRoot),
    Page(PageIndex),
    Cpu(CpuId),
    AllocatorQuota(PageSize, RwLockPageAllocatorPtr),
    AllocatorCache(PageSize, RwLockPageAllocatorPtr, CpuId),
    AllocatorGlobalPoll(PageSize, RwLockPageAllocatorPtr),
}

/// One lock currently held by a thread, paired with the unique logical kernel
/// object on which it was acquired.  Keeping the object identity alongside the
/// dynamic ordering id prevents the LocalContext ledger from losing object
/// identity when lock ids are copied or change during a Release section.
pub type HeldLock = (LockId, KernelObjId);
// -------------------- End of kernel obj id ------------------


}
