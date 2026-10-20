use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::*;
use core::cmp::Ordering;

use crate::define::*;
verus! {
// -------------------- Begin of const ------------------------
// A being-killed object (any kill-state type) reports the minimal id (High, High, KILLED_LOCK_MAJOR,
// minor): the killer keeps it held across sections and may still acquire every ordinary lock afterwards.
pub const KILLED_LOCK_MAJOR: LockMajorId = 0;
pub const CPU_LOCK_MAJOR_RUNNING: LockMajorId = 1;
pub const CPU_LOCK_MAJOR_IDLE: LockMajorId = 2;
// An Off CPU is terminal after its owning CPU-set lock proves the slot closed.
pub const CPU_LOCK_MAJOR_OFF: LockMajorId = 30002;
pub const PCID_NEEDFLUSH_LOCK_MAJOR: LockMajorId = 30001;
pub const CONTAINER_LOCK_MAJOR: LockMajorId = 101;
// Per-container offline request cells: held through an entire self-offline, so it sits below the process,
// thread, and cpu-set locks taken there; above the container lock so a parent can request a child's cpu.
pub const CPU_OFFLINE_FLAG_LOCK_MAJOR: LockMajorId = 104;
pub const PROCESS_LOCK_MAJOR: LockMajorId = 105;
pub const THREAD_LOCK_MAJOR: LockMajorId = 106;
// Above the thread lock so a process's last exiting thread can release its PCID after locking P and T;
// new_process therefore takes the allocator after T.
pub const PCID_ALLOCATOR_LOCK_MAJOR: LockMajorId = THREAD_LOCK_MAJOR + 1;
// A KILLED thread stays write-held across sections; its id sits above the killer's own thread and the PCID allocator
// and below pages, so the holder can still reclaim its page and allocator slots afterwards.
pub const THREAD_KILLED_LOCK_MAJOR: LockMajorId = PCID_ALLOCATOR_LOCK_MAJOR + 1;

pub const ALLOCATED_PAGE_MAJOR: LockMajorId = 1000;
// Owned pages (Owned4k/Owned2m) are never actually wlock'd — they are retyped
// immediately. Give them a very low major so they don't interfere with real
// lock ordering.
pub const OWNED_PAGE_LOCK_MAJOR: LockMajorId = 1;

pub const THREAD_IPC_TRANSIT_LOCK_MAJOR: LockMajorId = 10000;
pub const ENDPOINT_LOCK_MAJOR: LockMajorId = 10001;
// The page of an endpoint follows the endpoint lock, so the holder of an endpoint's last reference can lock its page
// to release it. Allocator caches and quotas still follow.
pub const ENDPOINT_PAGE_MAJOR: LockMajorId = ENDPOINT_LOCK_MAJOR + 1;
pub const THREAD_BLOCKED_LOCK_MAJOR: LockMajorId = ENDPOINT_PAGE_MAJOR + 1;
// A rendezvous discovers and pins its blocked peer before it can discover the
// two process address spaces.  Page tables therefore follow blocked threads;
// mapped pages still follow both page-table kinds.
pub const PAGE_TABLE_LOCK_MAJOR: LockMajorId = THREAD_BLOCKED_LOCK_MAJOR + 1;
// The one static VT-d root table precedes the IOMMU tables: an exiting process detaches its functions under the root
// table and write-locks its own IOMMU table before it releases the root table.
pub const IOMMU_ROOT_TABLE_LOCK_MAJOR: LockMajorId = PAGE_TABLE_LOCK_MAJOR + 1;
pub const IOMMU_TABLE_LOCK_MAJOR: LockMajorId = IOMMU_ROOT_TABLE_LOCK_MAJOR + 1;
// Page-table 2M window locks sit above every page-table and IOMMU table lock and below every page lock.
pub const PAGE_TABLE_WINDOW_LOCK_MAJOR: LockMajorId = IOMMU_TABLE_LOCK_MAJOR + 1;
// A table's walk pages follow both table kinds, so the holder of a table can lock the walk pages it unlinks.
pub const PAGETABLE_PAGE_MAJOR: LockMajorId = PAGE_TABLE_WINDOW_LOCK_MAJOR + 1;
pub const MAPPED_PAGE_LOCK_MAJOR: LockMajorId = PAGETABLE_PAGE_MAJOR + 1;

// CPU sets are discovered through IPC peers; their locks follow mapped pages.
pub const CPU_SET_LOCK_MAJOR: LockMajorId = MAPPED_PAGE_LOCK_MAJOR + 1;

// An endpoint rendezvous discovers the peer only after locking the endpoint
// and that blocked thread. Its owning-container scheduler is therefore locked
// afterward. Keep allocation above the scheduler so new-thread creation can
// still allocate while holding the destination scheduler.
pub const SCHEDULER_LOCK_MAJOR: LockMajorId = CPU_SET_LOCK_MAJOR + 1;
// Allocator caches, pools, and quotas split their majors by page size (4K < 2M < 1G) so one section can hold
// the same-kind objects of several sizes; same-size objects of two containers are ordered by the minor.
pub const ALLOCATOR_SIZE_4K: usize = 0;
pub const ALLOCATOR_SIZE_2M: usize = 1;
pub const ALLOCATOR_SIZE_1G: usize = 2;
pub const ALLOCATOR_CACHE_4K_MAJOR: LockMajorId = SCHEDULER_LOCK_MAJOR + 1;
pub const ALLOCATOR_CACHE_2M_MAJOR: LockMajorId = ALLOCATOR_CACHE_4K_MAJOR + 1;
pub const ALLOCATOR_CACHE_1G_MAJOR: LockMajorId = ALLOCATOR_CACHE_2M_MAJOR + 1;
pub const ALLOCATOR_GLOBAL_POOL_4K_MAJOR: LockMajorId = ALLOCATOR_CACHE_1G_MAJOR + 1;
pub const ALLOCATOR_GLOBAL_POOL_2M_MAJOR: LockMajorId = ALLOCATOR_GLOBAL_POOL_4K_MAJOR + 1;
pub const ALLOCATOR_GLOBAL_POOL_1G_MAJOR: LockMajorId = ALLOCATOR_GLOBAL_POOL_2M_MAJOR + 1;
pub const THREAD_SCHEDULED_LOCK_MAJOR: LockMajorId = 20001;

pub const FREE_PAGE_LOCK_MAJOR: LockMajorId = 30000;
pub const MERGED_PAGE_LOCK_MAJOR: LockMajorId = 30000;

pub const QUOTA_4K_MAJOR: LockMajorId = THREAD_SCHEDULED_LOCK_MAJOR + 1;
pub const QUOTA_2M_MAJOR: LockMajorId = QUOTA_4K_MAJOR + 1;
pub const QUOTA_1G_MAJOR: LockMajorId = QUOTA_2M_MAJOR + 1;

pub open spec fn allocator_cache_major(size: usize) -> LockMajorId {
    if size == ALLOCATOR_SIZE_4K { ALLOCATOR_CACHE_4K_MAJOR } else if size == ALLOCATOR_SIZE_2M { ALLOCATOR_CACHE_2M_MAJOR } else { ALLOCATOR_CACHE_1G_MAJOR }
}

pub open spec fn allocator_global_pool_major(size: usize) -> LockMajorId {
    if size == ALLOCATOR_SIZE_4K { ALLOCATOR_GLOBAL_POOL_4K_MAJOR } else if size == ALLOCATOR_SIZE_2M { ALLOCATOR_GLOBAL_POOL_2M_MAJOR } else { ALLOCATOR_GLOBAL_POOL_1G_MAJOR }
}

pub open spec fn allocator_quota_major(size: usize) -> LockMajorId {
    if size == ALLOCATOR_SIZE_4K { QUOTA_4K_MAJOR } else if size == ALLOCATOR_SIZE_2M { QUOTA_2M_MAJOR } else { QUOTA_1G_MAJOR }
}
// -------------------- End of const --------------------------

// -------------------- Begin of lock thread id  --------------
pub type LockThreadId = usize;
// -------------------- End of lock thread id  ----------------

// -------------------- Begin of lock id  ---------------------
#[derive(PartialEq)]
#[derive(Eq)]
pub enum LockOwnerId {
    High,
    Some(usize),
    None,
    NotApp,
}
impl LockOwnerId {
    pub open spec fn none() -> Self { LockOwnerId::None }
    pub open spec fn spec_eq(self, other: Self) -> bool {
        ||| self === other
        ||| self is NotApp || other is NotApp
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
        match (self, other) {
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
        ||| self == other
        ||| self > other
    }
    pub open spec fn spec_lt(self, other: Self) -> bool {
        // Mirror of spec_gt: a < b iff b > a (NotApp rows stay false). Order
        // high → low is None > Some(big) > Some(small) > High, so `None` is
        // never less than anything and `High` is less than everything.
        match (self, other) {
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
        ||| self == other
        ||| self < other
    }
}

pub type LockMajorId = usize;
// Minor ids compare lexicographically, front to back; a strict prefix sorts before every extension.
pub type LockMinorId = Seq<usize>;

// The one-element branch repeats the recursive case so singleton minors compare without a second unfolding.
pub open spec fn lock_minor_lt(lhs: LockMinorId, rhs: LockMinorId) -> bool
    decreases lhs.len(),
{
    if lhs.len() == 0 { rhs.len() > 0 }
    else if rhs.len() == 0 { false }
    else if lhs[0] != rhs[0] { lhs[0] < rhs[0] }
    else if lhs.len() == 1 { rhs.len() > 1 }
    else { lock_minor_lt(lhs.skip(1), rhs.skip(1)) }
}
pub struct LockId {
    pub container: LockOwnerId,
    pub process: LockOwnerId,
    pub major: LockMajorId,
    pub minor: LockMinorId,
}

pub proof fn lock_id_fields_eq_imply_eq()
    ensures
        forall|lock_id1: LockId, lock_id2: LockId| {
            &&& lock_id1.container == lock_id2.container
            &&& lock_id1.process == lock_id2.process
            &&& lock_id1.major == lock_id2.major
            &&& lock_id1.minor == lock_id2.minor
        } ==> lock_id1 == lock_id2
{}

impl LockId {
    pub open spec fn spec_gt(self, other: Self) -> bool {
        if self.container.spec_eq(other.container) == false { self.container.spec_gt(other.container) }
        else if self.process.spec_eq(other.process) == false { self.process.spec_gt(other.process) }
        else if self.major != other.major { self.major > other.major }
        else { lock_minor_lt(other.minor, self.minor) }
    }
    pub open spec fn spec_ge(self, other: Self) -> bool {
        ||| self == other
        ||| self > other
    }
    pub open spec fn spec_lt(self, other: Self) -> bool {
        if self.container != other.container { self.container < other.container }
        else if self.process != other.process { self.process < other.process }
        else if self.major != other.major { self.major < other.major }
        else { lock_minor_lt(self.minor, other.minor) }
    }
    pub open spec fn spec_le(self, other: Self) -> bool {
        ||| self == other
        ||| self < other
    }
}

// -------------------- End of lock id  -----------------------

// -------------------- Begin of kernel obj id ----------------
//
// Ghost identifier of a lockable kernel object. Each variant carries enough
// information to uniquely locate the object in the kernel. It is paired with
// the dynamic `LockId` in the `LocalContext` typed held-lock maps.
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
    SchedulerShard(RwLockSchedulerPtr, CpuId),
    PcidAllocator(RwLockPcidAllocatorPtr),
    CpuSet(RwLockCpuSetPtr),
    PageTable(RwLockPageTableRoot),
    // One 2M window of a page table: the L2 entry word at the 2M-aligned VA is its spin lock.
    PageTableWindow(RwLockPageTableRoot, VAddr),
    IommuTable(RwLockPageTableRoot),
    IommuRootTable(PAddr),
    Page(PageIndex),
    Cpu(CpuId),
    PcidNeedFlush(CpuId, Pcid),
    CpuOfflineFlag(RwLockCpuOfflineFlagsPtr, CpuId),
    AllocatorQuota(PageSize, RwLockPageAllocatorPtr),
    AllocatorCache(PageSize, RwLockPageAllocatorPtr, CpuId),
    AllocatorGlobalPool(PageSize, RwLockPageAllocatorPtr),
}

// -------------------- End of kernel obj id ------------------
}
