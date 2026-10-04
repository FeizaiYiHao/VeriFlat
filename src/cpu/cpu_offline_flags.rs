use vstd::prelude::*;
use crate::*;

verus! {
/// One per-cpu offline request of a container; `index` pins the cell to its table and slot.
pub struct OfflineFlag {
    pub requested: bool,
    pub index: Ghost<(RwLockCpuOfflineFlagsPtr, CpuId)>,
}

pub type OfflineFlagArray = LockedArray<OfflineFlag, (), (), NUM_CPUS, NO_KILL_STATE>;

/// Per-container offline request table, stored in the second 4K of the container's 2M page.
pub struct CpuOfflineFlags {
    pub owning_container: Ghost<RwLockContainerPtr>,
    pub flags: OfflineFlagArray,
}

pub type CpuOfflineFlagsUnLockedMap = UnLockedMap<RwLockCpuOfflineFlagsPtr, CpuOfflineFlags>;

pub open spec fn cpu_offline_flags_ptr(container_ptr: RwLockContainerPtr) -> RwLockCpuOfflineFlagsPtr { (container_ptr + 4096) as usize }

/// The per-cpu request bits of one table, as `ContainerU.cpu_offline_requests` projects them.
#[verifier::opaque]
pub open spec fn cpu_offline_requests_of(table: CpuOfflineFlags) -> Seq<bool> {
    Seq::new(NUM_CPUS as nat, |i: int| table.flags.spec_index(i as usize).view().view().requested)
}

impl OfflineFlag {
    pub closed spec fn index(&self) -> (RwLockCpuOfflineFlagsPtr, CpuId) { self.index.view() }

    pub fn new(Ghost(flags_ptr): Ghost<RwLockCpuOfflineFlagsPtr>, Ghost(cpu_id): Ghost<CpuId>) -> (ret: Self)
        requires index_valid(NUM_CPUS, cpu_id),
        ensures ret.inv(), !ret.requested, ret.index() == (flags_ptr, cpu_id),
    {
        Self { requested: false, index: Ghost((flags_ptr, cpu_id)) }
    }

    pub fn set(&mut self, value: bool)
        ensures final(self).requested == value, final(self).index() == old(self).index(), final(self).index == old(self).index,
    {
        self.requested = value;
    }
}

impl LockInvTrait for OfflineFlag {
    open spec fn inv(&self) -> bool { index_valid(NUM_CPUS, self.index().1) }
}

impl LockOwnerIdTrait for OfflineFlag {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
}

impl LockMajorTrait for OfflineFlag {
    open spec fn lock_major_1(&self) -> LockMajorId { CPU_OFFLINE_FLAG_LOCK_MAJOR }
    open spec fn lock_major_2(&self) -> LockMajorId { CPU_OFFLINE_FLAG_LOCK_MAJOR }
    open spec fn lock_major_3(&self) -> LockMajorId { CPU_OFFLINE_FLAG_LOCK_MAJOR }
    open spec fn lock_major_default(&self) -> LockMajorId { CPU_OFFLINE_FLAG_LOCK_MAJOR }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}

impl LockUserVisibilityTrait for OfflineFlag {
    open spec fn is_user_visible() -> bool { false }
}

impl CpuOfflineFlags {
    pub open spec fn inv(&self) -> bool {
        &&& self.flags.inv()
        &&& forall|cpu_id: CpuId| #![trigger self.flags.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> self.flags.spec_index(cpu_id).view().inv()
    }

    pub fn new_empty(Ghost(owning_container): Ghost<RwLockContainerPtr>, Ghost(flags_ptr): Ghost<RwLockCpuOfflineFlagsPtr>) -> (ret: Self)
        ensures
            ret.inv(),
            ret.owning_container.view() == owning_container,
            forall|cpu_id: CpuId| #![trigger ret.flags.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
                &&& !ret.flags.spec_index(cpu_id).view().locked()
                &&& ret.flags.spec_index(cpu_id).view().view().index() == (flags_ptr, cpu_id)
                &&& !ret.flags.spec_index(cpu_id).view().view().requested
            },
    {
        let mut flag_array: Array<RwLock<OfflineFlag, (), (), NO_KILL_STATE>, NUM_CPUS> = Array::new();
        let mut cpu_id = 0;
        while cpu_id < NUM_CPUS
            invariant
                flag_array.wf(),
                0 <= cpu_id <= NUM_CPUS,
                forall|i: CpuId| #![auto] index_valid(NUM_CPUS, i) && i < cpu_id ==> {
                    &&& flag_array.spec_index(i).inv()
                    &&& !flag_array.spec_index(i).locked()
                    &&& flag_array.spec_index(i).view().index() == (flags_ptr, i)
                    &&& !flag_array.spec_index(i).view().requested
                },
            decreases NUM_CPUS - cpu_id,
        {
            flag_array.set(cpu_id, RwLock::new_unlocked(OfflineFlag::new(Ghost(flags_ptr), Ghost(cpu_id)), (), Ghost(())));
            cpu_id = cpu_id + 1;
        }
        Self { owning_container: Ghost(owning_container), flags: LockedArray::from_array(flag_array) }
    }
}
}

const ASSERT_CPU_OFFLINE_FLAGS_FITS_4K: [(); 1] = [(); (core::mem::size_of::<CpuOfflineFlags>() <= PAGE_SZ_4K) as usize];
const ASSERT_CONTAINER_LOCK_FITS_4K: [(); 1] = [();
    (core::mem::size_of::<RwLock<Container, ReadOnlyNode<ContainerRO>, ContainerGhost, CONTAINER_HAS_KILL_STATE>>() <= PAGE_SZ_4K) as usize
];
