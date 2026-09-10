use vstd::prelude::*;
use crate::*;

verus! {
#[repr(C)]
pub struct CpuSet {
    pub owning_container: Ghost<RwLockContainerPtr>,
    pub container_depth: Ghost<usize>,
    pub owned_cpus: ArraySet<NUM_CPUS>,
}

impl CpuSet {
    pub fn new_empty(owning_container: RwLockContainerPtr, container_depth: usize) -> (ret: Self)
        ensures
            ret.inv(),
            ret.owning_container.view() == owning_container,
            ret.container_depth.view() == container_depth,
            ret.owned_cpus.view() == Set::<CpuId>::empty(),
            ret.owned_cpus.closed_view() == Set::<CpuId>::empty(),
    {
        Self { owning_container: Ghost(owning_container), container_depth: Ghost(container_depth), owned_cpus: ArraySet::new() }
    }
}

impl LockInvTrait for CpuSet {
    open spec fn inv(&self) -> bool { self.owned_cpus.wf() }
}

impl LockMajorTrait for CpuSet {
    open spec fn lock_major_1(&self) -> LockMajorId { CPU_SET_LOCK_MAJOR }

    open spec fn lock_major_2(&self) -> LockMajorId { 233 }

    open spec fn lock_major_3(&self) -> LockMajorId { 233 }

    open spec fn lock_major_default(&self) -> LockMajorId { 233 }

    open spec fn lock_major_1_predicate(&self) -> bool { true }

    open spec fn lock_major_2_predicate(&self) -> bool { true }

    open spec fn lock_major_3_predicate(&self) -> bool { true }

    open spec fn lock_major_default_predicate(&self) -> bool { true }
}

impl LockOwnerIdTrait for CpuSet {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }

    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
}

impl LockUserVisibilityTrait for CpuSet {
    open spec fn is_user_visible() -> bool { false }
}
}

const ASSERT_CPU_SET_LOCK_FITS_4K: [(); 1] = [();
    (core::mem::size_of::<RwLock<CpuSet, (), (), CPU_SET_HAS_KILL_STATE>>() <= PAGE_SZ_4K) as usize
];
