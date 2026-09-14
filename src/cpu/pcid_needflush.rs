use vstd::prelude::*;
use crate::*;

verus! {
pub const PCID_NEEDFLUSH_MINOR_STRIDE: usize = 10000;

pub struct PcidNeedFlush {
    pub needflush: bool,
    pub index: Ghost<(CpuId, Pcid)>,
}

pub type PcidNeedFlushArray = LockedArray2D<PcidNeedFlush, (), Option<CpuId>, NUM_CPUS, PCID_MAX>;

impl PcidNeedFlush {
    pub closed spec fn index(&self) -> (CpuId, Pcid) { self.index.view() }

    pub fn new(Ghost(cpu_id): Ghost<CpuId>, Ghost(pcid): Ghost<Pcid>) -> (ret: Self)
        requires
            index_valid(NUM_CPUS, cpu_id),
            pcid_valid(pcid),
        ensures
            ret.inv(),
            !ret.needflush,
            ret.index() == (cpu_id, pcid),
    {
        Self { needflush: false, index: Ghost((cpu_id, pcid)) }
    }
    pub fn set(&mut self, value: bool)
        ensures
            final(self).needflush == value,
            final(self).index() == old(self).index(),
            final(self).index == old(self).index,
    {
        self.needflush = value;
    }
}

impl LockInvTrait for PcidNeedFlush {
    open spec fn inv(&self) -> bool {
        &&& index_valid(NUM_CPUS, self.index().0)
        &&& pcid_valid(self.index().1)
        &&& self.index().1 < PCID_NEEDFLUSH_MINOR_STRIDE
        &&& self.index().0 * PCID_NEEDFLUSH_MINOR_STRIDE + self.index().1 <= usize::MAX
    }
}

impl LockOwnerIdTrait for PcidNeedFlush {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
}

impl LockMinorTrait for PcidNeedFlush {
    open spec fn lock_minor(&self) -> LockMinorId { (self.index().0 * PCID_NEEDFLUSH_MINOR_STRIDE + self.index().1) as usize }
}

impl LockMajorTrait for PcidNeedFlush {
    open spec fn lock_major_1(&self) -> LockMajorId { PCID_NEEDFLUSH_LOCK_MAJOR }
    open spec fn lock_major_2(&self) -> LockMajorId { PCID_NEEDFLUSH_LOCK_MAJOR }
    open spec fn lock_major_3(&self) -> LockMajorId { PCID_NEEDFLUSH_LOCK_MAJOR }
    open spec fn lock_major_default(&self) -> LockMajorId { PCID_NEEDFLUSH_LOCK_MAJOR }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}
}
