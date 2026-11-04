use vstd::prelude::*;
use crate::*;

verus! {
pub const PCID_NEEDFLUSH_MINOR_STRIDE: usize = 10000;

/// The needflush cell of one (cpu, pcid) slot, named by `index`. A set `needflush` means that cpu's TLB and structure
/// cache for that PCID may hold stale translations and must be flushed before the cpu runs that PCID again.
/// `line_pad` makes the needflush lock cell exactly one 64-byte cache line (layout assert at the end of this file).
pub struct PcidNeedFlush {
    pub needflush: bool,
    pub index: Ghost<(CpuId, Pcid)>,
    pub line_pad: [usize; 6],
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
        Self { needflush: false, index: Ghost((cpu_id, pcid)), line_pad: [0usize; 6] }
    }
    pub fn set(&mut self, value: bool)
        ensures
            final(self).needflush == value,
            final(self).index() == old(self).index(),
            final(self).index == old(self).index,
            final(self).line_pad == old(self).line_pad,
    {
        self.needflush = value;
    }
}

impl LockInvTrait for PcidNeedFlush {
    /// The cell's slot is a valid (cpu, pcid).
    open spec fn inv(&self) -> bool {
        &&& index_valid(NUM_CPUS, self.index().0)
        &&& pcid_valid(self.index().1)
        // The lock minor cpu * STRIDE + pcid is unique and fits in usize.
        &&& self.index().1 < PCID_NEEDFLUSH_MINOR_STRIDE
        &&& self.index().0 * PCID_NEEDFLUSH_MINOR_STRIDE + self.index().1 <= usize::MAX
    }
}

impl LockOwnerIdTrait for PcidNeedFlush {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::None }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::None }
}

impl LockMinorTrait for PcidNeedFlush {
    open spec fn lock_minor(&self) -> LockMinorId { seq![(self.index().0 * PCID_NEEDFLUSH_MINOR_STRIDE + self.index().1) as usize] }
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

// Layout contract: every needflush lock cell is exactly one cache line.
const _: () = assert!(core::mem::size_of::<LockCell<PcidNeedFlush, (), Option<CpuId>, NO_KILL_STATE>>() == 64);
