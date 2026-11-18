use vstd::prelude::*;
use crate::*;

verus! {
/// The trap-frame permission of the thread each cpu runs. Slot `c` is taken and filled only with cpu `c`'s own local
/// context; the kill IPI returns a remote cpu's slot.
pub tracked struct CpuTrapFrameTable {
    tracked frames: Map<CpuId, TrapFramePerm>,
}

impl CpuTrapFrameTable {
    pub closed spec fn view(&self) -> Map<CpuId, TrapFramePerm> { self.frames }

    /// Init only.
    pub(crate) proof fn new(tracked frames: Map<CpuId, TrapFramePerm>) -> (tracked ret: Self)
        ensures
            ret.view() == frames,
    {
        CpuTrapFrameTable { frames }
    }

    pub proof fn take(tracked &mut self, tracked lctx: &LocalContext) -> (tracked ret: TrapFramePerm)
        requires
            old(self).view().dom().contains(lctx.cpu_id()),
        ensures
            final(self).view() == old(self).view().remove(lctx.cpu_id()),
            ret == old(self).view()[lctx.cpu_id()],
    {
        self.frames.tracked_remove(lctx.cpu_id())
    }

    pub proof fn put(tracked &mut self, tracked lctx: &LocalContext, tracked frame: TrapFramePerm)
        requires
            !old(self).view().dom().contains(lctx.cpu_id()),
        ensures
            final(self).view() == old(self).view().insert(lctx.cpu_id(), frame),
    {
        self.frames.tracked_insert(lctx.cpu_id(), frame);
    }
}
}
