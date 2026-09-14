use core::sync::atomic::{AtomicUsize, Ordering};
use vstd::prelude::*;
use crate::*;

verus! {
pub struct TrustedAtomicUsize {
    atomic: AtomicUsize,
    value: Ghost<usize>,
    owner_cpu: Ghost<CpuId>,
}

impl TrustedAtomicUsize {
    pub closed spec fn view(&self) -> usize { self.value.view() }
    pub closed spec fn owner_cpu(&self) -> CpuId { self.owner_cpu.view() }

    pub fn new(value: usize, Ghost(owner_cpu): Ghost<CpuId>) -> (ret: Self)
        requires index_valid(NUM_CPUS, owner_cpu),
        ensures
            ret.view() == value,
            ret.owner_cpu() == owner_cpu,
    {
        Self { atomic: AtomicUsize::new(value), value: Ghost(value), owner_cpu: Ghost(owner_cpu) }
    }

    /// The returned snapshot linearizes at the atomic load. The kernel caller
    /// closes Acquire before permitting another shared-state observation.
    #[verifier::external_body]
    pub fn load(&self, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: usize)
        requires old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            ret == self.view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            lock_id_set_aligned(old(lctx)) ==> lock_id_set_aligned(final(lctx)),
    {
        self.atomic.load(Ordering::SeqCst)
    }

    /// Only the owning CPU publishes this value. This operation does not write
    /// CR3 or change the separately modeled hardware context.
    #[verifier::external_body]
    pub fn store(&mut self, value: usize, Tracked(lctx): Tracked<&LocalContext>)
        requires
            old(self).owner_cpu() == lctx.cpu_id(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).view() == value,
            final(self).owner_cpu() == old(self).owner_cpu(),
    {
        self.atomic.store(value, Ordering::SeqCst);
        self.value = Ghost(value);
    }
}
}
