use core::sync::atomic::{AtomicUsize, Ordering};
use vstd::prelude::*;
use crate::*;

/// One hardware cr3/pcid word on its own cache line: every thread switch stores its cpu's word, so a shared line would
/// bounce between cpus.
#[repr(align(64))]
struct CacheLineWord(AtomicUsize);

/// Memory of the hardware cr3/pcid words, one cell per cpu. Only the token methods below reach it; the kernel object
/// holds the zero-size tokens and none of these bytes.
static CPU_HW_CR3_PCID_CELLS: [CacheLineWord; NUM_CPUS] = [const { CacheLineWord(AtomicUsize::new(0)) }; NUM_CPUS];

// Layout contract: each cpu's cr3/pcid word fills exactly one cache line.
const _: () = assert!(core::mem::size_of::<CacheLineWord>() == 64);

verus! {
/// Token of hardware cr3/pcid cell `owner_cpu()`: `view()` is the value that cell holds.
pub struct TrustedAtomicUsize {
    value: Ghost<usize>,
    owner_cpu: Ghost<CpuId>,
}

impl TrustedAtomicUsize {
    pub closed spec fn view(&self) -> usize { self.value.view() }
    pub closed spec fn owner_cpu(&self) -> CpuId { self.owner_cpu.view() }

    /// TCB: write `value` into cell `cpu_id` and mint the cell's token, owned by cpu `cpu_id`; init only, once per cell.
    #[verifier::external_body]
    pub fn new(cpu_id: CpuId, value: usize) -> (ret: Self)
        requires
            index_valid(NUM_CPUS, cpu_id),
        ensures
            ret.view() == value,
            ret.owner_cpu() == cpu_id,
    {
        CPU_HW_CR3_PCID_CELLS[cpu_id].0.store(value, Ordering::SeqCst);
        Self { value: Ghost(value), owner_cpu: Ghost(cpu_id) }
    }

    /// TCB: the returned snapshot of cell `cpu_id` linearizes at the atomic load. The kernel caller closes Acquire before
    /// permitting another shared-state observation.
    #[verifier::external_body]
    pub fn load(&self, cpu_id: CpuId, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: usize)
        requires
            index_valid(NUM_CPUS, cpu_id),
            self.owner_cpu() == cpu_id,
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            ret == self.view(),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
    {
        CPU_HW_CR3_PCID_CELLS[cpu_id].0.load(Ordering::SeqCst)
    }

    /// TCB: publish `value` in cell `cpu_id`, from cpu `cpu_id` itself or from the running-to-idle IPI it acknowledged.
    /// This does not write CR3 or change the separately modeled hardware context.
    #[verifier::external_body]
    pub fn store(&mut self, cpu_id: CpuId, value: usize, Tracked(lctx): Tracked<&LocalContext>)
        requires
            index_valid(NUM_CPUS, cpu_id),
            old(self).owner_cpu() == cpu_id,
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).view() == value,
            final(self).owner_cpu() == old(self).owner_cpu(),
    {
        CPU_HW_CR3_PCID_CELLS[cpu_id].0.store(value, Ordering::SeqCst);
        self.value = Ghost(value);
    }
}
}
