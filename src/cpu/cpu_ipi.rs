use vstd::prelude::*;
use crate::*;

// Platform implementation: send a wake-up IPI to `target`; halt the calling cpu with interrupts enabled
// until an interrupt arrives.
unsafe extern "C" {
    fn veriflat_send_ipi(target: usize);
    fn veriflat_halt_until_ipi();
}

verus! {
/// Platform IPI: kicks `target` into the kernel after an offline request, or out of `halt_until_ipi`
/// after an online. No model effect.
#[verifier::external_body]
pub fn send_ipi(target: CpuId, Tracked(lctx): Tracked<&LocalContext>)
    requires
        index_valid(NUM_CPUS, target),
        target != lctx.cpu_id(),
{
    unsafe { veriflat_send_ipi(target); }
}

/// Platform halt: the calling cpu holds no locks and sleeps until an IPI arrives. No model effect.
#[verifier::external_body]
pub fn halt_until_ipi(Tracked(lctx): Tracked<&LocalContext>)
    requires
        lctx.no_locks_held(),
{
    unsafe { veriflat_halt_until_ipi(); }
}
}
