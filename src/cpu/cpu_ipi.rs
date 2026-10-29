use vstd::prelude::*;
use crate::*;

// Platform implementation: send a wake-up IPI to `target`; halt the calling cpu with interrupts enabled
// until an interrupt arrives; clear the calling cpu's pending running-to-idle request before it ends its kernel step.
unsafe extern "C" {
    fn veriflat_send_ipi(target: usize);
    fn veriflat_halt_until_ipi();
    pub(super) fn veriflat_clear_running_to_idle_pending();
}

verus! {
/// Platform wake-up IPI: releases remote cpu `target` from `wait_until_online` into its idle loop. Sending it uses
/// the target's kernel-call permission; the target moves to `Idle`.
#[verifier::external_body]
pub fn ipi_wake(target: CpuId, Tracked(cpu_op): Tracked<&mut CpuOpArray>, perm: Tracked<&KernelCallPerm>, Tracked(lctx): Tracked<&LocalContext>)
    requires
        index_valid(NUM_CPUS, target),
        target != lctx.cpu_id(),
        perm.view().cpu_id() == target,
        lctx.kernel_view_locking_state() is Release,
    ensures
        final(cpu_op).view() == old(cpu_op).view().update(target as int, CpuOpState::Idle),
{
    unsafe { veriflat_send_ipi(target); }
    proof { cpu_op.woken(target); }
}

/// Platform halt: the calling cpu holds no locks and sleeps in a plain `hlt` with its interrupt flag set until an IPI
/// arrives. No model effect.
#[verifier::external_body]
pub fn halt_until_ipi(Tracked(lctx): Tracked<&LocalContext>)
    requires
        lctx.no_locks_held(),
{
    unsafe { veriflat_halt_until_ipi(); }
}
}
