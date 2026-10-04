use vstd::prelude::*;
use crate::*;

verus! {
/// Platform IPI stub: kicks `target` into the kernel after an offline request, or out of
/// `halt_until_ipi` after an online. No model effect; the platform body lands later.
pub fn send_ipi(target: CpuId, Tracked(lctx): Tracked<&LocalContext>)
    requires index_valid(NUM_CPUS, target), target != lctx.cpu_id(),
{
}

/// Platform halt stub: the calling cpu holds no locks and sleeps until an IPI arrives.
pub fn halt_until_ipi(Tracked(lctx): Tracked<&LocalContext>)
    requires lctx.no_locks_held(),
{
}
}
