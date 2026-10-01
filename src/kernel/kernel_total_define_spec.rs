use vstd::prelude::*;
use crate::*;
pub use super::kernel_step_wrappers::KernelSteps;

verus! {
/// One non-stuttering transition of the kernel's user projection.
///
/// Kernel atomic sections whose `KernelU` projection is unchanged are internal
/// implementation steps and are deliberately omitted from this ledger.
pub ghost struct KernelStep {
    pub old_u: KernelU,
    pub new_u: KernelU,
}

impl KernelStep {
    pub open spec fn nonlock_step(self) -> Option<KernelStep> {
        let old_u = kernel_u_nonlock_fields(self.old_u);
        let new_u = kernel_u_nonlock_fields(self.new_u);
        if old_u == new_u { None } else { Some(KernelStep { old_u, new_u }) }
    }
}

pub open spec fn record_user_view_change(
    steps: Seq<KernelStep>,
    old_u: KernelU,
    new_u: KernelU,
) -> Seq<KernelStep> {
    if old_u == new_u {
        steps
    } else {
        steps.push(KernelStep { old_u, new_u })
    }
}

#[verifier::opaque]
pub open spec fn kernel_steps_prefix_unchanged(old_steps: Seq<KernelStep>, new_steps: Seq<KernelStep>) -> bool {
    old_steps.len() <= new_steps.len() && new_steps.subrange(0, old_steps.len() as int) =~= old_steps
}

}
