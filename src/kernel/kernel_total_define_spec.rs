use vstd::prelude::*;
use crate::*;

verus! {

/// One non-stuttering transition of the kernel's user projection.
///
/// Kernel atomic sections whose `KernelU` projection is unchanged are internal
/// implementation steps and are deliberately omitted from this ledger.
pub ghost struct KernelStep {
    pub old_u: KernelU,
    pub new_u: KernelU,
}

/// Ghost refinement ledger threaded through a syscall.
///
/// `snap_shot` is the user projection at the end of the preceding kernel
/// boundary (or at syscall entry).  A kernel section does not announce a user
/// step in advance.  Instead, `end_kernel_step` or `kernel_step_boundary`
/// compares the section's final projection with this snapshot and appends a
/// `KernelStep` iff the projection changed.  Thus kernel-only work is handled
/// as a stuttering step automatically.
pub tracked struct KernelSteps {
    pub ghost steps: Seq<KernelStep>,
    pub ghost snap_shot: KernelU,
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

impl KernelSteps {
    pub open spec fn view(&self) -> Seq<KernelStep> {
        self.steps
    }

    /// Finish the syscall's last kernel atomic section without introducing an
    /// interleaving point.  Any non-stuttering user projection change is
    /// recorded automatically.
    #[verifier::external_body]
    pub proof fn end_kernel_step(
        tracked &mut self,
        krnl: &KernelK,
        tracked lctx: &LocalContext,
    )
        requires
            krnl.inv(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).steps == record_user_view_change(
                old(self).steps,
                old(self).snap_shot,
                kernel_k_to_kernel_u(*krnl),
            ),
            final(self).snap_shot == kernel_k_to_kernel_u(*krnl),
    {
        unimplemented!()
    }
}

}
