use vstd::prelude::*;
use crate::*;

verus! {

/// One user-visible atomic transition this thread has linearized.
///
/// Records the user/kernel view immediately before (`old_*`) and after
/// (`new_*`) one user-visible atomic section. A step is *opened* by
/// `begin_user_view_step` (`old_*` capture the current state, `new_* ==
/// old_*` as a placeholder) and *closed* by `end_user_view_step` (`new_*`
/// overwritten with the post-section state).
pub ghost struct KernelStep{
    pub old_u: KernelU,
    pub old_k: KernelK,
    pub new_u: KernelU,
    pub new_k: KernelK,
}

/// Ghost ledger of user-view atomic steps, threaded through a syscall by
/// ownership (like `LocalContext`). Kept separate from `KernelK` so that the
/// live kernel state is never copied/compared when a step is opened or
/// closed — the linearization primitives read `KernelK` through a shared
/// `&` reference and only mutate this ledger and the `LocalContext` phase.
pub tracked struct KernelSteps{
    pub ghost steps: Seq<KernelStep>,
}

impl KernelSteps{
    pub open spec fn view(&self) -> Seq<KernelStep>{
        self.steps
    }

    /// Trusted: open a user-view atomic step (the linearization point).
    ///
    /// Appends a fresh step whose `old_*` capture the current kernel state
    /// (`new_* == old_*` as a placeholder until the step is closed), and
    /// flips the `LocalContext` user-view phase to `Release` so the syscall
    /// may release its user-visible locks.
    ///
    /// Preconditions:
    ///   - `kernel_k.inv()` (well-formed at the linearization point, so the
    ///     projection `kernel_k_to_kernel_u` is meaningful);
    ///   - kernel-view `Acquire` (inside an atomic section);
    ///   - user-view `Acquire` (no step currently open in this syscall).
    #[verifier::external_body]
    pub proof fn begin_user_view_step(tracked &mut self, kernel_k: &KernelK, tracked lctx: &mut LocalContext)
        requires
            kernel_k.inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).user_view_locking_state() is Acquire,
        ensures
            // A new step is appended; earlier steps are preserved.
            final(self).steps.len() == old(self).steps.len() + 1,
            final(self).steps.subrange(0, old(self).steps.len() as int) == old(self).steps,
            // The opened step captures `old_*` from the current state, with
            // `new_* == old_*` as a placeholder.
            final(self).steps.last().old_k == *kernel_k,
            final(self).steps.last().old_u == kernel_k_to_kernel_u(*kernel_k),
            final(self).steps.last().new_k == *kernel_k,
            final(self).steps.last().new_u == kernel_k_to_kernel_u(*kernel_k),
            // LocalContext: both phases change — kernel flips to Release
            // (no more locks may be acquired), user flips to Release
            // (user-visible locks may now be released).
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_map() == old(lctx).lock_map(),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Release,
    {
        unimplemented!()
    }

    /// Trusted: close the currently-open user-view atomic step.
    ///
    /// Overwrites the last step's `new_*` with the current (post-section)
    /// kernel state, and flips the `LocalContext` user-view phase back to
    /// `Acquire`. The step's `old_*` and all earlier steps are preserved.
    ///
    /// Preconditions:
    ///   - `kernel_k.inv()` (the section restored well-formedness before
    ///     closing);
    ///   - a step is open (`steps` non-empty, user-view `Release`).
    #[verifier::external_body]
    pub proof fn end_user_view_step(tracked &mut self, kernel_k: &KernelK, tracked lctx: &mut LocalContext)
        requires
            kernel_k.inv(),
            old(self).steps.len() > 0,
            old(lctx).user_view_locking_state() is Release,
        ensures
            // Step count unchanged; earlier steps preserved.
            final(self).steps.len() == old(self).steps.len(),
            final(self).steps.subrange(0, old(self).steps.len() - 1)
                == old(self).steps.subrange(0, old(self).steps.len() - 1),
            // The open step keeps its `old_*` and gets `new_*` from the
            // current (post-section) state.
            final(self).steps.last().old_k == old(self).steps.last().old_k,
            final(self).steps.last().old_u == old(self).steps.last().old_u,
            final(self).steps.last().new_k == *kernel_k,
            final(self).steps.last().new_u == kernel_k_to_kernel_u(*kernel_k),
            // LocalContext: only the user-view phase changes (back to Acquire).
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_map() == old(lctx).lock_map(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            final(lctx).user_view_locking_state() is Acquire,
    {
        unimplemented!()
    }
}

}
