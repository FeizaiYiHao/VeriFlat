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
///
/// The `snap_shot` field tracks the user-view projection at the last
/// "synchronization point": initialized to the projection at syscall entry
/// (a precondition the caller must satisfy), refreshed by
/// `end_user_view_step` to the post-step projection, and refreshed again
/// by `kernel_step_boundary` after interleaving with concurrent threads.
/// Any U-mutation by this thread that isn't bracketed by a
/// `begin_user_view_step` … `end_user_view_step` pair leaves `snap_shot`
/// stale, and is caught at the next `kernel_step_boundary` (which
/// requires `snap_shot == kernel_k_to_kernel_u(current state)`).
pub tracked struct KernelSteps{
    pub ghost steps: Seq<KernelStep>,
    pub ghost snap_shot: KernelU,
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
    /// The `snap_shot` field is preserved unchanged: at begin time, the
    /// snap_shot already equals the current user-view projection (the
    /// caller must arrange this; at syscall entry it's a precondition, and
    /// inside the syscall it's maintained by `end_user_view_step` and
    /// `kernel_step_boundary`).
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
            // Snapshot preserved across begin: the caller has arranged
            // that snap_shot already equals the current projection.
            final(self).snap_shot == old(self).snap_shot,
            // LocalContext: both phases change — kernel flips to Release
            // (no more locks may be acquired), user flips to Release
            // (user-visible locks may now be released).
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_maps_equal(old(lctx)),
            final(lctx).kernel_view_locking_state() is Release,
            final(lctx).user_view_locking_state() is Release,
            // Opening a user-view step is pure bookkeeping: it touches neither the
            // kernel state nor the LocalContext maps/`thread_id` (only the locking-state
            // phases, which `locked_objects_match_lctx` does not read), so the
            // held-lock ⇄ lctx agreement is carried across unchanged.
            kernel_k.locked_objects_match_lctx(old(lctx))
                ==> kernel_k.locked_objects_match_lctx(final(lctx)),
    {
        unimplemented!()
    }

    /// Trusted: close the currently-open user-view atomic step.
    ///
    /// Overwrites the last step's `new_*` with the current (post-section)
    /// kernel state, and flips the `LocalContext` user-view phase back to
    /// `Acquire`. The step's `old_*` and all earlier steps are preserved.
    ///
    /// Refreshes `snap_shot` to `kernel_k_to_kernel_u(*kernel_k)` — i.e.
    /// the user view AFTER this step's mutations. This is the mechanism
    /// that lets a syscall mutate U-state inside a user-step without
    /// failing the next `kernel_step_boundary` snapshot check: the
    /// mutation is recorded in the step's `new_u`, and the snapshot is
    /// refreshed to match.
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
            // Snapshot refreshed to the post-step projection.
            final(self).snap_shot == kernel_k_to_kernel_u(*kernel_k),
            // LocalContext: only the user-view phase changes (back to Acquire).
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_maps_equal(old(lctx)),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            final(lctx).user_view_locking_state() is Acquire,
            // Closing a user-view step touches neither the kernel state nor
            // LocalContext maps/`thread_id` (only the user-view phase), so the held-lock
            // ⇄ lctx agreement is carried across unchanged.
            kernel_k.locked_objects_match_lctx(old(lctx))
                ==> kernel_k.locked_objects_match_lctx(final(lctx)),
    {
        unimplemented!()
    }
}

}
