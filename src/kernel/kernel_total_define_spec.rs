use vstd::prelude::*;
use crate::*;

verus! {

/// Top-level kernel state including the user-view projection.
///
/// - `kernel_k` is the live kernel state.
/// - `old_kernel_u` is the user-view projection captured at some earlier
///   point (typically pre-syscall world). This primitive does not
///   constrain how it was set; the user-view linearization point can
///   happen in a different atomic section than syscall entry.
/// - `kernel_k_snapshot` is the `KernelK` state at the moment of the
///   user-view linearization. Captured by the linearization primitive.
/// - `new_kernel_u` is the user-view projection of `kernel_k_snapshot`
///   (equivalently, of `kernel_k` at the linearization point).
pub struct KernelTotal{
    pub kernel_k: KernelK,

    pub old_kernel_u: KernelU,
    pub kernel_k_snapshot: Ghost<KernelK>,

    pub new_kernel_u: KernelU,
}

impl KernelTotal{
    /// Trusted user-view linearization primitive.
    ///
    /// Models the per-syscall linearization point for user-visible state:
    ///   - the syscall declares "this is the user-view linearization
    ///     point" by calling this primitive;
    ///   - we capture the current `kernel_k` into `kernel_k_snapshot`
    ///     and project it to `new_kernel_u` via `kernel_k_to_kernel_u`;
    ///   - `kernel_k` itself is unchanged (this is a logical observation
    ///     point, not a state mutation);
    ///   - `old_kernel_u` is preserved (set elsewhere, typically pre-
    ///     syscall);
    ///   - `LocalContext.user_view_locking_state` flips to `Release`,
    ///     unblocking unlock of user-visible objects;
    ///   - `LocalContext.kernel_view_locking_state`, `lock_map`, and
    ///     `thread_id` are unchanged.
    ///
    /// Preconditions:
    ///   - `kernel_k.inv()` (the kernel is well-formed at the
    ///     linearization point — required so the projection is meaningful);
    ///   - `kernel_view_locking_state is Acquire` (we're inside an atomic
    ///     section, not between two of them);
    ///   - `user_view_locking_state is Acquire` (user-view linearization
    ///     hasn't already happened in this syscall).
    ///
    /// Note: this is the *user-view* linearization point only. The
    /// kernel-view counterpart is `KernelK::kernel_view_linearize`.
    #[verifier::external_body]
    pub proof fn user_view_linearize(tracked &mut self, tracked lctx: &mut LocalContext)
        requires
            old(self).kernel_k.inv(),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).user_view_locking_state() is Acquire,
        ensures
            // KernelTotal: kernel_k unchanged; snapshot captured at the
            // linearization point; old_kernel_u set to the projection of
            // the snapshot (the user-visible state observed atomically
            // at the linearization point); new_kernel_u unconstrained
            // (the syscall sets it elsewhere as its declared post-state).
            final(self).kernel_k == old(self).kernel_k,
            final(self).kernel_k_snapshot@ == final(self).kernel_k,
            final(self).old_kernel_u == kernel_k_to_kernel_u(final(self).kernel_k),
            // LocalContext: only user-view phase changes; everything else
            // preserved (we still hold every lock we held).
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).lock_map() == old(lctx).lock_map(),
            final(lctx).kernel_view_locking_state() == old(lctx).kernel_view_locking_state(),
            final(lctx).user_view_locking_state() is Release,
    {
        unimplemented!()
    }
}

}
