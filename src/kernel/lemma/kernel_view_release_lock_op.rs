use vstd::prelude::*;
use crate::*;

verus! {
pub proof fn enter_kernel_view_release_preserving_lock_alignments(krnl: &KernelK, tracked lctx: &mut LocalContext)
    requires
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(krnl, old(lctx)),
    ensures
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        typed_lock_maps_aligned(krnl, final(lctx)),
        krnl.all_objects_unlocked(final(lctx)) == krnl.all_objects_unlocked(old(lctx)),
{ lctx.enter_kernel_view_release(); assert(krnl.all_objects_unlocked(lctx) == krnl.all_objects_unlocked(old(lctx))) by { reveal(KernelK::all_objects_unlocked); }; }
} // verus!
