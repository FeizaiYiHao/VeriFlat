---
name: project_locker_unlocker_alignment_2026_07_27
description: Raw lock-wrapper alignment contracts and explicit kernel-view Release transition
---

# Locker/unlocker lock-id alignment (2026-07-27)

This decision supersedes the protocol-boundary note in
`project_payload_mutation_wrapper_2026_07_27.md`.

- All 17 `KernelK` wrappers in `locker_unlocker.rs` require
  `lock_id_aligned(old(self), old(lctx))` and ensure
  `lock_id_aligned(final(self), final(lctx))`.
- Non-page wrappers preserve the page-only dynamic-id relation by framing
  `page_array` and `page_lock_map`. Page acquire composes the exact insert;
  page release composes the exact remove.
- `LocalContext::enter_kernel_view_release` is the approved narrow TCB
  primitive. It changes only kernel-view `Acquire` to `Release`; thread id,
  user-view phase, and every lock map are preserved.
- `KernelK::enter_kernel_view_release_preserving_locked_match` carries
  `locked_objects_match_lctx` across that phase transition.
- After a held page is retyped, allocator paths now perform:
  `enter Release -> refresh the page lock-map id -> unlock caches/pool`.
  This avoids the old cycle where the first unlock was needed to enter Release
  but the strengthened unlock contract already required alignment.
- Caller-side alignment proofs immediately after `wunlock_thread` and
  `wunlock_page` were removed; the wrappers now own those guarantees.

Verification after implementation and trimming:

```text
./verify.sh --time --num-threads 4
498 verified, 0 errors
```

No `assume`, invariant-trigger change, new `spinoff_prover`, or rlimit change
was added. The one new `external_body` is the explicitly approved
`enter_kernel_view_release` TCB transition.
