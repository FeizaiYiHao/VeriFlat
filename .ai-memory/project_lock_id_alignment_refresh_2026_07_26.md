---
name: project_lock_id_alignment_refresh_2026_07_26
description: Dynamic lock-map id refresh, exact map composition, and ground boundary preservation
---

# Lock-id alignment and verification cleanup (2026-07-26)

- `LockPerm.lock_id` is a capability token (`LockToken`), not the deadlock-ordering id. Dynamic ordering ids are kept in `LocalContext.lock_map` and must equal each held object's current `LockId`.
- `lock_id_aligned` is intentionally page-only. A held page retyped during Release must refresh its `lock_map` entry before `kernel_step_boundary`, using `update_lock_id_preserving_locked_match` followed by `page_lock_id_aligned_after_refresh`.
- Scheduler ids are static. `scheduler_lock_id_is_static()` is universally quantified, so callers invoke it once; do not refresh scheduler ids after a boundary.
- `cache_perms_match_lctx` in `src/kernel/implementation/allocate_free_4k_page.rs` contains cache permission state/thread/token plus the current dynamic lock-map key/value. Object-side `wlocked_by` and `being_killed` are recovered at the actual borrow/unlock from `locked_objects_match_lctx` and `allocator_perms_wf`.
- The old page-specific historical frame `forall`s are no longer needed. Compose the exact insert/remove/update relations and prove one extensional equality against the snapshot taken before transient cache/pool locks were acquired. A snapshot taken immediately before scanning is wrong because it already contains the keys that are later removed.
- Batch lock wrappers need both directions of their frame: old keys are preserved, and every post key is either old or one of the explicitly acquired cache/pool keys. The reverse-domain classification prevents an exact-map composition proof from admitting surprise keys.
- `held_page_aligned_after_boundary` is the reusable ground boundary lemma. Given one held page key, pre-boundary alignment, boundary preservation, and the unchanged lock map, it derives slot equality, current dynamic-id alignment, and `locked_by` for that page. Prefer this over exporting or rebuilding a page-wide `forall`.
- Exact map equalities in `lock_ensures`, `unlock_ensures`, and lock-id refresh contracts subsume separate domain equality, inserted/removed-key membership, lookup, and preservation consequences. If a later primitive misses one fact, instantiate that one ground fact at the consumer rather than restoring the consequence bundle.
- Last verification after the follow-up simplification: `bash verify.sh --time` reported `484 verified, 0 errors` in 20.65s; `git diff --check` passed. The only automatic-trigger diagnostics were the unrelated ones in `src/primitive/bitmap.rs:44` and `:47`.
