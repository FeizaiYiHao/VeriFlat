---
name: project_lock_id_alignment_refresh_2026_07_26
description: Dynamic lock-map id refresh, cache contract cleanup, and remaining verification bridges
---

# Lock-id alignment and verification cleanup (2026-07-26)

- `LockPerm.lock_id` is a capability token (`LockToken`), not the deadlock-ordering id. Dynamic ordering ids are kept in `LocalContext.lock_map` and must equal each held object's current `LockId`.
- `lock_id_aligned` is intentionally page-only. A held page retyped during Release must refresh its `lock_map` entry before `kernel_step_boundary`, using `update_lock_id_preserving_locked_match` followed by `page_lock_id_aligned_after_refresh`.
- Scheduler ids are static. `scheduler_lock_id_is_static()` is universally quantified, so callers invoke it once; do not refresh scheduler ids after a boundary.
- `cache_perms_match_lctx` in `src/kernel/implementation/allocate_free_4k_page.rs` contains cache permission state, thread, capability token, current dynamic lock-map id, and write-lock relation. `scan_caches_and_alloc` and `wunlock_all_caches` consume this named contract, eliminating duplicated cache `forall` proofs at callers.
- Last verification: `./verify.sh` reported `484 verified, 0 errors`; `git diff --check` passed. The only automatic-trigger diagnostics were unrelated ones in `src/primitive/bitmap.rs:44` and `:47`.
- Intentional remaining quantified bridges in `allocate_free_4k_page.rs`: page-refresh frames around lines 177 and 270, and scheduler-frame composition around lines 667 and 687. They relate composed wrapper frames to caller-selected historical snapshots. Removing them would require a generic historical lock-map-frame lemma or stronger wrapper postconditions; avoid reintroducing the former without an explicit design decision.
