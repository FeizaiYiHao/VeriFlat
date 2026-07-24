---
name: project_match_lctx_wrapper_contract
description: "locked_objects_match_lctx is folded into the 6 4k-path lock wrappers' contracts; pattern + which callers still rebuild it"
metadata: 
  node_type: memory
  type: project
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

`locked_objects_match_lctx(lctx)` (kernel_k_define_spec.rs:202) is a self↔lctx
relation — 11 per-subsystem bidirectional foralls — and is NOT part of `inv()`.
It is a precondition of `kernel_step_boundary`.

**As of 2026-07-16, the 6 4k-path lock wrappers in
`kernel/implementation/locker_unlocker.rs` carry it in their contract:**
`wlock_allocator_cache`, `wunlock_allocator_cache`, `wlock_allocator_global_pool`,
`wunlock_allocator_global_pool`, `wlock_page`, `wunlock_page`. Each has
`requires old(self).locked_objects_match_lctx(old(lctx))` +
`ensures final(self).locked_objects_match_lctx(final(lctx))`, re-established in
the body by ONE scoped `assert(self.locked_objects_match_lctx(&*lctx)) by { the 9
sub-pred reveals }` placed right after `assert(self.inv());`. The touched
sub-pred closes from bare reveals (no 2-arm split, no assume needed) — the untouched
10 hold because a foreign-enum-variant insert/remove leaves their trigger terms
unchanged. NOTE: the 4 allocator wrappers already `reveal(allocator_perms_wf)` at
function-top, so do NOT add it inside the scoped assert (dead — removed in trim).

**Why the wrappers CAN carry it cheaply:** `lock_ensures`/`unlock_ensures` give
the exact `lock_map` delta (`.insert`/`.remove` one obj_id) and the field-framing
gives "every other subsystem map == old". Chose INLINE per wrapper, not a shared
generic lemma (touched sub-pred is re-derivation not preservation; 11
heterogeneous map types can't be one signature).

**Callers no longer rebuild it** — the 10 inline blocks in `allocate_free_4k_page`
were deleted. BUT the 2 blocks inside `pop_stage_4k_page` / `pop_stage_global_4k_page`
STAY: those helpers mutate `self` (pop/retype/stage) AFTER their internal
`wlock_page`, so they must re-establish match_lctx at their OWN ensures boundary —
NOT deletable (learned: the design predicted they were, they weren't). 3 more blocks
in `wlock_all_caches_and_global_pool`/`wunlock_all_caches`/`scan_caches_and_alloc`
were out of scope.

**Batch 2 DONE (2026-07-17, "as prep"): all 8 cpu/container/quota/process
wrappers now also carry the requires/ensures.** Same inline scoped-assert pattern;
all closed from bare reveals (both the plain and `_unless_killed` success/failure
shapes — the killed no-op preserves match_lctx trivially). `_unless_killed`
wrappers get an UNCONDITIONAL `ensures final(self).locked_objects_match_lctx` (holds
in both branches). The bridge lemma
`all_unlocked_imply_locked_objects_match_lctx(k, lctx)` (requires
`all_objects_unlocked` + empty lock_map; reveal-only body, NO axiom) lives in
`syscall_alloc_quota.rs` and seeds the first wlock at syscall entry.

**Batch 2 net cost +2.92M rlimit (locker_unlocker +2.41M, syscall +0.50M).**
`syscall_alloc_quota` uses `begin/end_user_view_step` (NOT `kernel_step_boundary`),
so it has NO match_lctx consumer — nothing to delete; Batch 2 is groundwork for
when a real consumer lands.

**KEY FIX (2026-07-17, Xiangdong's call): `begin_user_view_step` +
`end_user_view_step` (TCB `external_body` in `kernel_total_define_spec.rs`) now
ensure `kernel_k.locked_objects_match_lctx(old(lctx)) ==>
...(final(lctx))`.** Sound because both are pure bookkeeping — they preserve
`lock_map()` + `thread_id()` (the only lctx fields match_lctx reads) and take
`kernel_k` by shared ref. This CARRIES match_lctx across step boundaries the way
they already carry `lock_map`, instead of forcing callers to re-assert. It
reclaimed −4.28M in the syscall (7.89M → 3.61M): 5 of the 6 scoped 9-reveal
re-asserts (the 4 error-branch `begin`s + the commit-body `end`) became deletable.
**Only 1 re-assert remains** — the commit-body one AFTER the quota-alloc MUTATION
(a payload change, not a step boundary, is what loses the deep quantifier there;
delete-and-reverify confirms load-bearing).

**Lessons:** (1) folding match_lctx into wrappers pays off for `kernel_step_boundary`
callers (allocate_free_4k_page); for user-view-step syscalls the win comes instead
from the step primitives FRAMING match_lctx. (2) A boundary/framing primitive that
preserves the fields a deep invariant reads should ENSURE that invariant is carried
(`old ==> new`), not make every caller re-reveal it. (3) Don't over-specify helper
ensures: `commit_alloc_quota_4k`'s `ensures match_lctx` was dead (caller derives
all_objects_unlocked itself) — removed. `syscall_new_thread` still disabled
(distrusted "fk AI" file) — its own task. See
[[project_alloc_free_4k_rlimit_drivers]].