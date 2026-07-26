---
name: project_syscall_new_thread
description: syscall_new_thread is now ENABLED and fully verifies (lock skeleton + release paths); thread-creation body is still a stub — roadmap for finishing it
metadata: 
  node_type: memory
  type: project
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

> Historical snapshot from 2026-07-17. The stub/blocker status below is
> superseded by `project_thread_wiring_milestone.md` and
> `project_contract_proof_simplification_2026_07_25.md`; do not use it as the
> current implementation status.

`kernel/implementation/syscall_new_thread.rs` is now ENABLED in mod.rs and
**fully verifies** (3 verified, 0 errors; full crate 462; module 337K rlimit).
It was previously the distrusted non-compiling "wip. fk AI. Useless" file.

**What was done (2026-07-17):**
- Wrote the missing `release_cpu_and_finish` helper (cpu-only release, for the
  process-killed path) — the sole compile blocker (an undefined method call).
- Threaded Batch-2 `locked_objects_match_lctx` through: seeded the entry bridge
  `all_unlocked_imply_locked_objects_match_lctx` (referenced by full path
  `crate::kernel::implementation::syscall_alloc_quota::...` — it's pub but not
  re-exported at crate root), and added `locked_objects_match_lctx` to both release
  helpers' requires. begin/end_user_view_step now FRAME match_lctx (the earlier
  TCB fix), so no per-step re-asserts were needed inside the helpers.
- Fixed pre-existing gaps in the never-verified helpers: replaced two bare
  `kernel_k_to_kernel_u(*old)==*self` asserts with
  `kernel_no_change_to_user_view_fields_imply_kernel_u_eq(old(self), self)`; added
  the missing `being_killed()==false` requires to `release_cpu_and_process_and_finish`
  (its internal `wunlock_process` needs it).
- Trimmed the grind/AI scaffolding both helpers carried: dead `pre_wunlock_self`
  ghost, the per-process framing forall, the `process_perms_wf`/`thread_perms_wf`/
  cpu `unchanged_except` asserts (none load-bearing once the `kernel_no_change`
  lemma does the work — the helpers only ensure the steps ledger, NOT `final.inv()`).

**STILL A STUB — and BLOCKED on missing TCB infrastructure (scouted 2026-07-18,
4 parallel agents; 3 converged independently).** The quota-sufficient path returns
`RetValueType::Error`. Finishing real thread creation is NOT a bounded proof task
today — it is blocked:

**BLOCKER 1 — no runtime object allocation exists.** `LockedMap` (locks/locked_map.rs)
has NO `insert`/`alloc`/domain-growing method: every mutator's ensures fixes the
domain (`unchanged_except` literally requires `old.dom()==self.dom()`). `RwLock` has
no constructor; `wlock_external`/`wunlock_external` are TCB-only, gated
`requires true==false` (uncallable). No boot/init populates any map; `main()` empty.
The `UnLockedMap` insert (tracked_insert) machinery is COMMENTED OUT. `ThreadState`
has only SCHEDULED/BLOCKED/RUNNING — no UNUSED/FREE variant, so no "claim a free
slot" pool model either. So growing `thread_map` at syscall time needs a NEW
`external_body` TCB insert primitive (`ensures dom()==old.dom().insert(key)` +
mints the `PointsTo`+`RwLock<Thread>`+perm) that does not exist.

**BLOCKER 2 — a thread IS a retyped 4k page.** `thread_pages_wf`
(memory_management/pages_thread_spec.rs) is a bidirectional `thread_map.dom()` ↔
pages-in-state-`Allocated4k{AsThread}` coupling. So creating a thread = consume a
4k page → retype Free/Owned→`AsThread` → that page ptr BECOMES the thread ptr →
grow thread_map + process.owned_threads (LinkedList, via push_tail) + container
owned_threads/owned_indirect_threads ghost sets + scheduler queue (if SCHEDULED) —
all consistently.

**BLOCKER 3 — conservation fold needs a NEW axiom.** `container_process_allocator_quota_{4k,2m,1g}_wf`
folds over the container's ghost `owned_threads`/`owned_indirect_threads` SETS.
Existing axioms (kernel_fold_axioms.rs) only cover fixed-domain (`_fold_eq`) or
single-member-value-change (`_fold_change_by`). Inserting a NEW set member (even a
zero-`free_quota_pending` one that contributes 0) has NO covering axiom — needs a
new trusted `fold_insert_zero` axiom.

**What IS reusable when unblocked:** LinkedList `push_tail`/`push_head` +
`ExternalNode::take`/`put` (proven element insertion), `LockedMap::borrow_mut`, the
`pop_stage_4k_page` mutate→inv-rebuild template, `commit_alloc_quota_4k`'s
begin/end-step+Success pattern. Full per-invariant checklist (10 items) is in the
scout findings.

**DECISION NEEDED FROM XIANGDONG before any code:** finishing this means authoring
several TCB `external_body` axioms (a LockedMap domain-insert primitive + a
fold-insert axiom) — a TCB expansion, exactly the proof-gap-protocol "stop and
flag" case. Options: (a) design the map-insert TCB primitive with him; (b) confirm
the static-allocation model + a free-slot-pool redesign; (c) keep the stub and defer.
The lock-skeleton + release paths are done and verified (462 crate). See
[[project_match_lctx_wrapper_contract]], [[project_alloc_free_4k_rlimit_drivers]].
