# VeriFlat Codex instructions

This file is the repository-level source of truth for Codex and every Codex
subagent.  Read it before editing.  `.clinerules` is for Cline and is not a
Codex steering file.  The documents under `.kiro/steering/` contain useful
background, but some architecture examples are stale; when they conflict with
this file or live code, this file and live code win.

## Scope and ownership

- Preserve the user's dirty worktree and unrelated edits.  Never reset or
  overwrite changes you did not make.
- A subagent edits only the files assigned by the parent.  It must report every
  changed file and verification run number.
- Freeze shared core APIs before parallel module verification.  Because all
  subagents use one worktree, do not run coupled migrations concurrently: one
  agent changing a common spec can invalidate every other agent's in-flight
  result.
- Shared-worktree diagnostics are visible immediately.  Do not leave temporary
  proof scaffolding in the tree when yielding or reporting completion.
- Before accepting a subagent result, the parent reviews the diff against this
  file; a green verification result is not sufficient.

## Current lock model

- `LocalContext` contains one held-lock ledger:
  `Set<(LockId, KernelObjId)>` (`Set<HeldLock>`).  Do not reintroduce typed lock
  maps, a parallel object set, or a scalar-only lock-id set.
- `lock_id_aligned(k, lctx)` is the exact object-sensitive mirror:

  ```text
  lctx.lock_id_set().contains((id, obj))
      <==>
  obj exists in its corresponding kernel map/array
      && the real object is read- or write-locked by lctx.thread_id()
      && id is that object's current dynamic lock id
  ```

- Acquisition checks object freshness and inserts exactly `(current_id, obj)`.
  Unlock removes exactly `(current_id, obj)`.  A dynamic-id change replaces the
  old pair with the new pair during Release.
- `LocalContext` has no separate `wf()` predicate.  Its only ghost state is the
  thread id, phase, and held-lock ledger; consistency with kernel lock state is
  expressed exclusively by `lock_id_aligned` at the kernel layer.
- At `kernel_step_boundary`, the pair set is exactly unchanged, held-object
  state and rodata are explicitly framed, and final alignment is explicit.
- `all_objects_unlocked` means the thread holds neither a read nor a write lock
  on any kernel object, and is an externally tracked lock-state fact. Preserve it
  directly through operation contracts and boundary framing.  Do not derive it
  by expanding an empty pair set through global `lock_id_aligned`.

## Finished-proof acceptance rules

- Do not write a bare `assert(condition);`.
- Do not retain `assert(condition) by {}`.  If SMT proves the fact without a
  reveal or a genuinely necessary trigger bridge, delete the assertion.
- `assert(condition) by { reveal(opaque_predicate); }` is the normal accepted
  form.  Reveal only the predicates needed by that assertion.
- Open specs do not need `reveal`.  A reveal of an open spec is dead proof and
  must be removed.
- Do not use function-scope/bare `reveal(...)` when a scoped
  `assert(...) by { reveal(...); }` can own it.  A reveal must not pollute later
  proof obligations.
- Do not introduce `assert forall`.  It leaks a quantified fact and its trigger
  into the remaining solver context.  Fix the producer's trigger or explicit
  postcondition instead.  The only exception is an already-established
  fold/linked-list proof pattern that the user has explicitly approved.
- Do not introduce proof-only ghost captures/snapshots.  An old dynamic lock id
  captured because a real transition changes that id is allowed only when its
  contract consumes the value.
- Do not make bare lemma calls that seed the surrounding SMT context.  Put a
  genuinely reusable narrow lemma inside the specific assertion that consumes
  it.  Never add a global wrapper lemma for one function or a lemma that merely
  packages an entire invariant proof.
- Do not add new no-change/framing lemmas.  Prefer explicit operation
  postconditions and direct field/object-state transmission.  Existing narrow,
  reusable lemmas may be used only when the live proof already establishes that
  pattern or the user approves it.
- Do not add `assume(...)`, `assume(false)`, or `#[verifier::external_body]` as a
  proof workaround without explicit user approval.  Temporary diagnostics must
  be removed immediately after measurement.
- Do not add `#[verifier::spinoff_prover]` unless the user asks for that exact
  experiment.
- Do not change triggers on a kernel invariant or very common lemma without
  asking the user first, unless the current user request explicitly authorizes
  that exact trigger change.
- Do not add unnecessary proof.  Once verification is green, delete each new
  assert, reveal, lemma call, and ghost value one at a time and retain only what
  fails without it.

## Proof design

- Prefer direct, explicit facts over chains such as
  `map key -> id set -> major bound -> fresh`.
- Lower-level functions should expose frequently needed facts directly in
  postconditions: exact lock-set changes, target lock state, dynamic lock-id
  stability/change, and unchanged kernel fields.  Callers should not reopen
  implementation specs to rediscover these facts.
- For lock acyclicity, quantify directly over the held pair set and compare the
  `.0` lock-id component.
- Keep invariant reveals scoped and minimal.  Re-establish only invariant
  conjuncts whose actual inputs changed.
- Do not hide a difficult callsite proof inside a new lemma.  If a proof cannot
  close using the intended reveals and existing narrow reusable lemmas, report
  the exact obligation and measured cost to the user.

## Verification and performance

- Run Verus from the repository root with `./verify.sh`.  The script records a
  monotonically increasing run number; include it in reports.
- Typecheck/compile before interpreting proof failures.  Then verify the
  smallest relevant module/function, followed by a 32-thread full run for a
  completed cross-cutting change.
- Treat a verification taking more than roughly 50 seconds as suspicious and
  diagnose it rather than normalizing it.
- Use both wall time and rlimit when evaluating proof cost.  Rlimit alone does
  not establish that a proof is slow.
- To localize cost, temporarily cut individual assertions or the postcondition
  with `assume(false)` only when the user has authorized that diagnostic, then
  restore the real proof immediately.
- Before handoff, run `git diff --check` and scan changed files for bare asserts,
  empty `by {}`, `assert forall`, loose reveals, `assume`, dead ghost snapshots,
  duplicate reveals, and newly added wrapper/framing lemmas.

## Layout

- Use the nearest live sibling as the formatting reference.
- Keep submodule declarations in the directory's `mod.rs`.  Name split files
  with the original module prefix so repository search remains obvious (for
  example `locker_unlocker_pagetable.rs`).
- Avoid prose inside ordinary `proof {}` blocks.  Comments should explain a
  soundness boundary or non-obvious contract, not narrate each proof step.
