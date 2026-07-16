---
description: Check the working diff against Xiangdong's Verus style (verus-style.md + canonical files)
---

Review the current change for conformance to Xiangdong's VeriFlat Verus style.
Run this after any major edit to `src/` before considering the work done.

## Steps

1. **Get the diff — scoped to THIS session's edits.** The recorder hook
   (`.claude/hooks/style-record.sh`) logs every `src/**/*.rs` this session
   actually changed into `.claude/.session-edits` (repo-relative paths, one per
   line). Read that ledger and review ONLY those files — this is the same set the
   Stop gate blocks on, so reviewing anything else can't clear the gate, and it
   keeps pre-existing dirty files (that this session never touched) out of scope.

   - If the ledger is missing or empty, this session edited no Verus source:
     report **clean** and stop (nothing to check, nothing to clear).
   - Otherwise diff only the ledger files: `git diff HEAD -- <ledger paths>`
     (add `git diff --staged -- <ledger paths>` if mid-commit). Skip any ledger
     path git no longer reports dirty (reverted since it was edited).
   - If a base ref is given in `$ARGUMENTS`, diff the ledger files against that
     ref instead of `HEAD`.

   Only review Verus source that actually changed — ignore untouched code.

2. **Load the rubric.** Read `.kiro/steering/verus-style.md`. The canonical
   style references (mirror these — they are HIS code) are:
   - `src/kernel/implementation/syscall_alloc_quota.rs` (`syscall_alloc_quota_4k`,
     `commit_alloc_quota_4k`)
   - `src/kernel/implementation/locker_unlocker.rs` (`wlock_cpu`, `wunlock_quota_4k`,
     `wunlock_process`, …)
   For each changed function, open the nearest LIVE sibling in those files and
   compare shape. NEVER calibrate against commented-out / `/* */` code or the dead
   templates (`finish_empty_user_step`, `release_cpu_and_finish`).

3. **Check each changed function against these concrete tells** (from
   verus-style.md — the files win if they ever disagree):

   - **`requires` are BARE** — no `//` group notes, no `// ---- ----` banners.
   - **`// ---- <title> ----` banners are SINGLE-LINE**, and appear ONLY in
     `ensures` framing and the body's `inv()` re-establishment — never wrapped
     across lines, never in `requires`.
   - **`proof {}` blocks carry NO prose** — bare calls / asserts / reveals.
   - **Doc comments (`///`)** — absent on ordinary wrappers; present ONLY to
     explain the single non-obvious contract point, never to recap the body.
   - **Triggers** — `#![auto]` for shallow "every other entry unchanged" framing
     foralls; hand-written `#![trigger ...]` for deep invariant quantifiers;
     **NEVER `#![all_triggers]`**.
   - **No trigger-compensating asserts (HIGH SIGNAL — raise as a question, not a
     silent finding).** An `inv()` re-establishment should close from a few
     `reveal(...)`s (+ narrow lemma calls), like `wlock_quota_4k`. A hand
     `assert forall|...| ... == old(self)... by { if k != touched { assert(...) } }`
     block sitting BEFORE the conjunct asserts (to feed them) is a crutch for a
     quantifier that should fire on its own — a sign of a mis-set trigger, which is
     the AUTHOR's to fix at the spec/primitive, not to patch at the call site. When
     you see one: (a) flag it, (b) note that the reflex fix is to DELETE it and
     re-verify from the bare reveals, and (c) if you can, actually try the deletion
     (`--fix` path or a scratch check) and report whether it still verifies. If it
     still verifies → it was dead scaffolding, remove it. If it now fails → **do
     NOT conclude "load-bearing" yet.** The block almost always hides its real
     dependency in a NESTED `by { reveal(...) }` (e.g. `assert(dom.contains(aptr))
     by { reveal(container_allocator_wf); }`); deleting the block deletes that
     reveal too, so the conjunct fails for want of the reveal, not the forall.
     Scan the deleted block for every `reveal(...)` it was providing, hoist those
     up beside the conjunct's own reveal, and re-verify. `wlock_allocator_cache`
     collapses a 23-line `assert forall ... == old` block to exactly two reveals
     (`reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf);`)
     this way. Only if it STILL fails after every buried reveal is hoisted is the
     hand-proof real → then surface the trigger gap (do NOT re-add the assert).
     Exempt: asserts that are genuine proof steps (bringing an OLD-state fact into
     scope for a fold lemma, arithmetic, case splits) — the tell is specifically the
     `... == old(self)...` re-framing shape that duplicates what a lock op's
     `ensures` already delivers.
   - **Dead scaffolding around a stub (HIGH SIGNAL).** If the function stubs a
     conjunct with `assume(self.inv())` / `assume(...)` / a `//@Xiangdong` TODO,
     then every ghost snapshot (`let ghost pre_mut = *self;`, `post_pop`,
     `pre_stage_proc`, `storage_addr`, …) and every per-field frame assert
     (`assert(self.X == pre_mut.X)`, the nested `assert(self.memory_management_inv())
     by {...}` rebuild, `_fold_change_one`/`lemma_view_len` re-derivations) that was
     building toward that conjunct is now DEAD — nothing consumes it. Flag it: a
     stubbed body should be lean exec + the live lock-op precondition proofs + the
     stubs, nothing more. Reflex: delete a ghost / frame assert and re-verify; if it
     still passes with the stub in place, it was scaffolding — remove it. Keep ONLY
     what still feeds a LIVE (non-assumed) obligation (e.g. a real `wlock_*` call's
     acyclicity/freshness proof, and the ghost it reads like `cache_lock_id`).
   - **Untrimmed grind-time scaffolding in a GREEN proof (HIGH SIGNAL).** Distinct
     from the stub case: this applies to a proof that fully VERIFIES but still
     carries the intermediate asserts / extra `reveal(...)`s / `let ghost`
     snapshots that were added while grinding it out. A proof found by accretion
     reads long when it's really short. Suspect it when you see: (a) two asserts
     establishing the SAME fact by different routes; (b) a `reveal(...)` that a
     later `by { reveal(...) }` on the goal now subsumes; (c) a `let ghost` read
     only by an assert; (d) an assert that merely PRIMES a state a subsequent
     `by {}` block establishes on its own; (e) a bare `assert(X)` immediately
     before the conjunct/return that consumes X and nothing else. When you see a
     cluster of these, flag it and — if you can (`--fix` path or a scratch check) —
     actually delete the suspect assert/reveal/ghost (farthest-from-goal first),
     re-verify, and report which ones were removable (still green ⟹ dead
     scaffolding, remove) vs load-bearing (fail-on-delete ⟹ keep). This is the
     delete-and-reverify diagnostic run as cleanup. The finished proof should carry
     only the asserts that fail-on-delete; a green body still holding its
     grind-time scaffolding is an unfinished proof, not a finished one.
   - **EVERY `let ghost` snapshot must have a live reader (HIGH SIGNAL — check
     each one).** Ghost snapshots (`let ghost old_self = *self;`, `let ghost
     pre_mut = ...;`, `let ghost old_caches = self.cpu_caches;`, `let ghost old_ll
     = ...;`, `post_pop`, `pre_stage_proc`, `storage_addr`, …) are the single most
     common leftover from grinding — you snapshot the pre-state to compare against,
     then the real proof closes another way and the snapshot is never read. Go
     through EACH `let ghost` in a changed function and find the line that reads it
     (a later assert, a lemma-call argument, a framing conjunct). If nothing reads
     it — or the only readers are asserts you're already flagging as dead — DELETE
     it. Reflex: delete the binding and re-verify; still green ⟹ it was dead, stays
     out. A `let ghost` with no surviving consumer is pure noise that reads as "this
     proof tracks the old state" when it doesn't. Flag every orphaned one; a clean
     proof has zero ghost snapshots that aren't consumed by a live obligation.
   - **Layout** — `&&&` / `|||` alone on its own line before each operand;
     `&&&` = top-level conjuncts, `&&` = inside one conjunct.
   - **Framing** — lists EVERY `final(self).X == old(self).X` field; the touched
     one framed with `unchanged_except`; `=~=` for collections, `==` for scalars.
   - **`inv()` re-establishment is NESTED** — subsystem conjuncts wrapped in
     `assert(self.memory_management_inv()) by { ... }` etc.; banner order
     subsystems_inv → memory_management_inv → process_management_inv →
     inv() direct conjuncts → `assert(self.inv())`.
   - **`#[verifier::spinoff_prover]` is Xiangdong's call — do NOT add it unprompted.**
     Flag any NEW `#[verifier::spinoff_prover]` an edit introduced on its own (existing
     ones HE added are fine and stay). If a new wrapper/helper/lemma is slow enough to
     want spinoff, the reflex is to ask him, not to add it — so a self-added spinoff is
     a violation to raise, and its absence on a new fn is NOT a violation.
   - **Spec files hold ONLY specs** — a `proof fn` in a `*_spec.rs` is a violation;
     it belongs in an impl / `lemma_*` file.
   - **No `@` sugar in NEW code — spell out `.view()` (tooling constraint).** New
     wrappers/lemmas write `x.view()` / `x.view().view()` (and
     `x.view()->Write_lock_id`, `foo.view().linked_list`), never `x@` / `x@@` —
     the code analyzer doesn't resolve `@` well. Flag every `@` view-operator in a
     CHANGED function and give the `.view()` rewrite (it desugars identically, so
     the fix is mechanical and re-verifies unchanged). Scope note: only NEW/edited
     code — do NOT flag `@` in surrounding untouched lines (his live code is dense
     with `@` and is not being churned). `//@Xiangdong` TODO markers are text, not
     the operator — never flag those.
   - **Map-level lock-id** — `map.lock_id_by_key(key)` / `array.lock_id_by_index(i)`,
     never a hand-built `LockId{...}`.
   - **Framing lemmas** — hypothesis scoped to the fields the target-wf actually
     reads, not the whole `view()`.
   - **Naming** — `_4k`/`_2m`/`_1g` triples + non-suffixed combiner; `<from>2<to>`
     conversions; relations `<a>_<b>_wf` in lock-hierarchy order. Preserve the
     load-bearing in-tree typos (`childern`, `processs`, `global_poll`, …).

4. **Report.** List each violation as `path:line — <what> → <the fix>`, grouped
   by file, ordered by severity (comment discipline & `#![all_triggers]` are the
   highest-signal tells). If a construct is genuinely new (no sibling to mirror),
   say so and note which existing shape it's closest to. End with a one-line
   verdict: **clean** or **N violations**.

5. **Clear the gate (clean pass only).** The `Stop` hook
   (`.claude/hooks/style-gate.sh`) blocks stopping while `src/**/*.rs` is dirty and
   newer than the sentinel `.claude/.style-checked`. When — and only when — this
   review comes back **clean** (zero surviving violations), run
   `touch .claude/.style-checked` so the gate clears. If there are violations, do
   NOT touch it: fix them (or hand back to the user) and re-run `/style-check`; the
   gate stays shut until a clean pass. Never `touch` the sentinel by any other route
   — that is the one action that certifies the diff, so it must reflect a real pass.

Do NOT edit `src/` here — this is review-only (the `--fix` path below is the sole
exception). If the user wants fixes applied, they will ask (or pass `--fix` in
`$ARGUMENTS`, in which case apply the fixes after reporting, re-run
`./verify.sh --verify-only-module <changed module>` to confirm nothing broke, then
`touch .claude/.style-checked` to clear the gate).
