---
name: style-check
description: Check the working diff against Xiangdong's Verus style (verus-style.md + canonical files). Use after any major edit to src/ before considering the work done. Reviews only session-touched files and certifies a clean pass.
---

# Style Check

Review the current change for conformance to Xiangdong's VeriFlat Verus style.
Run this after any major edit to `src/` before considering the work done.

## Steps

1. **Get the diff — scoped to this session's edits.** Use `git diff --name-only -- src`
   to identify which `src/**/*.rs` files have been changed. Review ONLY those files.

   - If no files are dirty under `src/`, report **clean** and stop.
   - Otherwise diff only the changed files: `git diff HEAD -- <paths>`
     (add `git diff --staged -- <paths>` if mid-commit).
   - If a base ref is given in arguments, diff against that ref instead of `HEAD`.

   Only review Verus source that actually changed — ignore untouched code.

2. **Load the rubric.** Read `.kiro/steering/verus-style.md`. The canonical
   style references (mirror these — they are HIS code) are:
   - `src/kernel/implementation/syscall_alloc_quota.rs` (`syscall_alloc_quota_4k`,
     `commit_alloc_quota_4k`)
   - `src/kernel/implementation/locker_unlocker.rs` (`wlock_cpu`, `wunlock_quota_4k`,
     `wunlock_process`, ...)
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
   - **Every BARE `reveal(...)` deserves a second look (HIGH SIGNAL).** A
     `reveal(P)` at `proof {}`/function scope opens `P`'s definition for the
     ENTIRE rest of the function's SMT context. For a DEEP-quantifier predicate
     that leaked-open body enlarges the E-matching search space for every
     downstream assert. The fix is to SCOPE it: move the `reveal(P)` inside the
     `assert(<goal>) by { reveal(P); }` that actually consumes it.
     EXEMPT: a bare reveal is fine (a) when the same predicate is consumed by
     several sibling asserts (scoping would duplicate it N times), or (b) when
     it is delete-and-reverify load-bearing AND removing it fails the function.
   - **Doc comments (`///`)** — absent on ordinary wrappers; present ONLY to
     explain the single non-obvious contract point.
   - **Triggers** — `#![auto]` for shallow framing foralls; hand `#![trigger ...]`
     for deep invariant quantifiers; **NEVER `#![all_triggers]`**.
   - **No trigger-compensating asserts (HIGH SIGNAL).** An `inv()`
     re-establishment should close from a few `reveal(...)`s (+ narrow lemma
     calls). A hand `assert forall|...| ... == old(self)... by { if k != touched
     { assert(...) } }` block is a crutch for a quantifier that should fire on
     its own. When you see one: (a) flag it, (b) try the deletion and re-verify,
     (c) if it fails, scan for buried `reveal(...)`s, hoist them, re-verify.
   - **Dead scaffolding around a stub (HIGH SIGNAL).** If the function stubs a
     conjunct with `assume(...)` / `//@Xiangdong` TODO, then every ghost snapshot
     and per-field frame assert building toward that conjunct is DEAD. Flag it.
   - **Untrimmed grind-time scaffolding in a GREEN proof (HIGH SIGNAL).** A proof
     found by accretion reads long when it's really short. Suspect: (a) two
     asserts establishing the SAME fact; (b) a `reveal(...)` a later `by {}`
     subsumes; (c) a `let ghost` read only by an assert; (d) an assert that
     merely PRIMES a state a subsequent `by {}` establishes on its own.
   - **EVERY `let ghost` must have a live reader (HIGH SIGNAL).** Go through EACH
     `let ghost` and find the line that reads it. If nothing reads it — DELETE it.
   - **Layout** — `&&&` / `|||` alone on its own line before each operand;
     `&&&` = top-level conjuncts, `&&` = inside one conjunct.
   - **Framing** — lists EVERY `final(self).X == old(self).X` field; the touched
     one framed with `unchanged_except`; `=~=` for collections, `==` for scalars.
   - **`inv()` re-establishment is NESTED** — subsystem conjuncts wrapped in
     `assert(self.memory_management_inv()) by { ... }` etc.
   - **`#[verifier::spinoff_prover]` is Xiangdong's call — do NOT add it unprompted.**
   - **Spec files hold ONLY specs** — a `proof fn` in a `*_spec.rs` is a violation.
   - **No `@` sugar in NEW code — spell out `.view()`.** Only flag `@` in
     CHANGED functions, not surrounding untouched lines.
   - **Map-level lock-id** — `map.lock_id_by_key(key)` / `array.lock_id_by_index(i)`,
     never a hand-built `LockId{...}`.
   - **Naming** — `_4k`/`_2m`/`_1g` triples + non-suffixed combiner; `<from>2<to>`
     conversions; relations `<a>_<b>_wf` in lock-hierarchy order.

4. **Report.** List each violation as `path:line — <what> -> <the fix>`, grouped
   by file, ordered by severity. End with a one-line verdict: **clean** or
   **N violations**.

5. **Clear the gate (clean pass only).** When — and only when — this review comes
   back **clean** (zero surviving violations), record the certification:

   ```bash
   : > .qoder/.style-checked
   for f in $(git diff --name-only -- src | grep '\.rs$'); do
     printf '%s\t%s\n' "$(git hash-object "$f")" "$f" >> .qoder/.style-checked
   done
   ```

   If there are violations, do NOT regenerate it: fix them and re-run
   `/style-check`. The gate stays shut until a clean pass.

Do NOT edit `src/` here — this is review-only (the `--fix` path in arguments is
the sole exception). If the user wants fixes applied, they will ask (or pass
`--fix`, in which case apply the fixes after reporting, re-run
`./verify.sh --verify-only-module <changed module>` to confirm nothing broke,
then regenerate `.qoder/.style-checked` to clear the gate).
