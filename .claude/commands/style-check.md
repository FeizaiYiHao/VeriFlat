---
description: Check the working diff against Xiangdong's Verus style (verus-style.md + canonical files)
---

Review the current change for conformance to Xiangdong's VeriFlat Verus style.
Run this after any major edit to `src/` before considering the work done.

## Steps

1. **Get the diff.** Run `git diff HEAD -- 'src/**/*.rs'` (add `git diff --staged`
   if mid-commit). If a base ref is given in `$ARGUMENTS`, diff against that
   instead. Only review Verus source that actually changed — ignore untouched code.

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
   - **Layout** — `&&&` / `|||` alone on its own line before each operand;
     `&&&` = top-level conjuncts, `&&` = inside one conjunct.
   - **Framing** — lists EVERY `final(self).X == old(self).X` field; the touched
     one framed with `unchanged_except`; `=~=` for collections, `==` for scalars.
   - **`inv()` re-establishment is NESTED** — subsystem conjuncts wrapped in
     `assert(self.memory_management_inv()) by { ... }` etc.; banner order
     subsystems_inv → memory_management_inv → process_management_inv →
     inv() direct conjuncts → `assert(self.inv())`.
   - **`#[verifier::spinoff_prover]`** on every new wrapper/helper/proof fn.
   - **Spec files hold ONLY specs** — a `proof fn` in a `*_spec.rs` is a violation;
     it belongs in an impl / `lemma_*` file.
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
