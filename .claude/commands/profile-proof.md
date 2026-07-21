---
description: Attribute a Verus function's SMT cost to specific postconditions / inv() asserts by ablation (comment-and-remeasure the rlimit delta)
---

Find WHICH postcondition or WHICH `assert(<inv conjunct>) by {}` is driving a
VeriFlat Verus function's verification cost. Run this on a function that verifies
green but is expensive (high rlimit / slow) and you want to know where the cost
lives BEFORE trying to shrink it. This is the measurement front-end to
`/shrink-proof` — profile first (locate the costly obligation), then shrink or
scope-reveal or (ask-first) fix the trigger on the one that dominates.

`$ARGUMENTS` may name the function / module to target. If empty, use the most
recently edited proof in the session (`.claude/.session-edits`).

## The core idea

Total verification cost of a function is the SUM of the cost of discharging each
proof obligation (every `ensures` clause + every `assert` in the body). You
attribute that sum to individual obligations by **ablation**: remove one
obligation, re-measure, and the DROP in rlimit is that obligation's cost. Rank
the obligations by their deltas; the biggest delta is where the expense is —
and the only place worth spending shrink effort.

**rlimit is the signal, not wall-clock time.** rlimit (the SMT resource count)
is deterministic — the same source produces the same rlimit every run, so a
delta between two variants is real. smt-run time (ms) is noisy (scheduler,
thermal, thread contention); use it only as a secondary sanity check, and if you
must, average 2–3 runs. Report deltas in rlimit.

## Two ablation moves (pick per obligation kind)

1. **Postcondition — COMMENT the `ensures` clause.** Removes the obligation
   entirely. The rlimit drop is the full cost of proving that postcondition
   (including any body steps that existed only to serve it). Clean and coarse:
   tells you "postcondition X costs this much of the total."

2. **Body `assert(X) by { BODY }` — replace the whole thing with `assume(X);`.**
   This is the finer, PREFERRED move for an `inv()` re-establishment. `assume(X)`
   keeps the fact X in downstream context, so nothing after it cascades into new
   failures — you isolate exactly the cost of *establishing* X (the `by { BODY }`
   sub-proof) with no muddying knock-on effects. Deleting the assert instead
   would strip X from context and can topple later obligations, so the delta
   would no longer be attributable to X alone. Use `assume`, not delete, for
   ablating asserts.

Both moves are THROWAWAY measurement edits on a backup — they leave `assume` /
commented `ensures` in the tree, which is forbidden in committed code. The
procedure ends by restoring the file byte-for-byte (shasum match). Never land an
ablation edit.

## Measurement mechanics (confirmed against this Verus build)

Isolate the target function and read its rlimit:

```
./verify.sh --verify-only-module <module> --verify-function <fn> --time-expanded
```

- `--verify-function` matches on a unique substring of the function name and
  needs `--verify-only-module` (or `--verify-module`) to scope it.
- Read the line `total smt-run:   <ms> ms,   <N> rlimit`. With one function
  verified, `<N>` IS that function's rlimit. `<ms>` is the noisy time.
- Machine-readable alternative: add `--output-json` and read
  `times-ms.smt.rlimit-run`. A full-module run's JSON also carries
  `times-ms.smt.smt-run-module-times[0].function-breakdown[]`, each entry a
  `{function, rlimit}` — so one module run attributes rlimit to every function
  at once (handy for picking the target, or measuring several ablations in one
  pass).

**Bump the rlimit ceiling so nothing caps during measurement.** A function that
HITS its `#[verifier::rlimit(N)]` reports the cap, not its true cost (and fails).
Temporarily set a generous `#[verifier::rlimit(BIG)]` (or pass `--rlimit BIG`) so
every variant SUCCEEDS and reports its true consumption. Restore the original
`rlimit` attribute with the byte-for-byte revert at the end. (Do NOT add
`#[verifier::spinoff_prover]` as part of this — that's Xiangdong's call; see
below.)

## Procedure

1. **Scope + backup + baseline.** Identify the target (from `$ARGUMENTS` or the
   session ledger). `cp <file> /tmp/<name>.profile.bak` and record its shasum.
   Confirm it verifies green and capture the BASELINE rlimit with the isolated
   `--time-expanded` command above. If it's near/over its `rlimit(N)`, bump the
   ceiling first so the baseline is a true (uncapped) number.

2. **Enumerate the obligations to ablate.** List the target's `ensures` clauses
   and its body `assert(self.<subsystem>_inv()) by {}` / `assert(self.inv())`
   blocks. For an `inv()` re-establishment, go COARSE→FINE: first ablate the
   three nested combiners (`subsystems_inv`, `memory_management_inv`,
   `process_management_inv`) to find which subsystem dominates, THEN within that
   one ablate its individual conjunct asserts.

3. **Ablate one at a time, re-measure, record the delta.** For each obligation:
   comment the `ensures` (move 1) or swap `assert(X) by {…}` → `assume(X);`
   (move 2) — exactly ONE change from baseline — then re-run the isolated
   `--time-expanded` command and record `baseline_rlimit − variant_rlimit` = that
   obligation's cost. Restore to baseline before the next ablation so every delta
   is measured against the same reference. (To batch: ablate several independent
   asserts and read them all from one full-module `--output-json`
   `function-breakdown` — but keep each delta a single-change diff from baseline.)

4. **Rank and report.** Sort obligations by rlimit delta, largest first. The
   top entries are the costly proofs. Note the shape of the distribution — it
   determines the fix (next section).

5. **Optional drill-down on the dominant obligation** — `--profile-all` on the
   isolated function:
   ```
   ./verify.sh --verify-only-module <module> --verify-function <fn> --profile-all
   ```
   reports `Cost * Instantiations: <cost> (Instantiated K times …) top N of M
   user-level quantifiers` with the trigger selected for each. A quantifier with
   a huge instantiation count is an over-firing (or badly-triggered) quantifier —
   that's the mechanism behind the cost the ablation localized.

6. **Restore byte-for-byte.** `cp /tmp/<name>.profile.bak <file>` back, restore
   the original `#[verifier::rlimit(N)]`, and confirm the shasum matches the
   pre-profile file. Re-run the isolated verify to confirm green. The profiling
   must leave ZERO trace — no `assume`, no commented `ensures`, no bumped rlimit.

## Interpreting the distribution → the fix

- **One obligation dominates (e.g. one subsystem conjunct is 60%+ of the cost).**
  That is the shrink target. Hand it to `/shrink-proof` — the big cost is usually
  a trigger crutch (a hand `== old` frame) or an over-broad reveal feeding one
  conjunct. If `--profile-all` shows a single quantifier over-instantiating on a
  context-dependent trigger, that's a mis-set SPEC trigger → ask-first per
  `feedback_ask_before_invariant_triggers.md`.
- **Cost spread roughly evenly across many obligations (no single dominator).**
  This is the fingerprint of CONTEXT POLLUTION, not one expensive proof: a bare
  `reveal(P)` at `proof {}`/function scope leaks a deep-quantifier body into the
  whole function's SMT context, inflating every downstream obligation a little.
  Fix is to SCOPE the reveals into the `assert(<goal>) by { reveal(P); }` that
  own them (see the reveal-scoping rule in `verus-style.md` / `/style-check`) —
  re-profile after scoping; the flat cost should drop across the board. If it's
  genuinely irreducible cross-obligation cost, `#[verifier::spinoff_prover]`
  (which isolates the function's SMT context) is the remedy — but that is
  Xiangdong's call: flag it, don't add it.
- **Ablating a postcondition drops rlimit far more than its body work suggests.**
  The postcondition is pulling in an expensive lemma/reveal only it needs —
  candidate for a narrower framing lemma or a scoped reveal.

## Relationship to the sibling commands

- `/profile-proof` (this) — LOCATES the costly obligation (measurement only).
- `/shrink-proof` — SHRINKS a located obligation (delete-and-reverify).
- `/discharge-assume` — BUILDS a proof for an `assume`d conjunct by transplanting
  a sibling's reveal recipe (the inverse of shrink: adds real proof where there
  was a stub).
- `/style-check` — FLAGS the tells (bare reveals, `== old` crutches, orphan
  ghosts) that profiling confirms are costing rlimit.
Typical chain: profile → shrink the dominator (or scope its reveals) → re-profile
to confirm the win → style-check → gate.

## Guardrails

- **Measurement only — never land an ablation.** No `assume(...)` / `admit()` /
  commented `ensures` / bumped `rlimit` may survive. Restore byte-for-byte
  (shasum match) and re-verify green before finishing.
- **rlimit is the reported metric**, not wall-clock time (time is noisy; rlimit
  is deterministic). If you cite time, average multiple runs and say so.
- **Do NOT add `#[verifier::spinoff_prover]`** to fix what profiling finds — it's
  Xiangdong's call. Flag it as a candidate; don't apply it.
- **Invariant/opaque-spec triggers are ASK-FIRST**
  (`feedback_ask_before_invariant_triggers.md`). Profiling may point at a mis-set
  spec trigger; present the fix, don't make it unprompted.
- Follow the proof-gap protocol (`veriflat-project-notes.md`): if an ablation
  reveals a real gap (e.g. a postcondition that can't be re-proved after you
  restore), flag it — don't paper over it.
