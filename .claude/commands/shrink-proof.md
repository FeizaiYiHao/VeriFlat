---
description: Diagnose difficult/mis-set triggers and shrink a Verus proof to its genuine content (delete-and-reverify)
---

Shrink a VeriFlat Verus proof by finding the trigger problems behind its
"difficult asserts" and stripping every step that is scaffolding rather than
proof content. Run this on a function whose `inv()` re-establishment (or any
proof block) has grown large with hand `assert(...)` grinds.

`$ARGUMENTS` may name the function / module / file to target. If empty, use the
most recently edited proof in the session (`.claude/.session-edits`).

## The core idea (what Xiangdong taught)

A proof found by accretion reads 10× longer than the real proof. The bulk of a
big hand-grind is **trigger crutches** — steps that manually re-supply a term the
SMT would have if a quantifier's trigger fired on its own. The job is to
distinguish crutch from genuine content and delete the crutch.

**The tell of a trigger crutch (highest signal):** a hand
`assert(self.X == old(self).X)` byte-frame restatement, or an
`assert(old(self)...matches ...)` / `assert(old(self)...contains(...))`
materialization, sitting BEFORE a conjunct to feed it. When the mutation
primitive already exposes `unchanged_except`/framing in its `ensures`, and the
spec's own forward/reverse quantifier triggers are present, the e-graph rewrites
`self...` to `old...` by congruence and the revealed old-wf closes it — so the
restatement is dead weight. (This is the same rule as verus-style.md's "no
trigger-compensating asserts", applied as a cleanup sweep.)

**Two root causes, two fixes:**

1. **Proof-side accretion (fix freely).** The `assert(self.X==old.X)` frames,
   `old...matches` materializations, redundant `reveal(...)`s a later reveal
   subsumes, `let ghost` snapshots with no live reader, `page_index_wf`/`!=`
   primers a subsequent step establishes on its own. Delete these — they are not
   proof content. No permission needed; they live in the proof body.

2. **A mis-set trigger on the SPEC (ASK FIRST — see below).** When a spec
   quantifier's ONLY trigger is a context-dependent term (e.g. a reverse clause
   triggering on `array[i]@.locked_by(lctx)` — lctx-dependent), it can't fire
   after the context shifts (a `lock_map.insert`, a map mutation), because the
   solver has no context-independent handle on `array[i]`. The real fix is a
   structural, context-independent trigger on the spec quantifier itself
   (`#![trigger array[i]]` / `#![trigger map.spec_index(p)...]` /
   `#![trigger map.spec_index(p).cpu_caches.spec_index(c)]`). That single spec
   edit can retire an entire hand-written framing lemma. **This is an invariant
   change — do NOT make it unprompted; present it to Xiangdong (see
   `feedback_ask_before_invariant_triggers.md`).**

## Genuine content (never delete — these fail-on-delete for a real reason)

- **Cross-invariant facts**: a `dom().contains(x)` proved via a DIFFERENT wf's
  reveal (`container_page_owner_wf` for owner-in-map), `page_ptr_valid(addr)`
  pulled from `pagetables_inv`/`pagetable_perms_wf` so a `page_ptr2page_index`
  round-trip is valid on a reverse clause.
- **Round-trip / arithmetic lemmas**: `page_ptr_lemma1()`, `page_index_lemma()`,
  `seq_skip_lemma::<T>()`, the fold axioms.
- **Genuine case splits with content in a branch** (e.g. the popped-cache
  `if alloc==touched && cpu==touched { seq_skip_lemma(); <one map/membership fact> }`).
- **The shallow "every other entry unchanged" framing forall** IF it fails on
  delete — but test it: after the per-clause crutches are gone it is often
  redundant (the mutation primitive's `unchanged_except` already feeds it).

## Procedure

1. **Scope + baseline.** Identify the target function (from `$ARGUMENTS` or the
   session ledger). Back it up: `cp <file> /tmp/<name>.bak`. Confirm it verifies
   green NOW: `./verify.sh --verify-only-module <module>` (note the verified/errors
   counts and any pre-existing `recommendation not met` noise to ignore).

2. **Inventory the difficult asserts.** Find the hand-grind blocks — the ones with
   `assert(self.X == old(self).X)`, `assert(old(self)...matches/contains ...)`,
   repeated `let ghost` snapshots, per-clause `assert forall|..| ...` transport
   with inner `if k != touched { assert(...) }`. These are the candidates.

3. **Delete-and-reverify, farthest-from-goal first.** For each candidate assert /
   reveal / ghost / whole inner block:
   - Delete it (or reduce a `by { ...crutch... }` to `by { }` / just its genuine
     reveal).
   - `./verify.sh --verify-only-module <module>`.
   - **Still green ⟹ it was scaffolding. Leave it out.**
   - **Fails ⟹ do NOT conclude "load-bearing" yet.** First check the deleted block
     for a `reveal(...)` it was secretly providing inside a nested `by {}`; hoist
     that reveal up beside the conjunct and re-verify. Only if it STILL fails after
     every buried reveal is hoisted is the step genuine — restore the MINIMAL form
     (usually one reveal or one lemma call, not the whole block).
   Work one change at a time so each failure is attributable. When a whole
   subsystem conjunct's `by {}` collapses, try the minimal shape first: the reveals
   for that conjunct's opaque predicates + the one round-trip lemma
   (`page_ptr_lemma1()`), mirroring how the same conjunct is proved in
   `locker_unlocker.rs` (`wlock_page`/`wunlock_page`) — those are the reference
   minimal proofs for a page retype / lock-state change.

4. **If a conjunct won't shrink below a hand `== old` frame** — that is the signal
   of a mis-set SPEC trigger (root cause 2). STOP. Locate the spec quantifier whose
   trigger is context-dependent. Draft the structural-trigger fix, then present it
   to Xiangdong per `feedback_ask_before_invariant_triggers.md`:
   (a) the exact `#![trigger ...]` delta on the spec,
   (b) what it enables (e.g. "lets `lemma_X_preserved_for_...` be deleted and its
       call collapse to a bare `reveal`"),
   (c) confirmation the full crate still verifies.
   Do not edit the invariant spec until he approves. If he declines, keep the
   framing lemma / hand frame — it is then the accepted cost.

5. **Full-crate verify.** Spec-trigger changes have a 400+-function blast radius
   (every function that reveals the predicate re-shapes its instantiation). After
   any spec change — and once at the end regardless — run the WHOLE `./verify.sh`,
   not just the module, and confirm the count is unchanged and no other function
   slowed to an rlimit. Also `time ./verify.sh --verify-only-module <module>` to
   check the target didn't blow up.

6. **Trim the orphans the shrink created.** When a lemma call is collapsed to a
   reveal, its `let ghost` args (`pre_wlock_pages`, `page_lid`, …) are now unread —
   delete them (re-verify). When a framing lemma loses its last caller, delete the
   lemma. Audit EVERY surviving `let ghost` for a live reader.

7. **Report + gate.** Summarize: which asserts were scaffolding (removed), which
   were genuine (kept, with the one-line reason each fails-on-delete), and any
   spec-trigger fix proposed/applied. Then run `/style-check` on the touched files
   and land a clean pass (it gates the Stop hook).

## Proven results (this pattern, on `pop_stage_4k_page`)

- `page_pagetable_wf` (mapped_{4k,2m,1g} transport): ~120 lines → 8 (5 reveals +
  `page_ptr_lemma1()`); every `== old` byte-frame + `old...matches` + per-clause
  reveal was scaffolding. The mutation's `unchanged_except` + the spec's
  `mappings().contains` / `mapping_Nk().contains_key` triggers close it.
- `container_allocator_free_{2m,1g}_page_wf` (allocator byte-equal): ~75 → 3 each
  (`reveal(spec)` + `reveal(allocator_free_page_ptrs_wf)` + `page_ptr_lemma1()`).
- `container_allocator_free_4k_page_wf` (dual change: cache popped + page retyped):
  ~115 → ~70; kept only genuine content per clause — `reveal(container_page_owner_wf)`
  (cross-inv dom), `seq_skip_lemma()` + one map/membership fact (popped-cache),
  reverse-global_poll closed with an EMPTY `by {}` (trigger fires alone).
- Structural-trigger fixes (approved) that retired three framing lemmas:
  `#![trigger page_array[i]]` on `page_locked_match_lctx`,
  `#![trigger cpu_array[c]]` on `cpu_locked_match_lctx`,
  `#![trigger alloc_map.spec_index(p)]` / `...cpu_caches.spec_index(c)]` on
  `allocator_locked_match_lctx` — each let the lemma call collapse to a bare
  `reveal(..._locked_match_lctx)`.

## Guardrails

- **Never** leave the target non-green, and never `assume(...)`/`admit()` to force a
  shrink. If a step is genuinely needed and won't shrink, it stays.
- **Invariant/opaque-spec triggers are ASK-FIRST** (`feedback_ask_before_invariant_triggers.md`).
  Proof-body edits are free.
- Follow the proof-gap protocol (`veriflat-project-notes.md`): if a shrink exposes a
  real spec/proof gap, flag it — don't paper over it.
- `#![auto]` for shallow framing foralls, hand `#![trigger]` for deep ones, NEVER
  `#![all_triggers]`. Spell out `.view()` (no `@`) in anything you add.
