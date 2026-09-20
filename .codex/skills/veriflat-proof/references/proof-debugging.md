# Proof debugging

- Reproduce the first failure with the smallest function/module command before
  changing proof shape. Classify it as a missing semantic fact, producer shape,
  trigger/reveal issue, or resource cost.

## Invariant closure

- Survey a small set of independent invariant leaves per focused run. First
  batch them as separate naked `assert(target_wf(...));` checks so established
  sub-invariants, producer contracts, and terms already present in each goal
  get a chance to close them automatically. Treat the survey as one batch, not
  as a sequence of per-leaf experiments.
- If the naked batch is not fully green, rerun the same candidates as a
  self-reveal-only batch, with each assertion having exactly this shape:
  `assert(target_wf(...)) by { reveal(target_wf); };`
  Thus a normal survey uses at most two runs regardless of candidate count. Do
  not fall back to a separate naked/reveal pair of runs for every candidate.
  Include no candidate with a known child-invariant, lemma, quantified bridge,
  or unmet-`recommends` dependency. Do not put a `closed` predicate in the
  self-reveal batch: its body is unavailable, so keep its naked assertion when
  the naked batch proves it. A green naked batch classifies every candidate as
  automatic; a green second batch classifies the revealable candidates as at
  most self-reveal-only. If the second batch fails, reaches rlimit, or shows
  abnormal SMT time, bisect the candidates immediately and continue the normal
  one-leaf workflow. Do not broaden the batch proof to make it pass.
- If automatic closure fails or reaches rlimit, first isolate that one proof.
  Temporarily comment out unrelated invariant-closing assertions and proof
  blocks that do not produce facts consumed by the target. Do not bypass
  executable mutations, callee safety obligations, or producer facts on the
  target's lookup chain. Restore every diagnostic cutoff after the focused run.
- In the isolated proof, expand the invariant and write each top-level conjunct
  as a separate temporary `assert(...)`. Split a failing quantified body or
  nested conjunction again until Verus identifies the first failing term and
  reports any unmet `recommends`. Do this before guessing a trigger, lemma, or
  reveal fix. Remove the expanded diagnostic after moving the minimal fact to
  the real scoped goal.
- If automatic closure fails, inspect one cause at a time in this order:
  1. Trace the quantified trigger and lookup chain from the concrete changed
     object to the failing leaf. Compare a nearby proof of the same or analogous
     invariant and check whether the producer exposes every term needed to
     instantiate that chain.
  2. Check for an existing operation, relation, or generic Set/Seq/Map lemma
     whose conclusion directly supplies the missing fact. Call it only in the
     consuming invariant assertion.
  3. Check whether an opaque wrapper or prerequisite relation needs a reveal.
     Add the smallest scoped reveal set, one reveal at a time; do not use a broad
     reveal fan-out.
- Reverify after each hypothesis. Once the check closes, remove each added
  assertion, lemma call, and reveal separately and retain only fail-on-delete
  proof.
- If the resulting deletion-tested proof for one `*_wf` requires other `*_wf`
  predicates, add a short `Proof dependencies (confirmed): ...` comment
  immediately before the dependent predicate's definition. List only
  predicates that remain necessary after shrinking; do not list transient
  diagnostics, ordinary algebra lemmas, or speculative dependencies.
- If the invariant still does not close after checking the trigger chain,
  existing lemmas, and minimal reveals, stop before changing the model,
  contracts, common triggers, or adding a helper. Ask the user with the exact
  failed invariant leaf and direction, the chain gap found, the lemmas and
  reveals tested, and the concrete alternatives that need a decision.
- A missing algebra or lookup fact is a proof-fact gap. Report an actual semantic
  mismatch before changing the model; do not pass the desired post invariant as
  a precondition or hide its closure inside an operation-specific wrapper.

## Proof fact scope and context hygiene

- In `assert(goal) by { ... }`, intermediate facts established inside the
  `by` block are scoped to that block and do not enter later verification
  conditions. The proved `goal` does enter the surrounding solver context and
  remains available to every later verification condition in the function.
- Treat every standalone `assert(goal)` as a permanent context addition, even
  when its proof is locally scoped. Before adding one, ask whether a later
  callee or final invariant actually consumes `goal`; otherwise keep the fact
  inside the narrow assertion that needs it or delete it.
- Do not repeatedly assert broad opaque invariants, map-wide permission
  predicates, conjunction wrappers, or quantified framing relations at
  intermediate states. Their conclusions persist, and a later reveal can unfold
  every accumulated state instance into the same solver context.
- Keep preconditions to safety, operation semantics, and direct callee needs.
  An unnecessarily broad precondition forces every caller to materialize and
  retain facts that the operation does not consume.
- Keep postconditions to direct operation guarantees and facts that callers
  genuinely consume. An unnecessarily broad or indirect postcondition becomes
  a permanent fact at every call site and can seed unrelated quantifier
  instantiations. Prefer exact field updates and narrow preservation clauses over
  aggregate invariant results.
- Scope reveals and lemma calls inside the assertion that consumes them. A lemma
  call outside such a block leaves its entire quantified conclusion in all later
  verification conditions. Move a shared fact outward only after a deletion
  test proves that multiple later goals require the same conclusion.
- When auditing context leakage, inspect the complete call chain: caller entry
  assertions, callee `requires`, callee `ensures`, and post-call assertions.
  Narrowing only the caller proof does not help if a broad callee result
  immediately reintroduces the same fact.

- For a suspected trigger crutch, delete the call-site `assert forall` and
  reverify. If it fails, move only any buried reveals into the consuming
  assertion and retry; report a trigger gap only after that still fails.
- For an opaque `*_wf` or unmet `recommends`, temporarily assert its
  conjunction, then bisect conjuncts to find the first missing dependency.
  Move the minimal reveals/facts to the real scoped goal and remove the
  expanded diagnostic.
- Delete suspected asserts, reveals, and ghosts one at a time. A failure after
  deleting a block may mean a nested reveal was lost, not that the block's
  quantified conclusion was necessary.
- After changing result or constructor contracts, revisit the callers' old tail
  assertions, state rechecks, lemma calls, and history snapshots. Test deletion
  before adding more scaffolding. A more direct contract changes solver search;
  it does not guarantee that the old proof remains efficient.
- If several branches need the same fact, prove it once at a common point where
  it holds and subsequent callee guarantees preserve it. Keep the reveal scoped
  to that assertion. Verify that later mutations or interleaving cannot invalidate
  it, and retain only facts required by deletion tests.
- Diagnose cumulative cost with identical cache/thread scope and successive
  semantic boundaries. Use a temporary `assume(false)` cutoff only with
  explicit authorization, one cutoff at a time, and restore it immediately.
- Record the focused run number and SMT/wall/rlimit for each retained proof or
  scheduling change. Never leave diagnostic scaffolding in the tree.
