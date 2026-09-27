# VeriFlat repository rules

This is the repository-level source of truth for Codex. Live code wins over
older notes. Preserve the user's dirty worktree and unrelated edits.

Detailed workflow and model rules live in `.codex/skills/`. Durable design
orientation lives in `.ai-memory/` and is never a specification. Tool-specific
files such as `CLAUDE.md`, `.claude/`, and `.kiro/` are compatibility adapters;
they must point to these canonical sources instead of redefining their rules.

## Scope and semantics

- Read this file before editing.
- Do not use subagents without explicit user permission. When authorized,
  give subagents explicit file ownership and require them to report changed
  files plus verification run numbers.
- Do not reset, overwrite, restage, or clean unrelated changes. Freeze shared
  APIs before parallel verification.
- Diagnose questions read-only. Implement only when asked. If a proof exposes
  an unclear invariant or semantic mismatch, report it before changing the
  model. Do not invent preconditions, runtime checks, representations, or
  framing bridges.
- A direct postcondition may expose an operation's existing narrow guarantee.
  Preconditions stay limited to safety, semantics, and direct callees.
- Do not introduce `exists` or `choose` in specs, contracts, or proofs. Pass
  concrete arguments and results, and repair producer contracts or triggers
  instead of selecting hidden witnesses or counterexamples.
- After changing a contract, simplify its callers' old proofs and verify which
  facts are still necessary. Use typed lock maps directly for lock membership
  and scope; preserve the approved relations described by the kernel-model skill.
- All Verus spec, proof, contract, and exec edits must use the dense canonical
  style in the proof skill, with `syscall_alloc_quota/` as the hand-edited
  reference. Minimize vertical space, keep one logical contract clause per
  line, and keep short scoped proofs on one line, except blocks with local
  `let` bindings: put the opening brace, each `let`
  statement, each `&&&`/`|||` clause, and the closing brace on separate lines.
  This applies repository-wide to spec, contract, proof, and exec blocks;
  never compress these blocks into a single line. Pack function parameters,
  call arguments, tuple elements, and collection-literal elements into compact
  readable groups instead of defaulting to one item per line; wrap long groups
  across a few balanced lines rather than forcing one enormous line. Do not
  staircase one accessor chain, comparison, implication, or other logical
  expression across lines; wrap only at real semantic boundaries. Remove
  diagnostic/commented proof blocks before handoff. A green proof is not
  style-complete until this cleanup and the changed-file style audit are done.
- When an invariant does not close automatically, inspect producer triggers and
  quantified fact shape before adding assertions or reveals.
- When deletion-tested closure of one `*_wf` requires other `*_wf` predicates,
  record those confirmed proof dependencies in a concise comment immediately
  before the dependent predicate's definition. Do not document guesses,
  temporary diagnostic reveals, or generic lemmas as invariant dependencies.
- Survey several independent invariant leaves per focused run instead of
  running a per-leaf naked/reveal cycle. A normal survey uses at most two runs
  regardless of the number of candidates: first batch every candidate as a
  separate naked assertion; if that batch is not fully green, rerun the same
  candidates together with each proof body containing only
  `reveal(the_target_predicate)`. Do not run one naked check and one self-reveal
  check per leaf. Candidates with known child-invariant, lemma, or `recommends`
  dependencies do not belong in these batches. A `closed` predicate cannot be
  revealed and stays as a naked assertion if the naked batch proves it. If the
  self-reveal batch fails or its SMT cost is abnormal, bisect immediately and
  resume one-leaf trigger/recommendation diagnosis; do not add dependency
  reveals to make a mixed batch pass.
- Before introducing a new framing spec or framing lemma, obtain explicit user
  approval for that specific abstraction. Show its proposed name, complete
  definition or lemma statement, objects and fields preserved, intended use
  sites, and why direct proof or existing relations are insufficient. Reuse,
  performance, and ordinary proof isolation do not waive approval. Names must
  identify what is preserved. Permission to retain an existing spec or lemma
  does not authorize a new one.
  The one operation-specific state summary S and independently verified closure
  functions used to introduce full EOF for a long equation are the exception:
  they may be introduced without separate user approval. S may also be freely
  reshaped without approval, including adding, removing, strengthening,
  weakening, or reorganizing its clauses. S must remain a complete
  transition/framing summary, may not contain final invariants or `*_wf`
  closure, and may not change model semantics. This exception does not authorize
  reusable or cross-operation framing abstractions.
- Every new proof lemma requires explicit user approval unless it is an EOF
  closure function, a step-wrapper-layer lemma in `kernel_step_wrappers.rs`,
  or a fold-related lemma. Operation-local K→U bridging lemmas placed next to
  an exec function are not exempt: state the generic K→U fact in the
  step-wrapper layer and derive the operation's step predicates from it.
- Ordinary edits to a function's `requires` and `ensures` do not require
  separate approval, including clauses that state which fields or lock-map
  entries are preserved. Do not classify a normal contract edit as a new
  framing spec merely because it relates old and new states. This does not
  authorize introducing a new framing helper or abstraction.
- Delete dead private helpers after checking callers. Public syscalls and
  intended public primitives are not dead merely because they lack in-tree
  callers.
- There is no fixed acceptable wall-time regression. Follow the build skill's
  measurement rules and bring a persistent slowdown beyond observed variation
  to the user with the concrete simplification and measurements.
- A structurally large verification equation may use a higher rlimit; high
  rlimit alone is not a proof defect. Measure the uncapped equation and use the
  smallest practical ceiling. Any single equation exceeding 10 seconds of SMT
  time under `--time-expanded` is abnormal and must be simplified, context-
  isolated, or split before handoff; raising rlimit does not waive this rule.
- Full EOF means one complete operation-state summary S records every mutation
  and preservation fact needed after the operation. The main exec equation
  establishes S but does not close any final post-state invariant, invariant
  group, or `*_wf` leaf. Independently verified EOF proof functions outside the
  exec equation derive all final invariant closure from the entry invariants, S,
  and only narrow representation facts already guaranteed by executed callees.
  Moving or merging inline invariant assertions, or summarizing only the fields
  needed by one invariant, is not EOF. Intermediate facts required to execute a
  later mutation and final lock-map alignment remain in the exec equation.
  Introducing this full-EOF boundary for a long equation does not require user
  approval. S may be changed freely without approval, including adding,
  removing, strengthening, weakening, or reorganizing clauses, as long as the
  preceding completeness, semantic, and framing constraints are preserved.
- Ad-hoc tooling must never block the session. Run every temporary script and
  bulk text rewrite under `timeout`, test it on the largest target file before
  a batch run, avoid backtracking-prone regexes over whole files, start
  long verification runs in the background and poll their logs, and kill and
  delete any temporary script or stray process before continuing.
- Report verification and proof-performance results in the conversation. Do
  not retain verification reports, handoff records, run logs, profiles, or
  benchmark source snapshots. Temporary measurement files must be removed
  before handoff; the shared verification run counter may remain.

## Required repository skills

The detailed rules live in repository-owned skills so unrelated turns do not
load them. Use every matching skill before acting, and read only the references
that its `SKILL.md` routes to for the current task.

- Use `$veriflat-kernel-model` for locks, `LocalContext`, kernel transitions,
  `mmap_4k`, IPC, and the current syscall model.
- Use `$veriflat-proof` for Verus spec/proof/exec edits or reviews, proof
  debugging, invariant closure, trigger work, or proof-performance changes.
- Use `$veriflat-build` for crate/module/API boundaries, Cargo-Verus workspace
  changes, verification runs, measurements, and final handoff.

The canonical skill sources are under `.codex/skills/`. If a fresh Codex
process has not discovered one yet, open its `SKILL.md` there directly and
follow the same routing.

## Durable project memory

Read `.ai-memory/MEMORY.md` only when the task touches one of its routed design
topics. Re-check every note against live code and the matching repository skill.
Do not put proof workflow, verification procedure, session state, measurements,
or completed handoff history in project memory.
