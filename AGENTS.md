# VeriFlat repository rules

This is the repository-level source of truth for coding agents, including
Codex and Claude. Live code wins over older notes. Preserve the user's dirty
worktree and unrelated edits.

Detailed workflow and model rules live in `.codex/skills/`. Durable design
orientation lives in `.ai-memory/` and is never a specification. Tool-specific
files such as `CLAUDE.md`, `.claude/`, and `.kiro/` are compatibility adapters;
they must point to these canonical sources instead of redefining their rules.

## Terms used in these rules

- K and U: K is the concrete kernel state (`KernelK`) that exec code and its
  contracts describe; U is the user-visible model state (`KernelU`) that K
  projects to through `kernel_k_to_kernel_u`. "K-only" means no U state, U spec,
  or K-to-U projection appears.
- Framing spec, framing lemma: a named spec function or proof function whose
  content is that certain objects or fields are unchanged, or related old to
  new, across a transition. A `requires`/`ensures` clause inside a function's
  own contract is not a framing spec, even when it states what is preserved.
- EOF, EOL, S: EOF is the end-of-function proof structure in which one
  operation-state summary S (`<op>_eof_transition_framing`) records the
  operation's transition and separate closure functions derive the final
  invariants from S. EOL is the same structure for one loop body.
- Focused run: `./verify-workspace.sh --package <pkg> -- --verify-only-module
  <mod>` or `./verify-workspace.sh --package <pkg> -- --verify-function <fn>`.
  Heavy run: a whole-package run, a whole-workspace run, or the monolith
  (`./verify.sh`).

## Scope and semantics

- Read this file before editing.
- Roles. The main agent only plans, talks with the user, and audits. It
  delegates every code, proof, documentation, and verification task to
  subagents, reviews their diffs and run results itself, and keeps only
  read-only inspection for planning and auditing in its own thread.
- Delegation. Delegate routine work within the authorized task automatically,
  without repeated permission. Run work on disjoint files or independent
  diagnoses concurrently within the runtime's available agent slots. Each
  subagent must obey this file and the routed skills: the machine-wide limit
  of two heavy verification jobs, no edits to files under verification, and
  the same approval, style, and reporting rules. Give each explicit, disjoint
  file ownership and require changed files plus verification run numbers in
  its final report. Task-local delegation and run coordination are already
  authorized. Anything that outlives the task needs explicit user permission:
  scheduled or recurring agents, hooks, settings, workflow scripts, and other
  persistent orchestration.
- Codex model policy. Default to `gpt-6.1-sol` for main and implementation
  agents. Escalate genuinely difficult proof, invariant, trigger, or semantic
  problems to `gpt-6-astra`. Use `gpt-6-luna` only for straightforward,
  bounded auxiliary tasks, never primary kernel proof or model design. Start
  at the model's default reasoning effort and raise it as needed. This policy
  applies only to Codex.
- Claude model policy. Claude subagents use Opus 5.5 unless the user requests
  otherwise.
- On both platforms, actual model availability, the user's selection, and
  runtime limits take precedence: never silently substitute an unavailable
  model or claim one was used. Neither policy selects or switches the model of
  the running main agent.
- Coordination. Brief subagents once with complete scope and file paths instead
  of pasted code. Subagents resolve routine issues themselves and report only
  necessary issues and final delivery: changed files, concise results, and
  verification run numbers. Each subagent owns its verification runs and uses
  the runtime's native asynchronous waits or completion notifications, or waits
  on its own background jobs with bounded waits that preserve runtime
  responsiveness. While a subagent is running, the main agent does not duplicate
  its investigation or reasoning, incrementally inspect its task files, diffs,
  logs, or transcript, or poll for routine status. It intervenes only for
  substantive blockers, semantic or authorization questions, or necessary
  cross-task coordination. After delivery the main agent performs one
  consolidated audit of the diffs, verification results, and soundness together;
  targeted rereads follow actual findings or new changes. Avoid repeated full
  diff or log reads and user updates with no new information; satisfy
  platform-required status updates briefly from already known status.
- Run scopes. A subagent verifies only its own scope with focused runs, each
  under `systemd-run --user --scope -p MemoryMax=30G`. Focused runs are light.
  Focused runs on different packages run concurrently within available agent
  slots; focused runs on the same package serialize through the script's
  per-package lock, so two subagents given the same package wait on each other.
  Heavy runs count toward the machine-wide limit of two heavy verification jobs
  at a time. The main agent assigns them to one integration subagent, which
  runs them once per integration or handoff after every focused run is green.
- Git. The repository has three long-lived branches. `main` holds the kernel
  (`src/`, `crates/`), what it needs to boot (`boot/` loader, kernel glue,
  serial driver, `vsys`), and the small `boot/dom0` (hello world plus one short
  self-test per syscall). `proofs` is `main` plus `noninterference/`,
  `liveness/`, and `deadlockfree/`. `bench` is `main` plus the benchmark dom0
  (`boot/dom0-bench`), the device drivers (`boot/ice`, `boot/ice-linux`), and
  `boot/bench/`. Kernel work happens on `main`. After an integration or handoff
  on `main`, merge `main` into `proofs` and `bench`, never the reverse, and run
  each branch's own checks there. Work that touches only a branch's own
  directories is committed on that branch. Do not open other long-lived
  branches. Commit locally and report; the user decides when to push. Commit
  messages carry no AI attribution lines (no `Co-Authored-By` or
  `Generated with` trailers).
- Do not reset, overwrite, restage, or clean unrelated changes. Before launching
  subagents in parallel, freeze the signatures and contracts of every item they
  share; a subagent does not change an item that another running subagent
  depends on.
- A question gets a read-only diagnosis and a report, not a fix. Implementation
  starts only when the user asks for it. If a proof exposes an unclear
  invariant or a mismatch between the model and the code, report it before
  changing the model. Do not invent preconditions, runtime checks,
  representations, or framing bridges to make a proof pass.
- A contract may state directly, as an `ensures` clause, a narrow guarantee the
  operation already provides. A `requires` stays limited to what safety, the
  modeled semantics, or a direct callee's precondition needs.
- Do not introduce `exists` or `choose` in specs, contracts, or proofs. Pass
  concrete arguments and results, and repair producer contracts or triggers
  instead of selecting hidden witnesses or counterexamples.
- Do not write invariants keyed on a thread's `SyscallProgress`: no
  `KernelK::inv`, U-level invariant, or `*_wf` clause of the form
  `thread.syscall_progress is X ==> <facts about other objects>`. State of a
  multi-step syscall that must survive a step boundary belongs in the affected
  object's own (ghost) state, such as a container ghost kill flag, with the
  invariant stated on that object. `SyscallProgress` may still appear in step
  specs, trace lemmas, and exec contracts.
- Runtime performance comes first: a syscall's exec code is designed for
  speed and is never reordered or extended for the sake of the U model. Given
  that exec code, choose U step boundaries as coarse as possible: lock,
  unlock, and ghost-only changes fold into the adjacent recorded step; a
  `u_eq`/`rebase_snapshot_k_if_unchanged` point that stops holding is deleted
  so its stretch merges into the next recorded step, not turned into a new
  step; add a step only when a recorded boundary sits in between and cannot
  move without changing exec code.
- After changing a contract, simplify its callers' old proofs and verify which
  facts are still necessary. Use the typed lock maps directly for lock
  membership and scope; keep the approved predicates and relations listed in
  the kernel-model skill's `lock-model.md`.
- Style. All Verus spec, proof, contract, and exec edits use the dense
  canonical style of the proof skill, repository-wide, with the hand-edited
  `src/kernel/implementation/syscall_alloc_quota/` as the reference. Minimize
  vertical space and keep one logical contract clause per line. A short scoped
  proof with no local `let` binding stays on one line. A block with local `let`
  bindings is never compressed to one line: its opening brace, each `let`
  statement, each `&&&`/`|||` clause, and its closing brace go on separate
  lines. Pack function parameters, call arguments, tuple elements, and
  collection-literal elements into compact readable groups instead of one item
  per line, and wrap long groups across a few balanced lines rather than one
  enormous line. Do not staircase one accessor chain, comparison, implication,
  or other logical expression across lines; wrap only at real semantic
  boundaries. Remove diagnostic or commented-out proof blocks before handoff. A
  green proof is not style-complete until this cleanup and the changed-file
  style audit are done.
- When an invariant does not close automatically, inspect producer triggers and
  quantified fact shape before adding assertions or reveals.
- When deletion-tested closure of one `*_wf` requires other `*_wf` predicates,
  record those confirmed proof dependencies in a concise comment immediately
  before the dependent predicate's definition. Do not document guesses,
  temporary diagnostic reveals, or generic lemmas as invariant dependencies.
- Survey several independent invariant leaves per focused run instead of running
  a per-leaf naked/reveal cycle. A normal survey uses at most two runs
  regardless of the number of candidates: first batch every candidate as a
  separate naked assertion; if that batch is not fully green, rerun the same
  candidates together with each proof body containing only
  `reveal(the_target_predicate)`. Do not run one naked check and one self-reveal
  check per leaf. Candidates with known child-invariant, lemma, or `recommends`
  dependencies do not belong in these batches. A `closed` predicate cannot be
  revealed and stays as a naked assertion if the naked batch proves it. If the
  self-reveal batch fails, reaches rlimit, or shows abnormal SMT time, bisect
  immediately and resume one-leaf trigger/recommendation diagnosis; do not add
  dependency reveals to make a mixed batch pass.
- Before introducing a new framing spec or framing lemma, obtain explicit user
  approval for that specific abstraction. Show its proposed name, complete
  definition or lemma statement, objects and fields preserved, intended use
  sites, and why direct proof or existing relations are insufficient. Reuse,
  performance, and ordinary proof isolation do not waive approval. Names must
  identify what is preserved. Permission to retain an existing spec or lemma
  does not authorize a new one. The only exception is the EOF/EOL structure
  described below.
- Ordinary edits to a function's `requires` and `ensures` do not require
  separate approval, including clauses that state which fields or lock-map
  entries are preserved. Do not classify a normal contract edit as a new
  framing spec merely because it relates old and new states. This does not
  authorize introducing a new framing helper or abstraction.
- Full EOF. One complete operation-state summary S records every mutation and
  preservation fact needed after the operation. The main exec equation
  establishes S but closes no final post-state invariant, invariant group, or
  `*_wf` leaf; intermediate facts needed to execute a later mutation and the
  final lock-map alignment stay in the exec equation. Independently verified EOF
  closure functions outside the exec equation derive all final invariant closure
  from the entry invariants, S, and only the narrow representation facts that
  executed callees already guarantee. Moving or merging inline invariant
  assertions, or summarizing only the fields one invariant needs, is not EOF.
  Introducing this boundary for a long equation, adding its closure functions,
  and reshaping S (adding, removing, strengthening, weakening, or reorganizing
  clauses) need no user approval, as long as S stays a complete
  transition/framing summary, holds no final invariant or `*_wf` closure and no
  operation precondition (those stay in the exec `requires`), and changes no
  model semantics. This exception never covers a reusable or cross-operation
  framing abstraction. EOL applies the same structure and rules to a loop whose
  equation exceeds 5 seconds of SMT time under `--time-expanded`; the proof
  skill's `slow-equation.md` has the details. Names: S is
  `<op>_eof_transition_framing`; EOF-only helper framing is `<op>_eof_<what>`. S
  lives in the operation's `*_eof*.rs` or `*_spec.rs`, never in the exec file.
  Non-EOF framing names state what is preserved (`held_*_unchanged`,
  `kernel_*_nonlock_fields_unchanged`); rename names that do not
  (`*_framed_fields_equal`, `*_kernel_state_framing`).
- Every new proof lemma requires explicit user approval except these four kinds:
  an EOF/EOL closure function; a `*_wf_at` point lemma, which may instantiate
  several predicates at one index; a fold-related lemma; and a K-to-U lemma in
  one of two layers, either a generic K-to-U fact in the step-wrapper layer
  (`src/kernel/kernel_step_wrappers.rs`, `src/kernel/kernel_step_wrappers/`) or
  an operation-local bridging lemma in the operation's `*_trace.rs`
  (`<op>_<step>_pre_from_k`, `<op>_<step>_from_u`, `<op>_result_from_k`, trace
  composition) whose requires are K facts or wrapper ensures verbatim, whose
  ensures are existing U specs of that operation, and which introduces no new
  spec. Any other proof function needs approval, including one placed in the
  wrapper layer and one with an empty body. List every added lemma in the
  report. New framing specs or framing lemmas, reusable cross-operation
  abstractions, new invariants, and any change of model semantics always require
  approval. Every new lemma name states what implies what,
  `<premise>_implies_<conclusion>` (or `<producer>_implies_<fact>` for
  point/frame facts); names like `lemma_*`, `*_helper`, or `*_successor` without
  the conclusion are not accepted.
- Exec equations, including the `locker_unlocker/` primitives, and their own
  contracts are K-only transition proofs: they hold K facts, establish S and
  lock-map alignment, prove callee preconditions, and call the step-boundary
  wrappers, the wrapper layer's K-to-U step lemmas, and the operation's trace
  lemmas. They never `reveal` a `*_wf`/`*_inv` and never reason about U. A
  point fact comes from a `*_wf_at` lemma (the body instantiated at one index
  only, never a map-level or quantified fact) or from a callee's ensures. The
  full rule is in the proof skill's `style-and-discipline.md`.
- Delete dead private helpers after checking callers. Not dead: public
  syscalls, intended public primitives, and proof functions that are theorems
  by nature (environment-event K-to-U lemmas, noninterference lemmas), which
  have no in-tree callers.
- Speed matters. Outside the final cleanup/optimization stage (deletion tests,
  style pass, performance A/B), do not run verification repeatedly: accumulate
  a large batch of related edits before each run, fix every reported error
  together before the next run, and verify the smallest package set covering
  the batch. Never rerun a green verification to measure time: continue and
  judge cost from the rlimit that run already reported. Wall-time measurement
  and interleaved A/B comparisons happen once, for the final report.
- No wall-time regression is accepted by default, and no fixed tolerance
  exists. Follow the build skill's measurement rules and bring a slowdown that
  persists beyond observed variation to the user with the concrete
  simplification and measurements.
- Never use `#[verifier::spinoff_prover]` to paper over a flaky or unstable
  proof (one that fails although every sub-assertion passes, or that flips
  between the split workspace and the monolith). Find the cause — trigger
  shape, quantified context, missing direct fact — and fix the proof itself.
- Every exec loop and every recursive exec function must carry a
  `decreases` clause. `#[verifier::exec_allows_no_decreases_clause]` and
  loops without `decreases` are forbidden outside code explicitly marked as
  TCB. Exec recursion is allowed only when its depth has a physical upper
  bound (container tree depth, page-table levels); a measure that is an
  unbounded ghost quantity (a ghost `nat` such as a call-chain depth) must
  drive a loop, never recursion, to protect the kernel stack. A loop whose
  termination depends on another agent's progress is a model question:
  report it to the user instead of adding the attribute.
- A structurally large verification equation may use a higher rlimit; high
  rlimit alone is not a proof defect. Measure the uncapped equation and use the
  smallest practical ceiling. Any single equation exceeding 10 seconds of SMT
  time under `--time-expanded` is abnormal and must be simplified, context-
  isolated, or split before handoff; raising rlimit does not waive this rule.
- Ad-hoc tooling must never block the session. Run every temporary script and
  bulk text rewrite under `timeout`, test it on the largest target file before a
  batch run, avoid backtracking-prone regexes over whole files, start long
  verification runs in the background and follow them through the runtime's
  completion notification or short bounded log polls, and kill and delete any
  temporary script or stray process before continuing.
- Report verification and proof-performance results in the conversation. Do
  not retain verification reports, handoff records, run logs, profiles, or
  benchmark source snapshots. Temporary measurement files must be removed
  before handoff; the shared verification run counter may remain.

## Required repository skills

The detailed rules live in repository-owned skills so unrelated turns do not
load them. Use every matching skill before acting, and read only the references
that its `SKILL.md` routes to for the current task.

- Use `$veriflat-kernel-model` for locks, `LocalContext`, kernel transitions,
  `mmap_4k` and the other memory syscalls, IPC, and the current syscall model.
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
