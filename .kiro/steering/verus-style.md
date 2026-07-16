# VeriFlat — Verus code-style signature

How to write VeriFlat Verus code that looks like Xiangdong wrote it. This is
the SURFACE-STYLE delta over `verus-verification.md` (which covers the cost
playbook & TCB-axiom design); this covers layout, naming, idiom, and the
concrete proof-structure patterns that recur across the lock wrappers.

**Canonical style references — mirror these, they are HIS code:**
`kernel/implementation/syscall_alloc_quota.rs` (the `syscall_alloc_quota_4k`
syscall + `commit_alloc_quota_4k` helper) and the `kernel/implementation/
locker_unlocker.rs` wrappers (`wlock_cpu`, `wunlock_quota_4k`, `wunlock_process`,
…). When in doubt about layout, comment density, banner form, `requires`/`ensures`
shape, or trigger idiom, open the nearest LIVE function in these two files and
copy its shape. Do NOT calibrate against commented-out/`/* */` code or the dead
templates (`finish_empty_user_step`, `release_cpu_and_finish`) — those are not
his current style. The rules below are extracted FROM these files; the files win
if they ever disagree.

## Match these

- **Layout:** `&&&` / `|||` connector ALONE on its own line before each
  operand, even single-clause specs. `&&&` = top-level conjuncts; `&&` =
  inside one conjunct's body.
- **Naming:** `wf()` well-formedness, `view()`/`@` abstraction, `inv()` =
  thin `&&& self.wf()` shell. Spec twin = `spec_X` + `#[verifier(when_used_as_spec(spec_X))]`.
  Conversions `<from>2<to>` with literal digit (`page_index2page_ptr`).
  Relations `<a>_<b>_wf` in lock-hierarchy order. Page sizes always
  `_4k`/`_2m`/`_1g` triples + non-suffixed combiner. Pointers `RwLock<Obj>Ptr`.
  Contract helpers `<op>_ensures`/`<op>_requires` (thin call in the primitive's ensures).
- **Decompose:** many tiny `#[verifier::opaque] pub open spec fn` sub-preds;
  a NON-opaque combiner `&&&`s them. Never one monolithic invariant.
- **Triggers:** hand-written `#![trigger ...]` on the deepest lookup chain of
  every DEEP invariant quantifier; re-issue `reveal()` inside every nested `by`
  block. For a SHALLOW framing forall (the "every other entry unchanged" shape,
  `forall|k| dom.contains(k) && k != touched ==> self[k] == old[k]`) use
  `#![auto]` — that's the LIVE idiom in `wunlock_quota_4k`. NEVER `#![all_triggers]`.
- **No trigger-compensating asserts (high value — the tell that you have a
  trigger bug, not a proof gap):** an `inv()` re-establishment should close with
  a few `reveal(...)`s (+ the narrow fold/preservation lemma calls) — look at how
  `wlock_quota_4k` / `wunlock_process` prove each subsystem conjunct with just
  `by { reveal(...); }`. If you find yourself adding a hand `assert forall|...| ...
  == old ... by { if k != touched { assert(...) } }` block BEFORE the conjunct
  asserts to make them go through, STOP: that block is not proof content, it is a
  crutch for a quantifier that should have fired on its own. Needing it means the
  relevant trigger is mis-set — too conservative, badly chosen, or (rarely — you
  hit rlimit first) the instantiation search space blew up. That is Xiangdong's
  job to fix at the trigger site (the spec's `#![trigger ...]` or the primitive's
  `ensures` shape), NOT to paper over at the call site. DELETE the assert, confirm
  it still verifies from the bare reveals; if it then fails, that is the signal to
  flag the trigger gap (proof-gap protocol) — do not re-add the assert. A wrapper
  whose `inv()` rebuild carries `assert forall ... == old` scaffolding is a review
  finding, not a finished proof.
  - **When the delete-and-reverify FAILS, the culprit is usually a missing
    `reveal`, not a real proof obligation — hoist it before you conclude
    "load-bearing" (learned the hard way).** A hand `assert forall|c_ptr| ...
    quota fold ... by { assert(dom.contains(aptr)) by { reveal(container_allocator_wf); }; ... }`
    block hides its real dependency inside a NESTED `by { reveal(...) }`. Deleting
    the outer block ALSO deletes that buried reveal, so the conjunct fails — but
    that failure is the missing reveal, not the forall. The fix is NOT to keep the
    forall: hoist the buried reveal up beside the conjunct's own reveal
    (`by { reveal(container_process_allocator_quota_4k_wf); reveal(container_allocator_wf); }`)
    and the `#![trigger ...allocator_ptr_4k]` fires on its own — the fold args are
    byte-equal on a lock op, so congruence closes the sum with zero hand-proof.
    This is exactly how `wlock_allocator_cache` collapses a 23-line `assert forall
    ... == old` block to two reveals. Diagnostic order: (1) delete the block; (2)
    if it fails, scan the deleted block for `reveal(...)` calls it was secretly
    providing and add THOSE to the conjunct's `by {}`; (3) only if it STILL fails
    after every dependency reveal is hoisted is the hand-proof real — then flag the
    trigger gap. Concluding "needed" at step (1)'s failure is the trap.
- **When you stub a proof, delete the scaffolding that only fed it (high value):**
  a hand-off `assume(self.inv())` (or any `//@Xiangdong` stub standing in for an
  unfinished conjunct) makes ALL the machinery that was building toward it dead
  weight — the `let ghost pre_mut = *self;` / `post_pop` / `pre_stage_proc`
  snapshots, the per-field `assert(self.X == pre_mut.X)` frame blocks, the
  `_fold_change_one`/`lemma_view_len` re-derivations, the nested `assert(self.
  memory_management_inv()) by {...}` rebuild. Once the conjunct is an `assume`,
  none of that is load-bearing; leaving it around a stub reads as "finished proof"
  when it isn't, and buries the few live obligations. STRIP IT: collapse the whole
  rebuild to the single `assume`, and delete every ghost snapshot + frame assert
  that has no consumer left. Keep ONLY what still feeds a LIVE (non-assumed)
  obligation — e.g. the exec-precondition proofs a real `wlock_*`/`wunlock_*` call
  still needs (page-slot acyclicity/freshness, the `container_allocator_free_4k_page_wf`
  reveal that pins the peeked page Free4k so the page lock id computes), and the
  ghost (`cache_lock_id`) those proofs read. Reflex: after stubbing, delete a ghost
  / frame assert and re-verify; if it still passes, it was scaffolding for the
  stub — leave it out. A stubbed fast path should be lean exec + the live
  lock-op precondition proofs + the `//@Xiangdong` stubs, nothing more.
- **Trim the scaffolding once it's green (high value — do this EVERY time you
  finish a proof, before calling it done):** the asserts you add while GRINDING a
  proof — the intermediate `assert(...)` steps, the extra `reveal(...)`s, the
  `let ghost` snapshots you introduced to see what the solver had — are almost all
  redundant once the real closing step lands. A proof found by accretion reads as
  10 lines when it's really 2. After the function verifies, do a deliberate trim
  pass: delete each assert/reveal/ghost you added (start from the ones farthest
  from the goal), re-verify, and KEEP it only if removal breaks verification. This
  is the mirror of the delete-and-reverify diagnostic above, run as cleanup rather
  than debugging. Concretely, in this session `pop_stage_4k_page`'s line-572 fix
  needed a `contains(page_ptr)` primer, a cpu-id-match assert, an allocator-ptr
  assert, and a payload-framing assert to GET there — but several of those became
  dead once the target assert had its own `by { reveal(container_allocator_free_4k_page_wf); }`
  and the `node_addr == storage.addr()` substitution was in scope; the finished
  proof should carry only the asserts that still fail-on-delete. Watch especially
  for: (a) two asserts proving the SAME fact by different routes (keep the cheaper
  one), (b) a `reveal(...)` that a later `by { reveal(...) }` now subsumes, (c) a
  `let ghost` bound but read only by an assert you're deleting, (d) an assert that
  only PRIMED a solver state that a subsequent `by {}` block now establishes on its
  own. A wrapper whose body still carries its grind-time scaffolding after it's
  green is an unfinished proof, not a finished one — trim before `/style-check`.
  **Ghost snapshots are the #1 offender — audit EVERY `let ghost`:** the
  `let ghost old_self = *self;` / `old_caches` / `old_ll` / `pre_mut` / `post_pop`
  / `storage_addr` bindings are what accretion leaves behind most — you snapshot
  the pre-state to compare, then close the proof another way and never read the
  snapshot. For each `let ghost`, find the live line that reads it (a surviving
  assert, a lemma-call arg, a framing conjunct); if none does, DELETE it and
  re-verify. A finished proof has ZERO ghost snapshots that aren't consumed by a
  live obligation — an orphaned `let ghost` reads as "this tracks the old state"
  when nothing does.
- **Comment discipline (high value — surface tell):** `requires` blocks are
  BARE — no `//` group notes, no `// ---- ----` banners; the clauses stand alone
  (`wlock_cpu`, `syscall_alloc_quota_4k`). `// ---- <title> ----` banners are
  SINGLE-LINE and belong ONLY to `ensures` framing and to the body's `inv()`
  re-establishment; never wrap a banner across lines. `proof {}` blocks carry NO
  prose — the error-path blocks and the top reveal block in `syscall_alloc_quota_4k`
  are bare calls. Doc comments (`///`) are absent on the ordinary wrappers
  (`wlock_cpu`, `wlock_quota_4k`); a wrapper gets one ONLY to explain the single
  non-obvious contract point (e.g. `wunlock_process`'s temp-alloc protocol) —
  never to recap what the body does step-by-step.
- **Bidirectional relations:** two separate forall conjuncts tagged
  `// forward` / `// reverse`, each `dom()`-guarded.
- **Cost control:** do NOT add `#[verifier::spinoff_prover]` on your own — it's
  Xiangdong's call, applied only when he directs it (many existing wrappers carry
  it because HE added it; that's not a license to add more). If a new
  wrapper/helper/lemma is slow enough that you think it wants spinoff, flag it and
  ask — don't sprinkle it. The rest of the cost pattern still holds: function-wide
  `proof { reveal(...); }` hoist at top; re-establish `inv()` conjunct-by-conjunct
  under `// ---- subsystem ----` banners ending in `assert(self.inv());`.
- **Scope reveals to the assert that owns them — every BARE `reveal(...)` deserves a
  second look (high value — reveal scope is real SMT cost).** A `reveal(P)` at
  `proof {}` / function scope opens `P`'s definition for the WHOLE rest of the
  function's SMT context, not just the obligation that needs it. For a DEEP-quantifier
  predicate (`*_locked_match_lctx`, the `*_wf` membership/fold invariants) that
  leaked-open body enlarges E-matching for every downstream assert — pollution that
  inflates rlimit and can destabilize UNRELATED sibling conjuncts. The confining move
  is to attach the reveal to the specific `assert(<goal>) by { reveal(P); }` that
  consumes it (Verus `reveal` is lexically function-wide, so a nested `proof {}` does
  NOT limit it — only an `assert ... by {}` does). Scoping the 9-reveal
  `*_locked_match_lctx` chain in `pop_stage_4k_page` into
  `assert(self.locked_objects_match_lctx(&*lctx)) by { <the 9 reveals> }` cut the
  module rlimit ~6%. This is the SAME lever as the nested-`inv()` rebuild below (each
  `by {}` is its own scoped sub-goal) — apply it to loose reveals too. EXCEPTIONS
  where a bare hoist is correct: (a) the predicate is consumed by SEVERAL sibling
  asserts in the block (scoping would duplicate the reveal N times — the function-wide
  hoist is then the cheaper idiom), or (b) delete-and-reverify shows the reveal is
  needed function-wide (e.g. by exec precondition checks between the reveal and a later
  re-reveal). Don't force-scope a reveal a delete-and-reverify proves is needed broadly;
  DO scope a deep-quantifier reveal that exactly one downstream assert owns.
- **inv() re-establishment is NESTED, not flat** (high value): wrap each
  subsystem's conjuncts INSIDE
  `assert(self.memory_management_inv()) by { <its conjuncts> };` and
  `assert(self.process_management_inv()) by { <its conjuncts> };`, so each
  subsystem `inv()` is its own scoped SMT sub-goal. The `// ---- subsystems_inv
  ----` direct conjuncts (cpu_array_wf, container_perms_wf, …) and the final
  `// ---- inv() direct conjuncts ----` (cpu_dirty_map_wf, tlb_wf_spec) stay at
  the outer level; only the two big combiners get `by {}` blocks. Measurably
  cheaper SMT than flat. Banner order: subsystems_inv → memory_management_inv →
  process_management_inv → inv() direct conjuncts → `assert(self.inv())`.
- **Framing:** list EVERY field `final(self).X == old(self).X` even when one
  moves; frame the touched one with `unchanged_except`; `// Other fields untouched.`
  `=~=` for collections, `==` for scalars/the single changed field.
- **Tracked:** `Tracked(lctx): Tracked<&mut LocalContext>`; `final(lctx)`/`old(lctx)`.
  Result primitives split ensures `ret.0 == false ==> {...}` / `true ==> {...}`,
  false branch frames all-unchanged.
- **Files:** one concept per file named after it; preamble
  `use vstd::prelude::*;` → `verus! {` → `use crate::*;`; split APIs by
  const-generic into separate `impl` blocks; repeat full generics/bounds.
- **Quirks (unmistakably his):** sentinel `233` for don't-care major/minor
  ids & list capacity; `true == false` (not `false`) for TCB `requires` gates;
  `== false` instead of `!`; full `.view().view()` chains, no intermediate `let`;
  signs TODOs `//@Xiangdong`; `// SPEC FIX:` / `// PERF:` tags; keeps abandoned
  code commented in-tree rather than deleting.
- **Spell out `.view()` — do NOT use the `@` sugar (tooling constraint):** write
  `x.view()` / `x.view().view()` (and `x.view()->Write_lock_id`,
  `foo.view().linked_list`), never `x@` / `x@@`. `@` desugars to `.view()`
  identically for the verifier, but the code analyzer doesn't resolve the `@`
  sugar well, so NEW code spells it out. This is go-forward: much of HIS existing
  code (e.g. `wlock_cpu`) is dense with `@`, so you'll still READ `@` everywhere —
  don't churn his live code to convert it, and mirror the `.view()` chain shape,
  not the `@`, when you copy a sibling. `//@Xiangdong` TODO signatures are text,
  not the view operator — leave them as-is.
- **Spec safety:** derived quantities return `int` (no underflow); `recommends`
  (not `requires`) on pure accessors as inline doc; opacity-bridge via empty
  `lemma_view_len`-style proof fn, never open a closed spec.

## The lock-wrapper-per-object pattern (dominant shape in `kernel/implementation/locker_unlocker.rs`)

- One `KernelK` method per (object, lock-op): `wlock_cpu`/`wunlock_cpu`,
  `wlock_container_unless_killed`/`wunlock_container`,
  `wlock_quota_4k`/`wunlock_quota_4k`, `wlock_process_unless_killed`/`wunlock_process`.
  Each forwards to the layer primitive then re-establishes `inv()` with the
  nested template above.
- **Three-rung forwarding chain** for allocator pieces: `RwLock::w(un)lock` ←
  `PageAllocator::w(un)lock_quota` (`allocator/page_allocator.rs`) ←
  `UnLockedMap::w(un)lock_quota` (`locks/unlocked_map.rs`) ← `KernelK` wrapper.
  Many of these primitives sit COMMENTED in `/* */` blocks; lift just the rung
  you need (close the live impl after it, re-open `/* */` for the rest) — don't
  un-comment whole blocks (later methods depend on still-disabled lemmas).
- **`_unless_killed` wrappers** return `(bool, Option<Tracked<LockPerm>>)` with
  the success/failure `ret.0 == true/false ==> {...}` split; plain `wunlock_*`
  are unconditional (no Option), consume the `LockPerm` by value, return nothing.
- **wlock vs wunlock spec delta:** wlock ensures `lock_ensures`+`wlock_ensures`
  and `kernel_view_locking_state() == old`; wunlock ensures
  `unlock_ensures`+`wunlock_ensures`, asserts `locking_thread() is None`, and
  **must NOT** state `kernel_view_locking_state() == old` — `unlock_ensures`
  flips it Acquire→Release, so `== old` is unsatisfiable in an Acquire section
  (keep a verbatim NOTE explaining this, cross-ref the `LockedArray::wunlock`
  NOTE). Only `thread_id()` + `user_view_locking_state()` are framed on wunlock.

## Fold-conjunct discipline (`container_process_allocator_quota_{4k,2m,1g}_wf`)

- This is the one `inv()` conjunct that doesn't fall out of byte-equality. It's a
  `Set::fold` over `owned_processes`/`owned_threads` summing per-process/thread
  quotas == allocator `total_free_pages`. A lock op preserves each summand's
  `view()`, but Verus won't congruence-close two folds whose closure captures a
  (byte-)different map — bridge with the narrow TCB axioms in
  `lemma::lemma_t::kernel_fold_axioms` (enabled in `lemma_t/mod.rs`):
  `lemma_process_effective_quota_{4k,2m,1g}_fold_eq`,
  `lemma_thread_direct_pending_*_fold_eq`,
  `lemma_thread_indirect_pending_*_fold_eq_at_depth`. "No change in quota ⟹ no
  change in folded sum." These are his template (concrete params, lambda inlined
  verbatim); soundness = induct on the set.
- When the TOUCHED map is the one being folded over (e.g. `wlock_process`),
  feed the lemma's per-element hypothesis explicitly: `assert forall|p|
  owned.contains(p) ==> process_effective_quota_*(self[p]) == ...(old[p])`,
  proving owned ⊆ dom via `reveal(container_process_wf)` (its
  `owned_processes.subset_of(process_map.dom())` conjunct) then firing the
  hoisted per-element `view()`-equality frame. When the touched map is NOT
  folded (e.g. `wlock_quota`/`wlock_cpu`/`wlock_container`), the fold args are
  byte-equal so it closes by Leibniz / a single `reveal`.
- The fold conjunct's old-state equation must be brought into scope explicitly:
  `assert(<the same fold equation over old(self)...>) by { reveal(container_process_allocator_quota_4k_wf); };`.
- **`_fold_change_by` axioms (delta form):** when exactly one process's quota
  moves by `x` (an alloc/free, not a lock op), the fold shifts by `x`. Mirror
  `lemma_process_effective_quota_4k_fold_eq` but add `mod_p` + `x` params, the
  per-`mod_p` hypothesis `...(post[mod_p]) == ...(pre[mod_p]) + x`, and ensures
  `<fold post> == <fold pre> + x`. All three sizes; same `external_body` TCB
  family (soundness = induct on the set, one element contributes `+x`). Lives
  beside the `_fold_eq` axioms in `lemma_t::kernel_fold_axioms`.
- **Preservation lemma over the whole conservation conjunct
  (`container_process_allocator_quota_4k_wf_preserved_on_alloc`):** extracts the
  inline fold block into a `pub proof fn` taking
  `pre: &KernelK, post: &KernelK` (NOT loose maps — its source-wf requires are
  then literal entry-`inv()` clauses a caller with `old(self).inv()` discharges
  directly). Requires: source conjunct + `container_process_wf` +
  `container_allocator_wf` (state the OPAQUE clause itself, reveal it in the body
  — don't hand-copy a partial forall the caller can't match); the container map
  is write-locked so require per-entry `view()`/`view_rodata()` equality + same
  dom (NOT whole-map byte-equality — that's unsatisfiable after a wlock), while
  the untouched-size `thread_map`/`allocator` are byte-equal. Body: per-container
  `assert forall`, bridge goal (`post.container_map`) back to `pre` via the
  view-equality, fire `_fold_change_by` on the touched container and `_fold_eq`
  elsewhere, deriving allocator-uniqueness from `reveal(container_allocator_wf)`.
  Lives in the syscall file (it's syscall-specific), NOT the spec file.

## Factoring a syscall's commit phase into a helper (`commit_alloc_quota_4k`)

- When a syscall's happy path (mutate → re-establish `inv()` → unlock all → close
  the user-step) is lifted into a `KernelK` method, the helper's ENTRY is the
  already-locked mid-syscall state. Precondition = the proof context at that
  point, stated MINIMALLY: `inv()`, both phases `Acquire` + fresh `snap_shot`
  (for `begin_user_view_step`), and per held object the four-line lock bundle
  (`wlocked_by(old(lctx))` + `!being_killed` + perm `state/thread_id/lock_id` +
  `lock_map` dom-contains + `lock_map[key] == perm.lock_id()`), plus only the
  structural anchors the fold re-establishment reads and the range/`temp_alloc_clean`
  facts the mutations/unlocks need. Move BOTH the `begin_user_view_step` and its
  `kernel_no_change_*` bridge inside — the helper's `old(self)` IS the post-lock
  state, so its captured `old_u` is the projection directly (no bridge needed
  inside; the CALLER keeps one `kernel_no_change_*` call before the helper to
  discharge the `snap_shot` precondition).
- **Do NOT ensure `all_objects_unlocked` from the helper.** Proving it there
  needs `locked_objects_match_lctx` transported across `begin_user_view_step`
  AND the four unlocks — Verus fights the quantifier instantiation (a congruence
  lemma over equal `lock_map`/`thread_id` won't auto-close). Instead ensure the
  lock-STATE FRAMING (each touched entry `locking_thread() is None`, every other
  field byte-equal, the 4k entry's `cpu_caches`/`global_pool` framed, `lock_map`
  `.remove()`d of the four keys) and let the CALLER re-derive
  `all_objects_unlocked` from its own entry `all_objects_unlocked` fact — which
  is still in scope there — with just the `reveal(*_objects_unlocked)` set. This
  is how the monolithic syscall got it for free (entry-all-unlocked carried
  through the wlock→wunlock round-trip).
- Body reads `old(self)` only through lock-state-invariant quantities
  (`process_effective_quota_*`, tree-field subset equalities), so it transplants
  verbatim with a `let ghost pre_self = *self;` standing in for the syscall's
  `old(self)` in the fold lemmas / `kernel_process_quota_4k_changed_imply_*`.
- Inside a helper taking `Tracked(lctx): Tracked<&mut LocalContext>`: pass the
  shared borrow as `Tracked(&*lctx)` to `borrow_mut`, the owned perm as
  `Tracked(perm.borrow())`, and reborrow `&mut *lctx` to `begin/end_user_view_step`
  and the `wunlock_*` calls. `all_objects_unlocked(final(lctx))` in an ensures
  needs `final(lctx)` (it's `&mut`).

## Hoisted per-entry/per-element frame (go-to for "lock op touched one map")

Right after the primitive call, an `assert forall|k| dom.contains(k) implies
<the fields the fold/free-ptr conjuncts read> == old`, with `if k != touched_key
{ assert(self[k] == old[k]); }` (unchanged_except for others; the touched
entry's preserved fields come from `w(un)lock_ensures`). Then downstream
conjuncts fire off this named frame.

## Other concrete rules

- **Map-level lock-id:** use `map.lock_id_by_key(key)` / `array.lock_id_by_index(i)`
  in wrapper specs — NOT a hand-built `LockId{container, process, major, minor}`
  (stale commented code has the hand-built form; it doesn't typecheck on `PointsTo`).
- **Process temp-alloc protocol:** `wunlock_process` requires `temp_alloc_clean`
  (once unlocked, `process_temp_alloc_empty_unless_wlocked` demands the cache be
  empty — the write-lock is the only thing licensing a non-empty cache).
  `wlock_process_unless_killed`'s success path PROVES `temp_alloc_clean` (fresh
  lock ⟹ was unlocked ⟹ clean), so non-staging callers get it free.
- **Spec files hold ONLY specs.** `*_spec.rs` files (e.g.
  `container_allocator_process_thread_spec.rs`) get `spec fn`s only; a `proof fn`
  belongs in the relevant impl file (the syscall file, a `lemma_*` file). If you
  drafted a lemma in a spec file, move it out — leave the spec file at "0 verified".
- **Framing lemmas (`*_no_change_to_*_fields_imply_*` / `*_preserved_for_*`):** the
  re-establishment shortcut. `container_no_change_to_tree_fields_imply_wf`,
  `process_no_change_to_tree_fields_imply_wf`,
  `lemma_process_staged_pages_wf_preserved_for_view_eq`,
  `kernel_no_change_to_user_view_fields_imply_kernel_u_eq`. Requires source-wf +
  same-dom + per-element `view()`/`view_rodata()` equality; ensures target-wf.
  When writing a NEW one, mirror `container_no_change_to_tree_fields_imply_wf`:
  empty-bodied or reveal-laden, additive (changes no existing spec).
  SCOPE THE HYPOTHESIS TO THE FIELDS THE TARGET-WF ACTUALLY READS, not the whole
  `view()`: `process_tree_wf` reads only `children`/`parent_linkedlist_node`/
  `uppertree_seq`/`subtree_set` off a `Process.view()` (which also carries
  `quota_*`/`temp_alloc_cache_*`/`pagetable`), so
  `process_no_change_to_tree_fields_imply_wf` requires equality of just those +
  `view_rodata()` — requiring full `view()` equality (as the `Container` twin
  does, since a container's view IS all tree state) needlessly shuts out callers
  that stage pages or move quota. Weakening a precondition this way is
  monotonic — existing callers still discharge it by congruence.
- **Verifying against the WIP crate:** `syscall_alloc_quota.rs` often has live
  calls to not-yet-written helpers (`release_cpu_and_finish`, etc.) that block
  crate compile. To function-verify, back up that file, neutralize the dangling
  call with `// TEMP-VERIFY-STUB` + `assume(false)`, verify, then restore
  BYTE-FOR-BYTE (`cp` back + `shasum` match). Never leave the stub.

## Honest rough edges in-tree (don't "fix" silently)

`syscall_alloc_quota.rs`
is WIP but `syscall_alloc_quota_4k` + its `commit_alloc_quota_4k` helper now
verify fully (no `assume(false)`); `finish_empty_user_step` / `release_cpu_and_finish`
remain COMMENTED-OUT templates — treat them as dead, not as style references
(the live sources of truth are `syscall_alloc_quota_4k` and the
`locker_unlocker.rs` wrappers); opacity applied inconsistently;
`pagetable_impl_base.rs` inlines re-establishment. Follow the proof-gap protocol
(in `veriflat-project-notes.md`) before touching specs.

## On rejected AI code & strict scoping

Files last touched in commits like "wip. fk AI" may be AI-authored and are
distrusted — but the commented-out lemma files (`lemma_u/kernel_preservation.rs`,
`lemma_t/kernel_fold_axioms.rs`) often hold exactly the narrow axiom needed, in
HIS template. When pointed at one, prefer enabling/reusing it (it's his idiom)
over rewriting from scratch; offer the rewrite if he'd rather not trust the
provenance. The strict rule: **only read files reachable through `mod.rs` from
`lib.rs`** — commented-out `pub mod` lines mean off-limits unless he directs you
there. He builds the working knowledge incrementally and asks for one
wrapper/lemma at a time; mirror the nearest LIVE sibling (source of truth), not
the stale commented template (which may have bugs like the hand-built `LockId`).
