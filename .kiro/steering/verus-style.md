# VeriFlat — Verus code-style signature

How to write VeriFlat Verus code that looks like Xiangdong wrote it. This is
the SURFACE-STYLE delta over `verus-verification.md` (which covers the cost
playbook & TCB-axiom design); this covers layout, naming, idiom, and the
concrete proof-structure patterns that recur across the lock wrappers.

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
  every quantifier; re-issue `reveal()` inside every nested `by` block.
- **Bidirectional relations:** two separate forall conjuncts tagged
  `// forward` / `// reverse`, each `dom()`-guarded.
- **Cost control:** `#[verifier::spinoff_prover]` on every wrapper/helper;
  function-wide `proof { reveal(...); }` hoist at top; re-establish `inv()`
  conjunct-by-conjunct under `// ---- subsystem ----` banners ending in
  `assert(self.inv());`.
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
- **Framing lemmas (`*_no_change_to_*_fields_imply_*` / `*_preserved_for_*`):** the
  re-establishment shortcut. `container_no_change_to_tree_fields_imply_wf`,
  `process_no_change_to_tree_fields_imply_wf`,
  `lemma_process_staged_pages_wf_preserved_for_view_eq`,
  `kernel_no_change_to_user_view_fields_imply_kernel_u_eq`. Requires source-wf +
  same-dom + per-element `view()`/`view_rodata()` equality; ensures target-wf.
  When writing a NEW one, mirror `container_no_change_to_tree_fields_imply_wf`:
  empty-bodied or reveal-laden, additive (changes no existing spec).
- **Verifying against the WIP crate:** `syscall_alloc_quota.rs` often has live
  calls to not-yet-written helpers (`release_cpu_and_finish`, etc.) that block
  crate compile. To function-verify, back up that file, neutralize the dangling
  call with `// TEMP-VERIFY-STUB` + `assume(false)`, verify, then restore
  BYTE-FOR-BYTE (`cp` back + `shasum` match). Never leave the stub.

## Honest rough edges in-tree (don't "fix" silently)

Load-bearing typos in public ids (`childern`, `processs`, `additonal`/`addtional`,
`vaild`, `global_poll`, file `pagetabel_map_spec.rs`); `syscall_alloc_quota.rs`
is WIP — much is commented, the main `syscall_alloc_quota_4k` body ends in
`assume(false)`, and the live body often calls not-yet-written helpers (see the
WIP-crate verify note above); opacity applied inconsistently;
`pagetable_impl_base.rs` inlines re-establishment (no spinoff_prover),
contradicting the playbook. Follow the proof-gap protocol (in
`veriflat-project-notes.md`) before touching specs.

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
