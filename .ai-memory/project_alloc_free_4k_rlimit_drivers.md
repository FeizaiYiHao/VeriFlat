---
name: project_alloc_free_4k_rlimit_drivers
description: What drives SMT rlimit in allocate_free_4k_page.rs (profiler findings) and why ground-fact lemma scoping barely helps
metadata: 
  node_type: memory
  type: project
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

Profiled `kernel::implementation::allocate_free_4k_page` (via
`./verify.sh --verify-only-module ... --verify-function allocate_free_4k_page --profile-all`).
Module total smt-run ≈ 24.4M rlimit; per-function split:
`allocate_free_4k_page` **13.27M** (dominant — 54%, 2.9× the next),
`pop_stage_4k_page` 4.54M, `pop_stage_global_4k_page` 4.45M,
`wlock_all_caches_and_global_pool` 1.11M, `wunlock_all_caches` 0.53M,
`scan_caches_and_alloc` 0.28M.

**Top instantiation drivers in the main fn** (Cost×Instantiations, 44,577 total
user-quant instantiations): (1) `vstd/set.rs:655` Set axiom — 30% of ALL
instantiations (13,628); (2) `page_allocator.rs:46` `cpu_id_valid(cpu_i) ==>
cpu_caches[cpu_i].inv()` — highest per-inst cost 193,629; (3) `vstd/set.rs:702`
Set axiom — 17%; (4) `kernel_k_define_spec.rs:565` AllocatorCache lock-map-match
deep quantifier; (5) `allocator_spec.rs:11` `alloc_map[a_ptr].inv()` membership.

**Takeaway:** the cost is dominated by DEEP quantifiers (allocator/cpu-cache
`inv()` membership, lock-map-match) and `Set::fold` axioms — NOT by the ground-
equality lemma calls. So scoping a bare `lemma(...)` whose ensures is a GROUND
fact (e.g. [[project_lemma_scoping_ground_vs_forall]]) barely moves rlimit; the
real levers are the deep-quantifier `reveal`s and the fold axioms. See
[[feedback_lemma_scoping]].

**Ablation localized it further (via /profile-proof):** the 10 repeated
`assert(self.locked_objects_match_lctx(&*lctx)) by { reveal ×9 }` blocks in the
main fn were **83% / ~11M rlimit**. `locked_objects_match_lctx` is a self↔lctx
relation (11 deep bidirectional foralls), NOT part of `inv()`, so the wrappers
never carried it and every caller rebuilt it from scratch after each wrap.

**FIX SHIPPED (2026-07-16, option 2): folded `locked_objects_match_lctx` into the
6 4k-path wrapper contracts** in [[project_match_lctx_wrapper_contract]] —
`allocate_free_4k_page` dropped **13.27M → 2.25M (−83%)**; net ~−9.6M across both
modules (wrappers absorbed ~+1.4M). Full crate 458 verified, 0 errors.

**FIX SHIPPED (2026-07-20, redundant-nested-forall): the Case-2 pool path in the
main fn wrapped its acyclicity proof as `assert(forall|k| ...major <= GLOBAL_POLL)
by { reveal×2; assert forall|k| ...major <= GLOBAL_POLL by {...} }` — the OUTER
`assert(forall)` and the INNER `assert forall` proved the IDENTICAL fact. The
outer wrapper was pure E-matching pollution over the whole nested acyclicity
sub-proof. Collapsing to just the inner `assert forall` (delete the outer
`assert(forall ...) by {` wrapper + its closing `};`, hoist the two reveals):
`allocate_free_4k_page` smt-run **272.7M → 133.2M rlimit (−51%)**, 32s → 11s;
module 283M → 143M. Full crate 473 verified, 0 errors. LESSON: an
`assert(forall|k| P(k)) by { assert forall|k| P(k) by {...} }` (outer conclusion
== inner conclusion) is never proof content — the inner establishes P in context,
the outer just re-quantifies it and pollutes. Grep for this shape.
NOTE: the `#[verifier::rlimit(80000000)]` is a PER-QUERY ceiling; the 133M is the
SUM across queries, so it stays green — leave the attribute (Xiangdong's call to
lower).

**Trimmed grind scaffolding in `create_thread_from_staged_page`
(syscall_new_thread.rs) same day:** deleted 6 dead `assert forall|..| .. by { if
k != touched { assert(== old) } }` crutches + 3 top-of-proof primer asserts + a
duplicate `uppertree_seq.len()==depth` assert; `6.06M → 4.49M (−26%)`. The
`process_thread_wf` forward-clause forall + its 2 inner `old(self)` asserts, the
`container_thread_scheduler_wf` `reveal(container_thread_wf)`, and the push-bridge
`seq_push_lemma` are the ONLY load-bearing ones (fail-on-delete). `wunlock_thread`
foralls all confirmed load-bearing (mirror wunlock_process) — 0 trim.
