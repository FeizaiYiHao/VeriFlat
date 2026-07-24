---
name: feedback-ask-before-invariant-triggers
description: Ask Xiangdong before changing any trigger in an invariant / shared opaque spec predicate
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

Do NOT change `#![trigger ...]` annotations on invariant or shared opaque spec
predicates (e.g. the `*_wf` conjuncts, `*_locked_match_lctx`, anything in
`kernel_k_define_spec.rs` / the `memory_management` spec files) without asking
Xiangdong first. These are important, high-blast-radius changes — a trigger edit
on an opaque predicate re-shapes SMT instantiation for the 400+ functions that
reveal it.

**Why:** In one session I added `#![trigger page_array[i]]` to
`page_locked_match_lctx` and `#![trigger alloc_map.spec_index(p)]` /
`...cpu_caches.spec_index(c)]` to `allocator_locked_match_lctx` to retire framing
lemmas. It verified crate-wide (418/0), but Xiangdong flagged that changing
invariant triggers is his call to make, not something to do unprompted.

**How to apply:** Proof-side changes are fine to make freely — deleting scaffolding
asserts, adding `#![trigger]` on a LOCAL `assert forall` inside a proof body,
`reveal`s, lemma calls. The line is the SPEC definition: if the edit lands inside a
`pub open spec fn` / `#[verifier::opaque]` predicate's quantifier, STOP and ask,
presenting (a) the exact trigger delta, (b) what it enables (e.g. lets N lemmas be
deleted), (c) that the full crate still verifies. Let him decide. See
[[feedback-proof-gaps]] — same "flag before acting" reflex, applied to triggers.
