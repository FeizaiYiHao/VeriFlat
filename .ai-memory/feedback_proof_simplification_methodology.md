---
name: feedback_proof_simplification_methodology
description: "Contract-entailment-first method for removing redundant Verus proof code and specifications without weakening behavior"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: current
---

## Core Rule

Proof simplification is a logical provenance audit, not an assert-counting
exercise. For each precondition, postcondition, quantified conjunct, ghost
snapshot, and proof block, identify the next consumer and the strongest fact
that already implies it. Delete consequences rather than repeatedly forwarding
them through every helper.

Do not call a proof "minimal" merely because obvious debugging asserts are gone.
The 2026-07-25 pass removed another 321 net lines from code that had already been
described as minimal, without changing invariant triggers or adding proof gaps.

## Simplification Order

### 1. Audit consumers and implication first

Start at call sites and externally consumed postconditions. Keep a fact only if
a caller or the function body consumes it and it is not already implied by a
stronger retained predicate.

Common stronger sources in VeriFlat:

| Redundant fact | Stronger retained source |
|---|---|
| map domain/wf/init facts | `inv()` plus the relevant scoped `reveal(...)` |
| object `wlocked_by` and lock-id equality | `locked_objects_match_lctx`, the `LockPerm`, and the `lctx.lock_map()` entry |
| map-domain equality | `unchanged_except(...)` |
| inserted-key membership/value and old-key preservation | exact `map == old(map).insert(key, value)` |
| individual user-visible field deltas | a semantic change predicate such as `kernel_u_new_thread_changed` |
| tree shape, no-duplicates, freshness, and length bounds | `inv()` components, revealed where the operation needs them |

Do not retain both a summary relation and all of its consequences. A semantic
postcondition should be the public contract; field-by-field consequences can be
derived by consumers that actually need them.

### 2. Move derived facts to the callee that consumes them

If a helper can derive a fact from `old(self).inv()`, require `inv()` and reveal
the relevant component inside that helper immediately before use. Do not make
every caller prove and forward the expanded consequences.

This is especially effective for:

- container ancestor sequence membership/no-duplicates/depth facts;
- thread-key freshness derived from `thread_pages_wf` and
  `thread_locked_match_lctx`;
- queue/list overflow bounds derived by invariant lemmas;
- `perms_wf`, page initialization, and physical-permission presence.

This shrinks both the caller proof and the helper contract while keeping the
dependency explicit at the actual consumption point.

### 3. Use one canonical lock witness chain

For a held object, the preferred caller-facing facts are:

1. `LockPerm.state() is WriteLock`;
2. `LockPerm.thread_id() == lctx.thread_id()`;
3. the object's key is in `lctx.lock_map()`;
4. that key maps to `LockPerm.lock_id()`;
5. `locked_objects_match_lctx(lctx)`.

Together with `inv()`, these usually imply object-domain membership,
`wlocked_by`, and equality with the object's internal write-lock id. Reveal only
the relevant `*_locked_match_lctx` predicate in the callee when the low-level
lock primitive needs those consequences.

For quantified permission maps, quantify only the permission and lock-map facts
the next wrapper consumes. Avoid carrying object-side `wf`, `wlocked_by`,
`being_killed`, and internal lock-id equalities when the wrapper can recover
them from the canonical chain.

### 4. Prefer exact frame relations over consequence bundles

Exact equalities and frame predicates are compact proof interfaces:

- `final(map) == old(map).insert(...)`;
- `unchanged_except(...)`;
- `lock_ensures(...)` / `unlock_ensures(...)`;
- `kernel_u_*_changed(...)`.

Once one is retained, remove duplicate domain equalities, membership facts,
lookup equalities, preservation foralls, and individual field deltas that it
implies.

### 5. Remove proof-only plumbing

Delete unused exec/ghost parameters, snapshots, and generalized return variants
that exist only to forward redundant facts. Examples validated in this repo:

- an unused `cpu_id` on the allocator slow-path helper;
- an unused destination-container parameter in ancestor-set recursion;
- a generic `Error` result that the syscall can no longer return;
- ghost lock-map snapshots used only by a removable bridge forall.

### 6. Diagnose triggers only after the logical audit

Bridging `assert forall ... by { reveal(...) }` can indicate a trigger problem,
but first check whether the bridge is logically unnecessary because a stronger
callee ensure or frame relation already supplies the result.

If a real quantified postcondition is not instantiating, prefer a post-state
trigger on the narrow exec/spec helper. Do not change triggers on opaque
invariants without Xiangdong's approval. See
`feedback_ask_before_invariant_triggers.md` and
`feedback_aggressive_trigger_eliminates_bridging.md`.

Pre-boundary scoped reveals remain load-bearing when they expose a ground
lock-map fact from an opaque match predicate. Do not confuse those with
post-call bridge foralls.

### 7. Delete by fact family and verify immediately

Use a narrow delete-and-verify loop:

1. Remove one logical family, such as duplicate lock facts or one consequence
   bundle.
2. Verify the touched function/module.
3. If it fails, identify the exact downstream precondition instead of restoring
   the whole bundle.
4. Run the full verifier after the local passes.

A lower verified count is not automatically a regression: deleting a standalone
lemma legitimately removes one verification item. Compare errors and behavior,
not only the count.

## Usually Load-Bearing

- lock-order arithmetic (`spec_gt`, major/id comparisons) required by a wlock;
- `being_killed() == false` when an unlock/mutation primitive explicitly needs it;
- phase, snapshot, and `KernelSteps` facts at user/kernel boundaries;
- exact page/process state changes that define allocator behavior;
- scoped reveals that expose an opaque predicate's ground membership fact;
- the final user-visible semantic change predicate.

## Proof-Gap Discipline

Never turn simplification failures into `assume`, `external_body`,
`spinoff_prover`, trigger changes on invariants, or rlimit increases. A timeout
can hide an unprovable contract. First locate the missing fact or over-specified
contract, then either prove it, weaken the redundant requirement, or report the
gap.
