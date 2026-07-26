---
name: project_contract_proof_simplification_2026_07_25
description: "Verified 2026-07-25 simplification of allocate_free_4k_page, syscall_new_thread, and their lock/helper contracts"
metadata:
  node_type: memory
  type: project
  originSessionId: current
---

## Result

The 2026-07-25 contract/proof pass changed three files:

- `allocate_free_4k_page.rs`
- `syscall_new_thread.rs`
- `locker_unlocker.rs`

Diff: 80 insertions, 401 deletions, net -321 lines. Final full verification:
479 verified, 0 errors. The baseline was 480 verified; the one-count decrease is
the intentionally deleted redundant allocator lemma. Target-file checks were
15/11/17 verified with 0 errors. `git diff --check` passed.

No new `assume`, `external_body`, or `spinoff_prover` was introduced. The
pre-existing three assumes in
`lemma_inv_imply_owned_threads_len_bounded` and the pre-existing external-body
scheduler queue bound remain unchanged.

## Allocator Lessons

### Effective quota does not belong in a global-total precondition chain

`allocate_free_4k_page` no longer requires
`total_free_pages.view() > 0`, and
`lemma_effective_quota_ge_1_imply_total_free_pages_pos` was deleted. The
operation needs the process's effective quota and its normal cache/pool search
logic; forcing callers to prove a global conservation consequence created a
large, unused proof chain.

Keep the narrower `lemma_scan_fail_pool_nonempty`: pool non-emptiness becomes
relevant only after all caches have actually been shown empty.

### Canonical lock facts replace expanded lock state

Allocator helpers now mostly carry:

- permission state/thread;
- lock-map membership and key-to-lock-id equality;
- `locked_objects_match_lctx`;
- operation-specific facts such as `being_killed == false`.

They no longer forward every allocator/process domain fact, `wf`,
`wlocked_by`, or internal locking-thread equality. Those are recovered locally
from `inv()` and `allocator_locked_match_lctx` /
`process_locked_match_lctx`.

For all-cache quantified contracts, keep only facts consumed by unlock/scan:
permission-map membership, permission state/thread, and lock-map lookup. This
removed repeated deep allocator quantifiers from callers and loop invariants.

### Exact map updates subsume their consequences

For page acquisition, an exact lock-map insert equality already determines:

- inserted page-key membership;
- inserted page-key value;
- preservation of every old key/value.

The separate membership/value clauses and preservation forall were redundant.
Likewise, the executable global-pool linked-list length check was sufficient;
the duplicate nested spec-view length precondition was not needed.

### Wrapper contracts should derive their own low-level facts

The 4k allocator lock/unlock wrappers retain `inv()`, canonical permission and
lock-map facts, and `locked_objects_match_lctx`. Their bodies reveal
`allocator_locked_match_lctx` when calling the low-level primitive. Requiring
callers to also supply allocator `wf`, object `wlocked_by`, and internal lock-id
equality only duplicated the same relation.

The allocator slow-path helper also dropped its unused `cpu_id`; a parameter
with no execution or proof consumer should not remain merely because an earlier
contract mentioned it.

## New-Thread Lessons

### Keep the semantic syscall postcondition, not duplicate deltas

`kernel_u_new_thread_changed(...)` already describes the successful
user-visible transition. Separate quota decrement and owned-thread length
postconditions were consequences and were deleted. The impossible generic
`Error` result was also removed from the syscall result disjunction.

### Derive structural facts inside creation helpers

`create_thread_from_staged_page` now derives these from `inv()` in its own proof:

- ancestor sequence membership and no-duplicates;
- destination container exclusion;
- process owned-thread and scheduler queue length bounds;
- absence of the page key from `thread_map`;
- freshness of `KernelObjId::Thread(page_ptr)`.

Previously every caller had to establish and pass this expanded bundle.
`retype_staged_page_to_thread` similarly requires `old(self).inv()` and locally
reveals container/process/thread/page invariant components instead of requiring
all `perms_wf`, page initialization, depth equality, and physical-permission
consequences separately.

### Frame predicates and recursive signatures can be smaller

`unchanged_except` already includes map-domain preservation, so duplicate
domain-equality ensures were removed. `add_thread_to_ancestor_sets` did not use
the destination container; removing that parameter made the recursive proof
state match the property it actually establishes.

Release helpers need only facts consumed by their unlock calls and the final
user-view boundary. CPU/scheduler/process domain, `inv`, `wlocked_by`, and
internal lock-id facts derivable from the retained global invariant/match
relations should not be repeated in every helper contract.

## Boundary Between Redundant and Load-Bearing

Facts retained after delete-and-verify include:

- process/cache/pool `being_killed == false` where the primitive requires it;
- exact permission state/thread and lock-map lookup;
- lock-order assertions;
- process membership reveals immediately before a boundary;
- scheduler/process/CPU lock-map value assertions needed before ordered unlocks;
- exact staged-page, page-state, quota, and `KernelSteps` behavior;
- `kernel_u_new_thread_changed` as the public success specification.

Do not reintroduce a deleted consequence bundle when a new consumer appears.
First derive the one needed fact from the retained summary predicate at that
consumer. Strengthen a helper contract only when the fact genuinely cannot be
derived locally.
