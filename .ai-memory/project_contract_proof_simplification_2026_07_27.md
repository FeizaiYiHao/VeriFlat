---
name: project_contract_proof_simplification_2026_07_27
description: "Verified follow-up simplification after the LockToken/dynamic LockId split"
metadata:
  node_type: memory
  type: project
  originSessionId: current
---

# Contract simplification after dynamic lock-id refresh

## Result

The follow-up preserved the semantic LockToken/LockId fix while removing the
contract and proof bundles reintroduced around it. Relative to the 2026-07-26
baseline, the five-file diff is 187 insertions and 323 deletions, net -136
lines. Full verification is `484 verified, 0 errors`; no `assume`,
`external_body`, `spinoff_prover`, invariant trigger, or rlimit change was
added.

## Reusable proof techniques

### Keep capability identity separate from ordering state

`LockPerm.lock_id()` is a stable capability token. `LocalContext.lock_map`
stores the current deadlock-ordering `LockId`. A payload transition can change
the latter without changing the former. Contracts therefore carry two
independent witnesses:

- permission state/thread/token against `locking_thread`;
- lock-map membership/value against the object's current dynamic `LockId`.

Never recover the old unsound equality between the permission token and the
dynamic ordering id just to make a proof shorter.

### Compose exact maps from the right historical snapshot

For acquire-stage-release-refresh sequences, snapshot the local context before
the transient locks are acquired. Then compose exact insert/remove/update
postconditions into `final_map == base_map.insert(page, current_page_id)`.
Snapshotting after cache/pool acquisition makes that equality false because the
base still contains keys intentionally removed later.

When a multi-lock helper cannot prove exact composition, strengthen its real
frame with a reverse-domain/new-key classification. Do not add a page-specific
historical preservation `forall`.

### Instantiate boundary preservation at one held object

Boundary predicates are necessarily quantified, but callers normally need one
known held page. A ground helper such as
`held_page_aligned_after_boundary` should instantiate the quantified frame once
and return the slot equality, dynamic-id alignment, and lock ownership needed
by the next operation. This keeps quantified facts out of public contracts and
prevents four allocator branches from duplicating the same proof.

### Recover structure inside the consuming callee

`create_thread_from_staged_page_merged` now accepts canonical lock witnesses
instead of caller-proved domain, `wlocked_by`, ancestor-shape, length-bound,
thread-absence, and freshness consequences. At entry it reveals the relevant
parts of `inv()` and derives those facts where they are consumed.

For nested opaque invariants, reveal the provenance chain from the outside in.
For example, `uppertree_seq.no_duplicates()` requires revealing
`container_perms_wf` before `container_tree_fields_wf`; revealing only the
inner predicate does not expose the invariant's premise.

After adding the correct scoped reveals, delete explicit ground consequences
one family at a time. In this pass, object domain/`wlocked_by`, container
domain, ancestor no-duplicate/self-exclusion, depth, `perms_wf`, page
`inv/is_init/perm.is_some`, thread absence, and freshness assertions all became
unnecessary at the merged creator entry.

### Preserve public compatibility deliberately

The live syscall calls the merged creator. The legacy public creator and its
retype helper only call each other and have no in-repo consumer. Their
accidental contract edit was reverted rather than silently deleting public
APIs or adding proof churn outside the live path.

## Verification discipline

Use `--verify-function` while deleting one consequence family, then verify the
whole target module and finally the crate. A module pass can miss consumers of
shared lock contracts; the full-crate pass is mandatory after changing
`lock_ensures`, `unlock_ensures`, or common wrapper contracts.
