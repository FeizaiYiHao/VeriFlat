# VeriFlat — current work state

Fast-moving state: what's verified right now, what's in progress, and the
spec-bug log. The durable architecture/conventions live in
`veriflat-project-notes.md`; the verification playbook in
`verus-verification.md`. Update this file as work lands; keep the other two
stable.

## Recent state

- **419 verified, 0 errors.**
- `syscall_alloc_quota_4k` fully implemented, all 5 exit paths verified, full
  pre/post including success-path delta. (See the REFERENCE EXAMPLE section in
  `veriflat-project-notes.md` for how it's structured.)
- Wrapper-per-lock-op pattern in active use (8 + allocator wrappers).
- 4 narrow trusted set-fold axioms in `spec_util.rs`; verified preservation
  lemmas + several helper lemmas.
- `KernelSteps.snap_shot` field; `kernel_step_boundary` enforces the snapshot
  discipline.
- `release_container_cpu_and_finish` exists but is currently unused (drop-in
  for a future flow).
- `PageAllocator.differential` (ghost per-cpu snapshot) was REMOVED.
  `total_free_pages_wf` folds directly over live `cpu_caches` lengths;
  `differential_wf` is gone. `wlock_cache`/`wunlock_cache` re-establish `wf()`
  via `lemma_cache_len_fold_congruence`. Roughly halved SMT on every
  allocator-touching wrapper (`wlock_quota_4k` 152→49 ms, `wunlock_container`
  307→121 ms). Consequence: the conservation total reads per-cpu-lock-protected
  state, so a cache pop in `allocate_free_4k_page` must decrement ghost
  `total_free_pages` under the same cache lock to preserve `inv()`.

## allocate_free_4k_page — IN PROGRESS

`src/kernel/implementation/allocate_free_4k_page.rs`. Fast path (pop from the
running cpu's cache) is structurally complete and verifies end-to-end behind
staged `assume`s; `finish_allocate_4k_page` holds the page-state transition.

Exec sequence of the finish helper (all real calls, verified to compile/return
the right `page_ptr`): borrow_mut_cache → `pop_head` (returns
`(node_addr, node_perm)`; **page ptr = `node_perm@.value()@`, NOT `node_addr`**)
→ `page_array.wlock(FREE_PAGE_LOCK_MAJOR)` → take → `state = Owned4k` +
`free_list_node_storage.put(node_perm)` (restores `node_storage_inv`) → put →
`process_map.borrow_mut` + `temp_alloc_cache_4k.insert(page_ptr)` →
`allocator_4k_map.borrow_mut` + `total_free_pages -= 1` → page wunlock →
`wunlock_allocator_cache`.

DISCHARGED (no longer assumed):
- `page_ptr_valid` (from `allocator_free_page_ptrs_wf` on the popped value).
- page's prior `Free4k{PreCpuCache{cpu_id}}` state (corrected reverse-cache clause).
- the page-slot `wlock` block (`lock_id_acyclic` via None-as-MAX owner-id: the
  Free page's `None` container beats the held process's `Some` directly).
- `node_addr == storage.addr()` — via `LinkedList::lemma_value_addr_unique`
  (map injectivity) + the new map-dom conjunct + strengthened `pop_head`.
- process/page submap facts across the mutations; the page `wunlock` block.
- the **kernel_step_boundary tail**: after both unlocks (now correctly in
  Release) the boundary flips back to Acquire and refreshes the snapshot;
  Owned4k + staged + effective-quota−1 postconditions all proved from the
  held-process-preserved-across-boundary + `process_staged_pages_4k_wf` backward.

The in-Release `inv()` re-establishment is now DECOMPOSED and mostly proven:
- **subsystems_inv** — PROVEN (frame over unchanged maps + the touched
  allocator's `wf()`, see next).
- **touched allocator `wf()`** — PROVEN via new lemma
  `lemma_cache_len_fold_change_one` (lemma_t/seq_fold.rs): fold delta when one
  cache shrinks by 1, re-balancing `total_free_pages_wf` against the ghost
  `total_free_pages −1`. (A few per-element cache-length deltas relating the
  post-pop `cpu_caches` to entry are still `assume`d — they need the pop's
  length-−1 fact threaded down from the `borrow_mut_cache`/`pop_head` site.)
- **process_management_inv** — PROVEN. Tree fields are framed at the
  temp_alloc insert site (single-field `&mut` assignment ⟹ only
  `temp_alloc_cache_4k` of `process_ptr` changed); `per_container_process_tree_wf`
  lifted via `lemma_process_tree_wf_preserved_for_tree_fields_eq`.
- **the kernel_step_boundary tail** — PROVEN (Acquire restored, postconditions).

`memory_management_inv()` is now DECOMPOSED per-conjunct (18 conjuncts).
PROVEN via the page-array frame (only page_index changed Free4k→Owned4k; 2m/1g
allocator maps == entry) + `entry_self.memory_management_inv()`:
`container_page_owner_wf`, `hugepage_2m/1g_wf`, `page_pagetable_wf`,
`container_process_page_pagetable_wf`, `container_pages_wf`, `process_pages_wf`,
`pagetable_pages_wf`, `thread_pages_wf`, `endpoint_pages_wf`,
`process_pagetable_match`, `container_allocator_wf`,
`container_allocator_free_{2m,1g}_page_wf`. Also `process_staged_pages_4k_wf`
FORWARD direction for the new page (it's Owned4k + staged).

The touched-allocator `wf()` is now FULLY PROVEN, including the
`total_free_pages_wf` page-counting rebalance (cache len −1 = total −1) via
`lemma_cache_len_fold_change_one` + the durable post-pop cache facts
(`post_pop_cache_view = entry skip(1)`, `unchanged_except(entry, cpu_id)`,
global_poll unchanged, the popped cache's `inv()` captured at the pop site).

NEWLY PROVEN this round:
- **conservation law** `container_process_allocator_quota_wf` — via new lemma
  `lemma_container_process_allocator_quota_wf_preserved_for_alloc_stage`
  (spec_util.rs, sibling to `..._for_quota_transfer`): effective_quota_4k −1
  (temp_alloc insert) balanced by total_free_pages −1. THE page-counting
  soundness fact. (Two narrow inline assumes feed it: effective_quota_2m/1g
  unchanged, and process_ptr ∈ container_ptr.owned_processes.)
- **allocator_free_pages_wf** — wired via the durable post-pop subset fact
  (current cache view ⊆ entry's). (Narrow "unchanged cache/pool == entry"
  frame assumes remain.)

ALSO NEWLY PROVEN this round:
- `allocator_pages_wf` (framed: 4k allocator dom unchanged; the changed page
  is Owned4k, never As4KAllocator, and not in the allocator dom — entry's
  backward clause contradicts Free4k).
- `process_staged_pages_4k_wf` — BOTH directions fully proven (forward: new page
  staged + other Owned pages stay staged as temp cache only grows; backward:
  staged ⟹ Owned4k, case-split on the new page_ptr vs pre-existing).

THE LAST OBLIGATION — now isolated to ONE lemma body:
`lemma_container_allocator_free_4k_page_wf_preserved_for_alloc` (spec_util.rs).
The finish body CALLS it cleanly (no inline assume); the lemma's hypotheses
(page_index Free4k{PreCpuCache{cpu_id}}→Owned4k; cache[cpu_id] = pre.skip(1)
dropping the head page_ptr; everything else framed; the cache map loses only the
popped node's key) are all established at the call site. The lemma BODY has the
correct 4-clause structure (forward vacuous-at-page_index + framed; reverse
pool/cache via subset+frame) but is currently gated by a top-level `assume(false)`
with ~8 internal transfer `assume`s. Remaining work = discharge those:
  - skip(1) membership: pp ≠ head ⟹ pp ∈ pre.view() ⟹ pp ∈ post.view() (and vice
    versa for the reverse cache clause);
  - map-removal transfer: a surviving page's node key st ≠ storage0 ⟹ its
    map dom/value entry survives (needs the new map-removal precondition);
  - st ≠ storage0 for distinct Free pages (cache map injectivity, like
    lemma_value_addr_unique);
  - page_ptr2page_index(pp) ≠ page_index for pool/other-cache pages (page_index
    was the popped PreCpuCache head, not in the pool nor in post caches).
This is the single remaining `assume` gating the fast-path allocate `inv()`.

Narrow frame assumes inside now-wired conjuncts (all mechanically true):
unchanged caches/pools == entry (allocator_free_pages_wf); effective_quota_2m/1g
unchanged + owned_processes membership (conservation law); `total_free_pages@>=1`
(fold-≥-element). Plus the cache-unlock lock bookkeeping + in-Release inv +
snapshot, the parked `locked_objects_match_lctx`, and the slow path (259/289).

New lemma: `lemma_container_process_allocator_quota_wf_preserved_for_alloc_stage`
(spec_util.rs) — the conservation law across staging one page.

New lemma: `lemma_cache_len_fold_change_one` (lemma_t/seq_fold.rs) — sibling to
`lemma_cache_len_fold_congruence`, for the one-cache-shrank fold delta.

KEY PROOF PATTERN for this `inv()` re-establishment: assert
`entry_self.{subsystems,memory_management,process_management}_inv()` once, then
each conjunct that reads only FRAMED state (unchanged maps, or page states the
transition doesn't touch) discharges with just its `reveal(...)`. Only the
~5 conjuncts that genuinely read the Free4k→Owned4k page / the shrunk cache /
the conservation sum need real per-invariant arguments.

Design note (RESOLVED by the High owner-id): a Free page has owner-id
`None` (the MAX — locked last); an Owned page is intended to carry `High` (the
MIN — never lockable while a `Some`-owner is held, so effectively private). The
finish proof relies on this only indirectly: the Owned page's state is shown
stable across `kernel_step_boundary` via the *held process* (whose
`temp_alloc_cache_4k` pins it through `process_staged_pages_4k_wf`), not via the
page lock. Making `Page::container_depth`/`process_depth` state-dependent
(None when Free, High when Owned) is a future change, needed only when something
tries to *lock* an already-Owned page.

## Spec-bug history → .kiro/HISTORY.md

The three `container_allocator_free_*_page_wf` spec bugs found while wiring those
predicates into `inv()` (vacuous antecedent, key/value swap, unconstrained cpu
binder) are recorded in `.kiro/HISTORY.md` (not auto-loaded). The durable result
— the preservation lemmas and where they're called — is in
`veriflat-project-notes.md` § "Trusted set-fold axioms". Consult HISTORY only for
the *why* behind a clause.
