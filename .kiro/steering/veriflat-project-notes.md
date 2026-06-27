# VeriFlat — operational notes

Concrete things to remember when working on this codebase. Read
`Methodology.md` and `README.md` for the conceptual model.

## Project shape

- Microkernel verified with Verus, in `src/`.
- `verus/` is a submodule; the verifier binary lives at
  `verus/source/target-verus/release/verus`.
- Run `./verify.sh` from project root to verify everything (works in
  both bash and zsh).
- `./activate` sources the Verus build environment.

**Current verified count lives in `current-work.md` § Recent state** (single
source of truth — don't restate it here, it drifts). Don't introduce regressions.

## Proof gap protocol

When you discover a proof gap or spec gap (e.g., a missing postcondition,
a lock ordering incompatibility, a `closed spec` blocking a proof, or a
Verus/SMT limitation), **stop and flag it to the user** before adding any
`#[verifier::external_body]` axiom or `assume(...)` workaround. Explain:
1. What property can't be proved.
2. Whether it's a spec gap (fixable by strengthening specs) or a Verus
   limitation (e.g., `closed spec` + opaque datatype field restrictions).
3. What the narrow TCB axiom would look like if the user chooses to accept it.

## Module layout

- `src/lib.rs` — crate root; re-exports everything.
- `src/locks/` — trusted base. `RwLock`, `LocalContext`, `LockedMap`,
  `LockedArray`, `PointsTo` glue. Mostly `external_body`.
- `src/define/` — types, constants, traits.
- `src/page/`, `src/proc/`, `src/cpu/`, `src/allocator/` — kernel object
  definitions (`Page`, `Container`, `Process`, `Thread`, `Endpoint`,
  `Scheduler`, `Cpu`, `PageAllocator`).
- `src/pagetable_seq/` — page table machinery.
- `src/kernel/` — global kernel state and invariants.
  - `kernel_k_define_spec.rs` — `KernelK` struct and the global `inv()`.
  - `kernel_u_define_spec.rs` — `KernelU` user-view projection.
  - `kernel_total_define_spec.rs` — `KernelStep`, `KernelSteps` ledger.
  - `spec_util.rs` — preservation lemmas, narrow trusted set-fold axioms.
  - `memory_management/`, `process_management/`, `cpu_tlb_management/` —
    spec files, one bidirectional relation per file.
  - `implementation/` — verified syscall implementations.
- `src/lemma/`, `src/util/`, `src/primitive/`, `src/linkedlist/` — proof
  helpers and data structures.

## RwLock — five generic params

```rust
RwLock<T, ROT, KGhostT, UGhostT, const HAS_KILL_STATE: bool>
```

- `T` — lock-protected payload. Always kernel-visible; user-visible iff
  `T::is_user_visible()`.
- `ROT` — read-only data. Same visibility as `T`. `borrow_rodata()` works
  without a lock.
- `KGhostT` — kernel-view-only ghost. Never user-visible.
  `update_kernel_ghost` mutates without a lock; kernel-view Release op.
- `UGhostT` — user-view-visible ghost. Same visibility as `T`.
  `update_user_ghost` mutates without a lock; kernel-view Release; if
  `T::is_user_visible()`, also requires user-view Release.
- `HAS_KILL_STATE` — `bool` const generic. Toggles whether the rwlock
  carries a `killer_info: Option<KillerInfo>` (kill-protocol marker).

Most concrete sites pass `(), (), ()` for ROT/KGhostT/UGhostT. Container,
process, thread, endpoint, scheduler, page-table all use
`HAS_KILL_STATE`. Page array, allocator's internal pieces use
`NO_KILL_STATE`.

## RwLock API split

- `RwLock<…, NO_KILL_STATE>` exposes `wlock` (no kill check).
- `RwLock<…, HAS_KILL_STATE>` exposes `wlock_unless_killed` and
  `try_wlock_and_mark_kill`. Both fail if `killer_info.is_some()`.
- `wlock_external` / `wunlock_external` exist for TCB construction code;
  gated by `requires false`. Use only inside the TCB.

## LocalContext

Tracked ghost type minted by the TCB at syscall entry, threaded through
every kernel call by ownership.

- `kernel_view_locking_state`: per atomic section (`Acquire → Release`).
  Acquire = locks may be taken. Release = no more acquires; releases
  only.
- `user_view_locking_state`: per user-step (`Acquire → Release`). Same
  shape. Flipped both directions by `begin/end_user_view_step`.
- `lock_seq: Seq<LockId>` — strictly ascending under `LockId::spec_gt`,
  enforcing global lock ordering for deadlock-freedom.
- `unlock_requires<T>(...)`: `T::is_user_visible() ==>
  user_view_locking_state is Release`. Wired into both `wunlock`
  variants. The user-view linearization point is mandatory before any
  user-visible lock can be released.

## KernelSteps + snap_shot discipline

`KernelSteps` is a tracked ledger threaded through a syscall, recording
user-visible atomic transitions:

```rust
pub tracked struct KernelSteps {
    pub ghost steps: Seq<KernelStep>,
    pub ghost snap_shot: KernelU,  // user-view at last refresh point
}
```

Each `KernelStep` has `old_u`, `old_k`, `new_u`, `new_k`. Steps are
opened by `begin_user_view_step` and closed by `end_user_view_step`.

The `snap_shot` field is the discipline mechanism that catches
unrecorded U-mutations:

- **Syscall entry** (precondition): `old(steps).snap_shot ==
  kernel_k_to_kernel_u(*old(self))`. Caller hands us a fresh snapshot.
- **`begin_user_view_step`**: snap_shot preserved.
- **`end_user_view_step`**: snap_shot refreshed to current projection
  (the user-step's mutations are now recorded in the ledger).
- **`kernel_step_boundary`**:
  - requires: `kernel_k_to_kernel_u(*self) == steps.snap_shot` (no
    unrecorded U-mutation).
  - ensures: snap_shot refreshed to post-interleaving projection.

If a syscall mutates U outside of a `begin/end_user_view_step` pair, the
snap_shot stays stale, and the next `kernel_step_boundary` will fail to
verify. This mechanically enforces "U-mutations only inside user-steps."

## Wrapper-per-lock-op convention (CRITICAL pattern for SMT cost)

The *why* and the general recipe live in `verus-verification.md` § "THE CORE
PLAYBOOK" → "Wrapper-per-lock-op pattern". This section records the
VeriFlat-specific live wrappers and the measured wins.

In one line: every lock primitive (`wlock_*`, `wunlock_*`,
`wlock_*_unless_killed`) gets a `#[verifier::spinoff_prover]` wrapper method on
`KernelK` that calls the primitive AND re-establishes `KernelK::inv()`, so the
consumer body is just a sequence of wrapper calls with no inline inv blocks.

Live wrappers in `src/kernel/implementation/syscall_alloc_quota.rs`:

- `wlock_cpu`, `wunlock_cpu`
- `wlock_container_unless_killed`, `wunlock_container`
- `wlock_quota_4k`, `wunlock_quota_4k`
- `wlock_process_unless_killed`, `wunlock_process`

Consumer (syscall body) becomes a sequence of wrapper calls with NO
manual inv blocks between. Each wrapper carries its own SMT cost; the
consumer stays light. Adopt this pattern for every new lock primitive
introduced into the syscall layer.

**Measured win (allocate_free_4k_page, 2026-06-23).** The slow path was
calling allocator lock primitives *directly* on `allocator_4k_map`
(`wlock_global_poll`/`wunlock_global_poll`/`wunlock_cache`) followed by one
monolithic ~58-line inline `inv()` block. Wrapping them in three KernelK
wrappers (`wlock_allocator_global_poll`, `wunlock_allocator_global_poll`,
`wunlock_allocator_cache`, alongside the existing `wlock_allocator_cache`)
dropped the main function's own isolated `smt-run` from **253 ms → 73 ms
(−71%)** and verify-time 693 → 350 ms. Each wrapper's own SMT is ~55-95 ms.
Summed-serial total SMT barely moves (you redistribute obligations, you don't
delete them) — the win is (1) wall-clock via parallel `spinoff_prover` threads,
(2) incremental cost: editing the consumer body reruns a 73 ms query, not a
253 ms one, and the wrappers only re-verify when their own contract changes,
(3) reuse: every branch (fast path, lock-all scan) calls the same wrappers
instead of growing its own inline inv block. Measure isolated per-function
cost with `--verify-only-module <m> --verify-function <f> --time` and read the
`total smt-run` line.

## Per-invariant preservation lemmas

For each opaque bidirectional invariant, factor the heavy quantifier
reasoning into a dedicated lemma.

**File organization (IMPORTANT — enforced):**
- `src/kernel/spec_util.rs` holds **ONLY `spec fn`s** (the "objects unlocked"
  pieces, getters). NO `proof fn`s / lemmas / `external_body` axioms there.
- **Trusted (`external_body`) axioms** → `src/lemma/lemma_t/` (`lemma_t` = the
  trusted module). `seq_fold.rs` = the allocator cache-length fold lemmas;
  `kernel_fold_axioms.rs` = the process/thread set-fold quota axioms +
  `lemma_process_staged_pages_wf_preserved_for_view_eq`.
- **Proven (non-axiom) lemmas** → `src/lemma/lemma_u/` (`lemma_u` = verified).
  `kernel_preservation.rs` = all the `KernelK` preservation lemmas
  (`lemma_container_process_allocator_quota_wf_preserved_for_{process_lock_op,
  quota_transfer,alloc_stage}`, `lemma_container_allocator_free_*_page_wf_preserved_for_*`,
  `lemma_process_tree_wf_preserved_for_tree_fields_eq`,
  `lemma_process_perms_wf_preserved_for_process_lock_op`,
  `lemma_release_with_process_preserves_user_view`, etc.).
- Both `lemma_t`/`lemma_u` are dir modules with `general_{t,u}.rs` + topical
  files; re-exported flat via `crate::*` so call sites use bare names.
- Some preservation lemmas remain private in
  `src/kernel/implementation/syscall_alloc_quota.rs` (e.g.
  `lemma_container_{thread,endpoint,scheduler}_wf_preserved`,
  `lemma_release_preserves_user_view`).

The pattern: each lemma takes a clean pre/post pair, requires what's
relevant (per-element equalities, dom equality, etc.), ensures the
specific wf-conjunct holds in post. Heavy reasoning is contained in
the lemma's own SMT query.

**`reveal`-only asserts are prover-budget-fragile.** A bare
`assert(foo_wf(...)) by { reveal(foo_wf); }` that re-establishes a framed
invariant can pass in `--verify-function` isolation yet FAIL in the full-crate
run (different spinoff_prover budget/query order) — and a module move can tip
it over. The robust fix is NOT `rlimit` (it didn't help); supply the explicit
FRAME the predicate reads (e.g. for `process_thread_wf`: assert per-process
`owned_threads`/`pagetable` == entry, plus `thread_map == entry`), so the goal
discharges structurally regardless of budget. See the quota-transfer release
path in `syscall_alloc_quota.rs` (~line 2662).

## Trusted set-fold axioms (`spec_util.rs`)

The fold-based conjunct of `KernelK::inv()` is
`container_process_allocator_quota_wf` — a forall over containers
asserting the per-container quota equation:

```
fold(owned_processes, sum + process_map[p].view().quota_4k)
  + fold(owned_threads, sum + thread_map[t].view().direct_cache_4k)
  + fold(owned_indirect_threads, sum + thread_map[t].view().indirect_cache_4k[depth])
  + allocator[c.allocator_ptr_4k].quota.view().value
  ==
  allocator[c.allocator_ptr_4k].total_free_pages.view()
```

Verus has no built-in extensional set-fold equality. To preserve this
across operations, narrow `external_body` axioms in `spec_util.rs`:

- `lemma_process_effective_quota_{4k,2m,1g}_fold_eq` (pointwise eq → fold eq)
- `lemma_process_effective_quota_4k_fold_change_one` (one-element delta → fold delta)
- thread-pending fold variants (`lemma_thread_{direct,indirect}_pending_*`)

For the allocator's `total_free_pages_wf` (a `Seq` fold over live
`cpu_caches` lengths — the `differential` ghost field was removed; see
`current-work.md` § Recent state), the analogous
fact is the VERIFIED (non-axiom) `lemma_cache_len_fold_congruence` in
`lemma::lemma_t::seq_fold` (`src/lemma/lemma_t/seq_fold.rs`): equal-length
cache seqs with pointwise-equal `view().linked_list.len()` fold to the same
sum. Wired into `wlock_cache`/`wunlock_cache` to lift the fold across a
lock-state-only change. Its sibling `lemma_cache_len_fold_change_one` (same
file) handles the one-cache-shrank fold delta. (The `Seq`-fold lemmas live in
`lemma_t/seq_fold.rs`, NOT in `page_allocator.rs` — keep new fold lemmas there.)

Two verified preservation lemmas build on the set-fold axioms (no longer
external_body):

- `lemma_container_process_allocator_quota_wf_preserved_for_quota_transfer`
- `lemma_container_process_allocator_quota_wf_preserved_for_process_lock_op`

The `container_allocator_free_{4k,2m,1g}_page_wf` invariants (page ⟺ its
location in pool/cache; conjuncts of `memory_management_inv`) have their own
per-granule preservation lemmas + a thin combinator in `spec_util.rs`:
`lemma_container_allocator_free_{4k,2m,1g}_page_wf_preserved_for_lock_op` and
`lemma_container_allocator_free_pages_wf_preserved_for_lock_op`. Split
per-granule because the combined query exceeds rlimit (4k carries
`#[verifier::rlimit(100)]`). Hypotheses: pre-predicate + `container_page_owner_wf`
(owner ∈ container.dom) + `container_allocator_wf` (alloc_ptr ∈ allocator.dom) +
`page_array_wf` (page@.inv ⟹ free_state_inv ⟹ `cpu_id_valid` for PreCpuCache
pages) + per-projection equalities (page_array unchanged, container rodata
preserved, allocator global_poll/cache-payload/owning_container preserved).
Called at all 9 lock-op inv-re-establish sites (4 allocate wrappers + 5
syscall_alloc_quota release paths). (The history of *why* these predicates were
edited — three spec bugs — is in `.kiro/HISTORY.md`.)

When adding new TCB axioms, follow this pattern: NARROW axioms (one
fact each, concrete maps, lambda body inlined verbatim), then VERIFY the
broad lemma on top.

### `lemma_process_perms_wf_preserved_for_process_lock_op` (now PROVEN)

Previously an `external_body` axiom; now fully proved. The old `requires`
preserved only per-process `view()`/`view_rodata()`, which is NOT enough to
determine `process_perms_wf` — that predicate also reads (a) the map's
`PointsTo` `is_init()`/`addr()` via `perms_wf()`, and (b) each entry's
`locking_thread()` via `process_temp_alloc_empty_unless_wlocked`. The honest
hypotheses are: `post.perms_wf()`, target `inv()`, target payload preserved,
a full-equality frame on every non-target entry, AND a disjunct on the target
`locking_thread() is Write || view().temp_alloc_clean()`.

The disjunct exposed a real protocol obligation: **`wunlock_process` now
requires `temp_alloc_clean(process_ptr)`** ("flushed before wunlock", per the
`Process.temp_alloc_cache_*` docs). Once the process is unlocked it is no
longer `Write`, so the global invariant demands its temp-alloc cache be
empty — `wunlock_process`'s own `inv()` can't supply this (it exempts the
still-locked process). The fact is threaded down from
`wlock_process_unless_killed`, which now has a success-ensures
`view().temp_alloc_clean()` (a successful wlock proves `old.locked() == false`,
so the pre-lock invariant forces cleanliness, preserved across the lock by
`wlock_ensures`' `new@ == old@`). Release helpers
(`release_all_with_process_and_finish`, `transfer_quota_4k_and_finish`,
`release_cpu_and_process_and_finish` in syscall_new_thread) carry it as a
precondition. Any future syscall that STAGES pages (non-empty temp_alloc
cache) must drain them before calling `wunlock_process`.

## Spec-design idioms

### Opaque spec functions (replaces the old `_proof`/`_inner` triple)

```rust
#[verifier::opaque]
pub open spec fn FOO_wf(...) -> bool { /* body */ }
```

To unfold inside a proof block: `reveal(FOO_wf);`.

When an exec/proof function needs many specs unfolded, batch reveals at
the top of the function body in a single `proof { ... }` block. They
stay in scope. Re-issue inside nested `assert by { }` blocks.

### Bi-directional relation pattern

For X ↔ Y (mostly in `kernel/process_management/` and
`kernel/memory_management/`):

```rust
#[verifier::opaque]
pub open spec fn x_y_wf(x_map, y_map) -> bool {
    // forward refs from x to y
    forall|x_ptr| #![trigger ...]
        x_map.contains(x_ptr) ==> /* x's forward refs are in y_map.dom() */
    // derived field consistency
    forall|x_ptr, y_ptr| #![trigger ...]
        where x.refs_y(y_ptr) ==> /* y.parent == x_ptr, depth match, etc. */
    // back refs from y to x
    forall|y_ptr| #![trigger ...]
        y_map.contains(y_ptr) ==> /* y's back refs are in x_map.dom() */
}
```

Each clause needs `#![trigger ...]`. Trigger on the actual lookup chain
that appears in the formula.

### Page state with ghost payload

`PageState` derives `Clone, Copy, Debug, PartialEq`. Adding a variant
with `Ghost<T>` payload breaks the derives. The pattern: put the payload
as a regular type (e.g., `RwLockThreadPtr` which is `usize`) and treat
it as ghost-only at the use site. Match with:

```rust
state is OwnedXk
    ==> { let t = state->OwnedXk_thread_ptr; ... }
```

The `_thread_ptr` accessor is auto-generated by Verus from the variant.
Don't write `state matches PageState::OwnedXk{thread_ptr} ==> ...` —
`matches` doesn't compose with `==>`.

**`matches` patterns BIND, they never TEST against an outer variable
(verification foot-gun, 2026-06-24).** Writing
`state matches Free4k { state: PreCpuCache { cpu_id: cpu_i } }` does NOT assert
the field equals the enclosing `cpu_i` — Rust/Verus patterns can only introduce
a fresh binding, so `cpu_i` here is a *new* variable shadowing the outer one,
and the pattern is true for any value. It looks like a constraint but is
vacuous (and the crate still verifies — a non-constraining invariant conjunct
is trivially preservable, so a green build does NOT mean the invariant says
what you think). Also, a `matches` binding does NOT scope across the following
`&&` (unlike Rust `if let` chains): `(s matches Foo { x }) && x == k` fails with
"cannot find value `x`". To constrain an enum field, assert the variant with
`matches` and then compare via the field ACCESSOR in a separate conjunct:
`state->Free4k_state->PreCpuCache_cpu_id == cpu_i`. The `->Variant_field` chain
is the auto-generated accessor (nests for nested enums).

## Conventions to follow

- **No `_inner`/`_proof` triples in new code.** Use `#[verifier::opaque]`
  + `reveal(...)`.
- **Bi-directional specs are opaque.** Top-level conjunctions like
  `container_tree_wf` are plain `pub open spec` and just AND the parts.
- **`LockMinorTrait` for objects in collections is provided by the
  wrapper** (`PointsTo::lock_minor() == addr` for `LockedMap`,
  `LockedArrayElement::lock_minor() == index` for `LockedArray`). Inner
  objects don't need their own minor field. Exception: objects in bare
  `RwLock`s (e.g., `AllocatorQuota`, `LinkedList`) carry their own
  `Ghost<LockMinorId>`.
- **Triggers spell out the full chain.** `#![trigger
  m.spec_index(k).view().some_field]`, not auto.
- **`#[verifier::spinoff_prover]` on every helper, wrapper, lemma.**
- **Wrapper-per-lock-op for every new lock primitive added at the
  syscall layer.**
- **Narrow, concrete TCB axioms only.** No spec_fn-typed parameters in
  `external_body` axioms — Verus's higher-order matching is unreliable.

## Auto-trigger warnings

Verus emits "automatically chose triggers ... low confidence" notes for some
quantifiers. Rule of thumb:

- **Inside a function body** (an `assert forall ... implies ... by { }` block,
  not a kernel invariant, not a commonly-used axiom): suppress by accepting the
  auto-chosen trigger with `#![auto]` right after the binder, e.g.
  `assert forall|c_ptr: RwLockContainerPtr| #![auto] ...`. These are local proof
  steps; the auto trigger is fine and not worth a hand-annotation.
- **In a kernel invariant or a shared/common axiom**: do NOT blanket-`#![auto]`.
  Spell out the intended `#![trigger ...]` on the actual lookup chain — these
  quantifiers are instantiated everywhere and a bad trigger is expensive.

## Common gotchas

- `Ghost<usize>` doesn't impl `Clone, Copy, Debug, PartialEq`. Don't put
  it in `derive`d enums/structs. Use the underlying type and treat it as
  ghost at the use site.
- macOS sed needs `-E` for extended regex and doesn't support `\b` word
  boundaries. Use punctuation boundaries (`(`, `<`, `,`, etc.).
- Reveal scope is the proof block, not the file. For exec functions
  needing many reveals, batch them at the top.
- `cpu_tlb.rs` (in `kernel/`) and `pagetable_tlb_spec.rs` (in
  `memory_management/`) are NOT in the module tree. Don't bother fixing
  errors there — they're stale.
- `container_tree_check_is_ancestor` and `process_tree_check_is_ancestor`
  are exec functions that need 6 reveals each at the top of the body.

## Linearization model — quick reference

A syscall is one user-visible atomic transition. Lock acquisition order
is deadlock-free (`LockId::spec_gt`). The user-view linearization point
is `begin_user_view_step`; after it, no more locks may be acquired.

The model has TWO atomicity levels:
- **Kernel-view sections** (between `kernel_step_boundary` calls): one
  atomic transition each. Held objects pinned; unheld objects can change.
- **User-view steps** (between `begin_user_view_step` and
  `end_user_view_step`): one user-visible atomic transition each. May
  span multiple kernel sections, but our current syscalls don't.

The `KernelSteps.snap_shot` field enforces that U-mutations only happen
inside user-steps; the boundary's snapshot check catches stragglers.

## syscall_alloc_quota_4k — current state (REFERENCE EXAMPLE)

File: `src/kernel/implementation/syscall_alloc_quota.rs`. Fully
implemented including the success path. Reference for how to structure
syscalls in this codebase.

Path summary (all branches verified):
- container-killed → `release_cpu_and_finish` (1 lock held)
- quota-insufficient → `release_all_and_finish` (3 locks held)
- process-killed → `release_all_and_finish` (3 locks held)
- process-quota-overflow → `release_all_with_process_and_finish` (4
  locks held)
- all checks passed → `transfer_quota_4k_and_finish` (4 locks held;
  opens user step, mutates, releases, closes step, returns true)

Postconditions:
- failure: user step recorded, `old_u == new_u` (kernel-internal failure)
- success: user step recorded, `old_u == kernel_k_to_kernel_u(*old(self))`,
  `new_u` differs from `old_u` exactly by `process_map[p].quota_4k +=
  alloc_amount` (captured by the helper spec
  `kernel_u_only_process_quota_4k_changed`).

SMT timing reference (full call graph): ~1279 ms serial-summed across
~17 spinoff_prover queries. The syscall body itself: 124 ms. The
single-query monolith before factoring was ~5258 ms.

## Working preferences

- **No visible thinking/reasoning preamble.** Do not emit chain-of-thought
  or narrate the plan before acting; go straight to tool calls and give a
  terse result. (Token-saving.)

## Working with a human on a verification project (lessons)

How to be useful on this codebase specifically — learned across the
differential refactor, the `container_allocator_free_*_page_wf` wiring, and
the `allocate_free_4k_page` finish logic.

- **The spec is under active debugging — a green build does NOT mean correct.**
  Three real spec bugs were found *after* the crate verified at N, 0 errors
  (vacuous `global_poll && cache` antecedent; key/value swap in a `map()`
  lookup; an unconstrained cpu binder). A non-constraining or wrong invariant
  conjunct still verifies — it's just weaker than intended. When a clause looks
  off, reason about *what it actually says on all inputs* (esp. out-of-domain
  keys, fresh pattern binders, junk indices), not whether it compiles. Read
  the predicate's reads against the data structure's own `wf`/`map`/`view`
  contracts (e.g. "is this map keyed by node-addr or page-ptr?").
- **The user wants spec bugs surfaced, not worked around.** Standing
  instruction: when a proof can't go through because the *spec* is wrong (not
  just hard), STOP and report — what the clause says, why it's wrong, the
  minimal fix, and impact (does it only weaken inv()? any consumers?). Then
  wait for agreement before editing a kernel invariant. This has been the
  single highest-value behavior in the session. Do it "one bug at a time" when
  asked — present the first, fix on agreement, re-verify, move on.
- **Propose the fix, then sanity-check your own fix.** A first fix can be wrong
  in a subtle way (the `matches PreCpuCache { cpu_id: cpu_i }` "equality" that
  was actually a fresh binding). Re-read it adversarially before claiming done.
- **Verify in isolation, tight loop.** Use
  `./verify.sh --verify-only-module <m> --verify-function <f>` per function
  while iterating; only run the full crate to confirm no regression. Use
  `--multiple-errors N` to see all gaps at once. Read the failing line numbers
  from the output rather than guessing.
- **Build exec skeleton first, stage proofs behind `assume`.** For a large
  verified function, get the exec mechanics (borrows, perm threading, types,
  return value) compiling with `assume(false)` / targeted `assume`s standing in
  for proof obligations, THEN discharge them one by one. Each `assume` should
  be a precise, labeled statement of the real obligation (the corrected
  invariant applied here / untouched-submap preservation / lock-map
  bookkeeping), so the discharge pass is mechanical. Flagging these as TODO
  `assume`s with the user's knowledge ≠ silently papering over a gap — but get
  them OFF before declaring the function done.
- **Mid-mutation `self` loses sibling-submap facts.** After `borrow_mut` on one
  field of `KernelK`, the SMT often drops `wf`/`perms_wf`/`dom`-membership of
  *untouched* maps (`page_array.inv()`, `process_map.perms_wf()`), and full
  `KernelK::inv()` is genuinely false between the pop and the final
  re-establishment. Don't try to carry `inv()` through the middle — take the
  specific facts each call needs right before it, and rebuild `inv()` at the
  end (the wrapper-per-lock-op pattern exists for exactly this reason).
- **Additive `lemma_*_view` helpers for closed `wf`.** When a `wf()` is `closed`
  (e.g. `LinkedList::wf`), facts inside it (like `view().len() == length`) are
  sealed. Add a small `pub proof fn lemma_len_view(&self) requires wf() ensures
  view().len() == spec_len()` mirroring `LockedArray::lemma_view_len`, rather
  than fighting the opacity at each call site.

## Live work state → see current-work.md

Fast-moving state (what's verified now, in-progress functions, the spec-bug
log) lives in `.kiro/steering/current-work.md`, kept separate so these
architecture/convention notes stay stable. Check there for the latest
`allocate_free_4k_page` status and the
`container_allocator_free_*_page_wf` spec-bug history.
