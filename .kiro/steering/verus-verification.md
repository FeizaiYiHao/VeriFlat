# Verus Verification Workflow (VeriFlat)

When working with VeriFlat's Rust files (everything under `src/` is Verus
code with `verus!` blocks, `requires`, `ensures`, `proof fn`, etc.).

## Spec safety (read this first)

**Be very, very careful when changing the spec (`requires`/`ensures`) of a
public function** — especially anything outside a function's own module that
callers depend on. Helper functions used only inside one module are
lower-stakes; a public boundary function is a contract.

**Always ask the user before changing an invariant or the spec of a
public function.** This includes `requires`, `ensures`, struct invariants
(`wf` predicates), and any opaque/closed spec that callers reason about.
Even when a spec change looks like an obvious bug fix or strengthening,
stop and confirm with the user first — they may have context about
callers, design intent, or downstream consequences that aren't visible
locally. Mention what the change is and why before making it.

When you do change a public spec (with the user's go-ahead), two things
you MUST avoid:

1. **Never write contradictory `requires` or `assume`** (`requires 1 == 0`,
   `requires false`, `assume(false)`, etc.). A `false` precondition makes
   the function vacuously verifiable but unsound — every caller that proves
   the precondition has actually proved `false` and can prove anything.
2. **Never introduce a postcondition that, together with the new
   preconditions, is unsatisfiable.** This is the same trap one indirection
   away: an unsatisfiable spec means the function can be "proved" but
   collapses to `false` at any call site.

**Exception: TCB-only gates.** A primitive declared `external_body` and
intended to be called only by other trusted (`external_body`) wrappers may
use `requires true == false` (or `requires false`) as a deliberate gate —
verified code cannot prove the precondition, so it cannot call the
primitive. This pattern is sound because:
  - the body bypasses verification (`external_body`),
  - verified callers are blocked at the precondition,
  - only trusted callers reach the body, and they take responsibility.
The pattern is in active use for `wlock_external` / `wunlock_external` in
`src/locks/rwlock.rs`. Don't replicate it casually; ask the user before
introducing a new TCB gate.

After changing any `requires` or `ensures`, verify the spec is still
consistent by adding a temporary `assert(false);` as the first line of the
function body and running `./verify.sh --verify-only-module <m>
--verify-function <f>`. If `assert(false)` succeeds, the spec is
inconsistent — fix it before continuing. Remove the `assert(false)` once
verification fails as expected. (For TCB gates with `requires false`, this
self-check is meaningless because the body is `external_body`; skip the
check there.)

This applies to lemmas (`proof fn`) too: a vacuous lemma with
contradictory preconditions or an unsatisfiable postcondition is worse
than no lemma — it silently corrupts every proof that uses it.

## How to verify in this project

- Whole crate: `./verify.sh` from the project root. Works in bash and zsh.
- Specific module: `./verify.sh --verify-module <path>` (e.g.,
  `--verify-module kernel::implementation::syscall_alloc_quota`).
- Specific function: `./verify.sh --verify-function <name> --verify-module
  <path>`.
- The MCP tools below also work and provide structured output.

Module paths follow the file tree under `src/`:

- `src/kernel/process_management/container_thread_spec.rs` →
  `kernel::process_management::container_thread_spec`
- `src/locks/rwlock.rs` → `locks::rwlock`
- `src/allocator/page_allocator.rs` → `allocator::page_allocator`

Current baseline: **295 verified, 0 errors**. Don't introduce regressions.

## Available MCP Tools (verus-mcp-server)

- `verify_and_diagnose` — Verify a single function, parse errors, return a
  prescriptive `nextAction`. Pass `verifyFunction` + `verifyModule`.
- `verify_and_diagnose_with_proof_state` — Same but with
  `-V proof-state-on-failure`. Returns the solver's assumptions and goals.
  Use when stuck on a proof.
- `verify_all` — Whole crate or a `verifyModule`. Use for regression checks.
- `search_vstd_lemmas` — Search vstd and project stdlib for lemmas.
- `read_verus_guide` — Read Verus documentation on specific topics.
- `reduce_resource_usage` — Auto-optimize a function's SMT resource usage.

**Workflow**: `verify_all` (module) → identify failing functions →
`verify_and_diagnose` (per function) → fix → repeat. When stuck, use
`verify_and_diagnose_with_proof_state` to see what the solver knows vs
what it needs.

## CRITICAL: Execute nextAction mechanically

When `verify_and_diagnose` or `verify_and_diagnose_with_proof_state` returns
a `nextAction`, execute it exactly as described:

1. Read `nextAction.action`:
   - `apply_edit`: Use strReplace with the provided `edit.file`,
     `edit.oldText`, `edit.newText`.
   - `search_lemma`: Call `search_vstd_lemmas` with the query from
     `toolCall.args`.
   - `run_command`: Call the MCP tool specified in `toolCall`.
   - `read_file`: Read the specified file, then apply the described change.
   - `manual`: Follow the description.
2. After applying, re-verify using `verifyAfter.verifyModule` and
   `verifyAfter.verifyFunction`.
3. Repeat until verification passes.

Do NOT skip the nextAction. Do NOT make ad-hoc decisions.

## General approach

When fixing verification errors in a module:

1. Run `verify_all` with `verifyModule` ONCE for the full error list.
2. Identify each failing function and its error type.
3. Fix functions ONE AT A TIME — `verify_and_diagnose` with `verifyFunction`
   + `verifyModule` for fast re-checks.
4. If `verify_and_diagnose` isn't enough, use
   `verify_and_diagnose_with_proof_state` to see solver assumptions/goals.
5. Re-verify in isolation before moving to the next.
6. Re-run `verify_all` only as a final regression check.
7. Never batch-edit multiple functions — changes can interact unexpectedly.

## VeriFlat-specific verification patterns

### Reveal-based unfolding (replaces the old `_proof`/`_inner` triple)

Bi-directional kernel invariants are `#[verifier::opaque] pub open spec
fn`. Their bodies don't auto-unfold. To reason about them inside a proof:

```rust
assert(container_process_wf(self.container_map, self.process_map)) by {
    reveal(container_process_wf);
};
```

When an exec function needs many opaque specs unfolded, batch the reveals
at the top of the function body:

```rust
{
    proof {
        reveal(container_root_wf);
        reveal(container_uppertree_seq_wf);
        // ...
    }
    // function body — reveals stay in scope
}
```

### Two-phase locking and `LocalContext`

Most spec preconditions reference `LocalContext` state:

- `lctx.kernel_view_locking_state() is Acquire` — section is in the
  acquire phase, locks may still be taken.
- `lctx.user_view_locking_state() is Release` — syscall has linearized,
  user-visible state can be released.
- `lctx.lock_id_acyclic(lock_id)` — the new lock id is greater than the
  current `last()` of `lock_seq` (deadlock-freedom ordering).

When a `wlock` precondition fails, check:
- Is the section still in `Acquire` phase? (`unlock` flips it to `Release`,
  permanently for that section.)
- Is `lock_id_acyclic` satisfied? (Check `LockId.md` for the ordering.)
- For user-visible objects, has the syscall flipped `user_view_locking_state`
  if it's about to unlock?

### Bi-directional spec failure → reveal first

If a proof obligation looks like a bi-directional consequence
(`container_map.contains(c) ==> process_map.contains(c.root_process)`),
the spec is almost certainly opaque. Reveal it.

### Page state matching

Don't write `state matches PageState::OwnedXk{thread_ptr} ==> ...`. The
`matches` syntax doesn't compose with `==>`. Use:

```rust
state is OwnedXk
    ==> { let t = state->OwnedXk_thread_ptr; ... }
```

The `_thread_ptr` accessor is auto-generated by Verus from the variant.

## Timeout optimization loop

If a function has a timeout/rlimit error, in order:

1. Add `#[verifier::spinoff_prover]` → re-verify.
2. Add `#[verifier::rlimit(20)]` → re-verify. Try 30, 40, 50. Don't exceed 50.
3. **Scope broadcast use statements**: move module-level `broadcast use`
   inside the function in a proof block; comment out unused ones.
   Re-verify after each. Often the most-skipped step — don't skip it.
4. Add `hide()` for spec functions called but whose details aren't needed.
5. Create helper proof lemmas.
6. Use `assume(false)` to isolate problematic paths.

For VeriFlat specifically, the most common cause of slowness is too many
opaque specs being implicitly required. Try `reveal` only the ones the
goal actually mentions.

## Failure strategies

### Assertion failures

1. If conjunction (`A && B && C`), split into separate asserts. If the
   spec function is internally a conjunction, look up the definition and
   assert each conjunct separately. Use `reveal()` first if opaque.
2. Find the targeted lemma with `search_vstd_lemmas`. Always
   `broadcast use` the individual lemma, not a broad group.
3. If no lemma helps, try calling method lemmas directly
   (e.g., `seq.lemma_seq_skip_skip(i as int)`).
4. Use `assert(...) by { ... }` and `#[trigger]` annotations.
5. `read_verus_guide` for "forall", "extensional_equality", "triggers".

### Invariant failures (loop invariant not satisfied)

At the failure point, add an `assert` restating the invariant. Converts
to an assertion failure — apply the assertion strategy.

### Precondition failures

Run with `extraFlags: ["--expand-errors"]` to identify which `requires`
clause failed. Add an `assert` for it before the call site.

For VeriFlat, the most common `requires` failures are:

- Missing `reveal(opaque_spec)` at the call site.
- Wrong phase of `LocalContext` (`Acquire` vs `Release`).
- Wrong lock-id ordering (`lock_id_acyclic` not satisfied).

### Postcondition failures

Run with `--expand-errors`. Use `assume(false)` on different exit paths
to isolate the failing one. At the failing exit, assert the ensures
clause.

## Project resources

- `Methodology.md` (project root) — conceptual model.
- `LockId.md` — lock ordering scheme.
- `SystemCalls.md` — syscall lock-acquire orders.
- `README.md` — high-level overview.
- `.kiro/steering/veriflat-project-notes.md` — operational notes (module
  layout, RwLock generics, conventions, gotchas).
- vstd library: `search_vstd_lemmas` for seq, map, set lemmas.
- Verus guide: `read_verus_guide` for triggers, quantifiers, proofs.

## Stale files (do NOT spend time fixing)

These files exist on disk but are NOT in the module tree, so verification
errors there are inert:

- `src/kernel/cpu_tlb.rs` (the active version is in
  `kernel/cpu_tlb_management/`).
- `src/kernel/memory_management/pagetable_tlb_spec.rs` (entirely
  commented out).
- `src/allocator/spec_define.rs` (entirely commented out).

## Hard-won Verus techniques (session learnings — keep these)

These are concrete, repeatedly-useful facts discovered while adding the
user-step postcondition to `syscall_alloc_quota_4k`. They are not obvious
from the Verus guide.

### Running the verifier (the MCP tools may be broken)

- The `verus-mcp-server` tools (`verify_all`, `verify_and_diagnose`, …) can
  fail on this machine with `./verus.sh: No such file or directory`. When
  that happens, drive Verus directly with `./verify.sh` (it forwards all
  flags to the verifier binary).
- Single function: `./verify.sh --verify-function NAME --verify-only-module
  PATH`. NOTE: with `--verify-function` you MUST use `--verify-only-module`,
  NOT `--verify-module` (the latter errors out).
- Whole module: `./verify.sh --verify-module PATH` or
  `--verify-only-module PATH`.
- Add `--expand-errors` to see *which* `requires` clause / conjunct failed
  (precondition + postcondition failures otherwise point only at the call
  site / function header).
- Because the MCP `verify_and_diagnose_with_proof_state` may be unavailable,
  you often cannot see the solver's assumptions/goals. Plan proofs
  defensively (small isolated lemmas) rather than relying on proof-state.

### Threading tracked state so the POSTCONDITION can see mutations

- A by-value `tracked mut x: Tracked<T>` parameter does **not** export its
  final value: `old(x)` is rejected ("expected `&mut`, found Tracked"), and
  an `ensures x@ …` refers to the ENTRY value, not the mutated one. Asserts
  inside the body can pass while the identical postcondition fails — this is
  the tell-tale sign.
- Fix: thread the tracked state as `Tracked(x): Tracked<&mut T>` (destructured
  param). Then in `ensures` use `final(x)` for the post-state (and `old(x)`
  for pre). Inside the body call methods directly on `x` (it is `&mut T`).
  This is the idiomatic mutable-tracked pattern (see Verus tests
  `mut_refs.rs`, `wrapped_params`).
- Call site: if the caller holds `Tracked<T>` by value, pass
  `Tracked(caller.borrow_mut())`; if the caller already has `&mut T` (i.e. it
  too received `Tracked(x): Tracked<&mut T>`), pass `Tracked(&mut *x)`.
- You CANNOT reassign a `tracked` place in exec context
  (`steps = self.helper(...)` → "cannot access proof-mode place in
  executable context"). Use the `&mut` threading above instead of
  returning-and-rebinding.
- Post-state of `&mut self`: this codebase writes `final(self)` (works for
  both exec and proof fns). For a `Tracked(g): Tracked<&mut U>` param,
  `final(g)` is the post `U`; for `Tracked(g): Tracked<&mut int>`,
  `*final(g)`.

### closed-spec opacity across modules

- A `closed spec fn` body is invisible OUTSIDE its defining module, even via
  another closed spec. Example: `LockedArray::inv()` (= `array.wf()` =
  `seq.len() == N`) and `LockedArray::view()` are both `closed`, so
  `view().len() == N` is NOT derivable in client code from `inv()`.
- Fix: add an ADDITIVE helper in the defining module that exposes the true
  consequence, e.g.
  `pub proof fn lemma_view_len(&self) requires self.inv() ensures self.view().len() == N {}`.
  This changes no existing spec and is sound. (Added to `lock_array.rs`.)

### Butterfly effect in spinoff_prover functions

- A whole `#[verifier::spinoff_prover]` function is ONE SMT query. Adding a
  large quantifier-heavy proof block can make a DIFFERENT, previously-passing
  `assert` elsewhere in the same function start to fail. This is not a
  resource limit — bumping `#[verifier::rlimit(..)]` does NOT help.
- Fix: extract the quantifier-heavy reasoning into its own `proof fn` lemma
  (its own query). The caller just establishes the lemma's (cheap)
  preconditions and calls it. This is the single most effective tool for
  taming large exec proofs.

### reveal scoping

- `reveal(foo)` is lexically scoped to the enclosing proof block. It does
  NOT reliably propagate into nested `assert ... by { }` or
  `assert forall ... by { }` sub-blocks. Re-issue `reveal(foo)` inside each
  nested `by` block that needs it.

### Extensional equality of projected sequences/maps

- To prove `Seq::new(n, f) =~= Seq::new(n, g)`, prove element-wise:
  `assert forall|i: int| 0 <= i < n implies #[trigger] f(i) == g(i) by { … }`.
  Then `=~=` closes it. For a struct of two such fields (e.g. `KernelU`
  with `cpu_array: Seq` + `process_map: Map`), prove each field `=~=` and
  the struct equality follows.
- Bridge `LockedArray::view()[i]` (Seq index, used by projections) to
  `spec_index(i).value` / `spec_index(i)@` — they are the same underlying
  RwLock (`spec_index` is `open` so it unfolds to `self@[i as int]`).
- To use `unchanged_except` (quantified `0 <= i < N`) over a projection
  range `0 <= i < view().len()`, you need `view().len() == N` — get it from
  `lemma_view_len`.

### unchanged_except → full element equality

- `unchanged_except(old, key)` gives per-element equality for every
  element except `key`. Combine with a fact about `key` itself to get FULL
  per-element equality `forall k: self.spec_index(k) == old.spec_index(k)`.
  Full element equality is far stronger than payload-view equality and makes
  wf-conjuncts transfer almost trivially — prefer it whenever the operation
  preserves the touched element (e.g. a FAILED `wlock_unless_killed` restores
  its element: false branch gives `old[key] == final[key]` and the
  unconditional `unchanged_except` covers the rest).
- Payload-view equality (`spec_index(k).view() == …`) is NOT enough for
  conjuncts that need the element's `@.inv()` (= `view().inv() && is_init()`).
  is_init is not a function of the payload view. Either use full element
  equality, or carry an explicit `spec_index(k).view().inv()` fact (lock
  op ensures provide `final[key]@.inv()`).

### Bidirectional invariants are the hard case

- A bidirectional relation (e.g. `container_cpu_wf`: container→cpu AND
  cpu→container) is hard to re-establish through an abstraction boundary.
  When both related objects changed lock state, the FORWARD direction often
  instantiates fine, but the REVERSE direction's `forall` may refuse to fire
  even with the trigger term present and the spec `reveal`ed and asserted
  true. This needed proof-state debugging that wasn't available. If you hit
  this, prefer keeping the re-establishment proof in the SAME context as the
  fresh lock-operation ensures (an inline proof, like the existing
  `release_all_and_finish` does with a plain `reveal(container_cpu_wf)`)
  rather than abstracting it into a lemma with view/element-equality
  preconditions.

### Never weaken soundness to make progress

- Do NOT use `assume(false)`, `requires false`, or contradictory specs to
  "stub out" an unfinished branch — it is unsound and silently corrupts
  every caller (and the user explicitly forbade it). The sound way to defer
  a branch that can't yet satisfy a postcondition is to NOT add that
  postcondition yet (keep the verified property on a factored helper), or
  implement the branch properly.
