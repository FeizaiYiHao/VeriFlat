# Verus Verification Workflow (VeriFlat)

When working with VeriFlat's Rust files (everything under `src/` is Verus
code with `verus!` blocks, `requires`, `ensures`, `proof fn`, etc.).

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
