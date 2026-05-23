---
inclusion: fileMatch
fileMatchPattern: "**/*.rs"
---

# Verus Verification Workflow

When working with Verus Rust files (files containing `verus!` blocks, `requires`, `ensures`, `proof fn`, etc.):

## Available MCP Tools (verus-mcp-server)

- `verify_and_diagnose` — Verifies a single function, parses errors, and returns a prescriptive `nextAction`. Requires
  `verifyFunction` + `verifyModule`.
- `verify_and_diagnose_with_proof_state` — Like `verify_and_diagnose`, but runs with `-V proof-state-on-failure`. When a
  proof fails, returns the assumptions the solver proved and the goal it couldn't discharge, plus a proof-state-aware
  `nextAction` that suggests specific lemma searches based on the gap. Requires `verifyFunction` + `verifyModule`.
- `verify_all` — Run verification on the entire crate or a specific module (optional `verifyModule`). Use for regression
  checks or module-level error overview.
- `search_vstd_lemmas` — Search vstd and project stdlib for lemmas to help with proofs.
- `read_verus_guide` — Read Verus documentation on specific topics.
- `reduce_resource_usage` — Automatically optimize a function's SMT resource usage.

**Workflow**: `verify_all` (module) → identify failing functions → `verify_and_diagnose` (per function) → fix → repeat.
When stuck on a proof, use `verify_and_diagnose_with_proof_state` to see what the solver knows vs what it needs.

## CRITICAL: Execute nextAction mechanically

When `verify_and_diagnose` or `verify_and_diagnose_with_proof_state` returns a `nextAction`, you MUST execute it exactly
as described:

1. Read the `nextAction.action` field to determine what to do:
   - `apply_edit`: Use strReplace with the provided `edit.file`, `edit.oldText`, `edit.newText`
   - `search_lemma`: Call `search_vstd_lemmas` with the query from `toolCall.args`
   - `run_command`: Call the MCP tool specified in `toolCall`
   - `read_file`: Read the specified file to understand context, then apply the described change
   - `manual`: Follow the description — it contains the specific guidance
2. After applying the action, re-verify using `verifyAfter.verifyModule` and `verifyAfter.verifyFunction`
3. Repeat until verification passes

Do NOT skip the nextAction. Do NOT make ad-hoc decisions. Do NOT jump ahead. Execute mechanically.

## General Approach

When fixing verification errors in a module:

1. Run `verify_all` with `verifyModule` ONCE to get the full error list for the module. Store/analyze this output.
2. From the output, identify each failing function and its error type. Do NOT re-run the full module verification
   repeatedly — it's slow.
3. Fix functions ONE AT A TIME — use `verify_and_diagnose` with `verifyFunction` + `verifyModule` for fast re-checks.
4. If `verify_and_diagnose` isn't enough to understand a failure, use `verify_and_diagnose_with_proof_state` to see the
   solver's assumptions and goals.
5. After fixing one function, re-verify it in isolation before moving to the next.
6. Only re-run `verify_all` AFTER all individual functions have been fixed, as a final regression check.
7. Never batch-edit multiple functions at once — changes can interact in unexpected ways.

## Timeout Optimization Loop

When a function has a timeout/rlimit error, follow these steps IN ORDER. Do NOT skip any step:

1. Add `#[verifier::spinoff_prover]` → re-verify
2. Add `#[verifier::rlimit(20)]` → re-verify. If still failing, try 30, 40, 50. Do NOT exceed 50.
3. **Scope broadcast use statements**: Find module-level `broadcast use` in the file. Move them INSIDE the function in a
   proof block. Comment out ones the function doesn't need. Re-verify after each change. This is the most commonly skipped
   step — DO NOT SKIP IT.
4. Add `hide()` for spec functions called but whose details aren't needed → re-verify
5. Create helper proof lemmas → re-verify
6. Use `assume(false)` to isolate problematic paths → re-verify

## Verification Failure Strategies

### Assertion Failures
1. If the assertion is a conjunction (A && B && C), split into separate asserts to isolate which conjunct fails. If the
   assertion calls a spec function that internally is a conjunction (e.g. `assert(is_valid(x))` where `is_valid` is
   `A &&& B &&& C`), look up the spec function definition and assert each conjunct separately. Use `reveal()` first if the
   spec is opaque. Re-verify, then remove the passing asserts — keep only the failing one to focus on.
2. Find the SPECIFIC targeted lemma using `search_vstd_lemmas`. Always `broadcast use` the individual lemma, NOT a broad
   group. Broad groups add noise and can make the solver slower. Example: use `broadcast use stdlib::str_empty_if_len0;`
   not `broadcast use stdlib::string_props;`.
3. If no single lemma helps, try calling method lemmas directly in a proof block (e.g.
   `seq.lemma_seq_skip_skip(i as int)`)
4. If no lemma helps, use `reveal()`, `assert(...) by { ... }`, or `#[trigger]` annotations
5. Use `read_verus_guide` for topics like "forall", "extensional_equality", "triggers"

### Invariant Failures (loop invariant not satisfied)
1. At the point where the invariant fails (end of loop body), add an `assert` restating the invariant
2. This converts it to an assertion failure — then apply the assertion failure strategy above

### Precondition Failures
1. Run with `extraFlags: ["--expand-errors"]` to identify which requires clause failed
2. Add an `assert` for the failed precondition just before the function call
3. This converts it to an assertion failure — then apply the assertion failure strategy

### Postcondition Failures
1. Run with `extraFlags: ["--expand-errors"]` to identify which exit path and ensures clause fails
2. Use `assume(false)` on different exit paths to isolate the failing one
3. At the failing exit, add an `assert` restating the ensures clause
4. This converts it to an assertion failure — then apply the assertion failure strategy

## Key Resources

- vstd library: search with `search_vstd_lemmas` for seq, map, set lemmas
- Verus guide: read with `read_verus_guide` for topics like triggers, quantifiers, proofs
- Project stdlib: `src/verus/stdlib.rs` has custom HashMap bridging lemmas and other helpers

## Scoped Verification

- `verifyModule`: derived from file path, e.g. `src/impl_verified/arn.rs` → `impl_verified::arn`
- `verifyFunction`: the function name, e.g. `get_resource_types_with_visibility`

## Platform Detection

- macOS → `./verus.sh`
- Linux → `cargo verus verify`
