# Verus Verification Workflow (VeriFlat)

When working with VeriFlat's Rust files (everything under `src/` is Verus
code with `verus!` blocks, `requires`, `ensures`, `proof fn`, etc.).

## Spec safety (read this first)

**Be very careful when changing the spec (`requires`/`ensures`) of a
public function** — anything outside a function's own module that callers
depend on is a contract. Helper functions used only inside one module are
lower-stakes; a public boundary function is not.

**Always ask the user before changing an invariant or the spec of a
public function.** This includes `requires`, `ensures`, struct invariants
(`wf` predicates), and any opaque/closed spec that callers reason about.
Even when a spec change looks like an obvious bug fix or strengthening,
stop and confirm with the user first.

When you do change a public spec (with the user's go-ahead), two things
to MUST avoid:

1. **Never write contradictory `requires` or `assume`** (`requires false`,
   `assume(false)`, etc.). A `false` precondition makes the function
   vacuously verifiable but unsound — every caller proves `false` and can
   prove anything.
2. **Never introduce a postcondition that, together with the new
   preconditions, is unsatisfiable.** Same trap one indirection away.

**Exception: TCB-only gates.** A primitive declared `external_body` and
intended to be called only by other trusted (`external_body`) wrappers may
use `requires false` as a deliberate gate. The pattern is in active use
for `wlock_external` / `wunlock_external` in `src/locks/rwlock.rs`. Don't
replicate casually; ask before adding a new TCB gate.

After changing any `requires` or `ensures`, verify the spec is still
consistent by adding a temporary `assert(false);` as the first line of the
function body and running `./verify.sh --verify-function <f>
--verify-only-module <m>`. If `assert(false)` succeeds, the spec is
inconsistent — fix it before continuing. (Skip this for `external_body`
TCB gates with `requires false` — the body bypasses verification.)

This applies to lemmas (`proof fn`) too: a vacuous lemma silently
corrupts every proof that uses it.

## Soundness rules — never weaken

- Do NOT use `assume(false)`, `requires false`, or contradictory specs to
  "stub out" an unfinished branch. Sound ways to defer: don't add the
  postcondition yet, or factor the verified property onto a helper that
  doesn't yet need to handle that branch.
- TCB axioms must be NARROW. Prefer many small `external_body` lemmas
  each capturing one specific fact over one big "this whole invariant is
  preserved" axiom. See "TCB axiom design" below.

## How to verify

Whole crate: `./verify.sh` from project root. Works in bash and zsh.

Single function: `./verify.sh --verify-function NAME --verify-only-module
PATH`. Note: with `--verify-function` you MUST use `--verify-only-module`
(`--verify-module` errors out with selected functions).

Whole module: `./verify.sh --verify-only-module PATH`.

With timing: add `--time`. Look at `total smt-run` for SMT-only cost.

With error expansion: add `--expand-errors` to see which `requires` clause
or which `&&` conjunct of an ensures failed.

Module paths follow the file tree: `src/kernel/spec_util.rs` →
`kernel::spec_util`, `src/locks/rwlock.rs` → `locks::rwlock`.

Current baseline: **402 verified, 0 errors**. Don't introduce
regressions. Run `./verify.sh` after any non-trivial change.

## Verification-cost reduction tactics (THE CORE PLAYBOOK)

VeriFlat's syscalls cross many invariants and would otherwise produce
multi-thousand-millisecond SMT queries. These are the techniques that have
been most effective on this codebase:

### 1. `#[verifier::spinoff_prover]` everywhere

Every helper function, every wrapper, every preservation lemma gets
`#[verifier::spinoff_prover]`. This makes each function its own
independent SMT query. The biggest single win: a 5258 ms syscall body
became 124 ms after factoring helpers and adding spinoff_prover to each.

### 2. Wrapper-per-lock-op pattern (THE most useful structural pattern)

For each lock primitive (`wlock_*`, `wunlock_*`, `wlock_*_unless_killed`)
add a wrapper method on `KernelK` that internally calls the primitive AND
re-establishes `KernelK::inv()`. Wrappers are `#[verifier::spinoff_prover]`.

```rust
#[verifier::spinoff_prover]
pub fn wunlock_cpu(&mut self, cpu_id: CpuId, ...)
    requires
        old(self).inv(),
        // ...lock-state preconditions...
    ensures
        final(self).inv(),
        // field-by-field framing of what changed
{
    self.cpu_array.wunlock(...);
    proof {
        // re-establish inv() — heavy reveal block
    }
}
```

Consumer code becomes a sequence of wrapper calls with no manual inv
blocks between them. Each wrapper carries its own SMT cost; the consumer
syscall stays light.

### 3. Per-invariant preservation lemmas

For each opaque bidirectional invariant (`container_thread_wf`,
`container_endpoint_wf`, `container_scheduler_wf`, etc.) create a
preservation lemma:

```rust
proof fn lemma_container_thread_wf_preserved(pre: KernelK, post: KernelK)
    requires
        container_thread_wf(pre.container_map, pre.thread_map),
        post.thread_map == pre.thread_map,
        post.container_map.dom() == pre.container_map.dom(),
        forall|c: ...| post.container_map[c].view() == pre.container_map[c].view(),
    ensures
        container_thread_wf(post.container_map, post.thread_map),
{ ... reveal-laden body ... }
```

The heavy quantifier reasoning lives in the lemma (one isolated SMT
query); the consumer just calls the lemma and provides cheap
preconditions. The 4-quantifier reverse-direction reasoning that would
otherwise blow up the consumer's query is contained.

### 4. Helper extraction over inline proofs

When a syscall has multiple distinct exit paths or sub-stages, factor
each into its own function with a clean spec:

- `release_all_and_finish` (3-lock failure path)
- `release_all_with_process_and_finish` (4-lock failure path)
- `transfer_quota_4k_and_finish` (success path)
- `release_cpu_and_finish` (cpu-only failure path)

The syscall body becomes a thin orchestrator. Each helper's proof is its
own SMT query. The total work is the same but distributed across many
small queries.

### 5. Function-wide reveal block at the top

When a function needs many opaque specs unfolded, batch them in a single
`proof { reveal(...); reveal(...); ... }` at the top of the function body.
Reveals stay in scope for the rest of the function body.

```rust
fn syscall_alloc_quota_4k(...) {
    proof {
        reveal(cpu_array_wf);
        reveal(container_perms_wf);
        reveal(allocator_perms_wf);
        // ...
    }
    // rest of body — reveals are in scope
}
```

Verus prunes definitions aggressively; without the reveal, even an
`assert` of a known fact will fail.

### 6. Narrow `external_body` axioms over broad ones

If a verified proof needs a fact you can't directly derive (e.g.,
extensional set-fold equality), expose it as a narrow `external_body`
lemma matching the user's `fold_change_mem_4k_lemma` template style:
**concrete maps as parameters, lambda body inlined verbatim**, no
spec_fn-typed parameters. Verus's higher-order matching is unreliable;
concrete forms unify trivially at call sites.

Example from this codebase: replaced ONE big trusted axiom
"`container_process_allocator_quota_wf` is preserved across X" with FOUR
narrow ones (`lemma_process_quota_4k_fold_eq_under_view_eq`, similarly
for 2m/1g, plus `lemma_process_quota_4k_fold_change_one`), and a
verified preservation lemma calls them. The TCB shrinks; the proof
becomes auditable per-axiom.

### 7. Fewer reveals per `assert by` block

Reveals are NOT auto-imported into nested `by` blocks. Each
`assert by { reveal(spec); ... }` needs its own reveals. This isn't a
cost-reduction technique per se but failing to follow it causes
inscrutable assertion failures.

### 8. Trigger annotations on quantifiers

Verus's auto-trigger selection for kernel-style quantifiers is weak.
Annotate explicitly:

```rust
forall|c: RwLockContainerPtr|
    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Container(c))]
    old(lctx).lock_map().dom().contains(KernelObjId::Container(c))
    ==> ...
```

Trigger on the actual lookup chain that appears in the formula. Bad
triggers → either no instantiation or 100x instantiation. Fix by spelling
out the right ones.

## Proof-structure patterns

### `assert(...) by { reveal(...); ... }` — the spec-unfolding wedge

Opaque spec functions don't auto-unfold. To prove a goal that requires
the body of `foo`:

```rust
assert(foo(args)) by { reveal(foo); /* whatever else */ };
```

Verus uses the body during proof of the assertion only. This contains
the opacity reveal to the smallest possible scope.

### Hierarchical `assert by` for compound goals

For a compound `&&&` goal, asserting the whole thing in one shot can fail
even when each conjunct is provable. Split:

```rust
assert(foo) by { reveal(spec_1); };
assert(bar) by { reveal(spec_2); };
assert(baz) by { reveal(spec_3); };
// the surrounding context now has foo, bar, baz; the original conjunction follows.
```

### The wf-re-establishment proof block

After any operation that changes lock state (acquire, release, transfer
etc.), `inv()` is invalidated. Re-establish it via a structured proof
block listing every conjunct of `inv()` once:

```rust
proof {
    reveal(cpu_array_wf);
    reveal(container_perms_wf);
    reveal(allocator_perms_wf);
    reveal(process_perms_wf);
    // ---- subsystems_inv ----
    assert(cpu_array_wf(self.cpu_array, self.default_pagetable.view())) by {
        reveal(cpu_array_wf);
    };
    assert(container_perms_wf(self.container_map)) by {
        reveal(container_perms_wf); reveal(container_tree_fields_wf);
    };
    // ... one assert-by per conjunct ...
    assert(self.subsystems_inv()) by { reveal(KernelK::default_pagetable_wf); };
    // ---- memory_management_inv ----
    // ...
    assert(self.inv());
}
```

Each conjunct's `assert by` block reveals only what's needed for that
conjunct. Bidirectional invariants get factored into preservation
lemmas (see point 3 above). The final `assert(self.inv())` is the
combine step.

### `unchanged_except` → full-element equality

`unchanged_except(old, key)` gives per-element equality for every
element except `key`. Combine with a fact about `key` itself to get FULL
per-element equality `forall k: self.spec_index(k) == old.spec_index(k)`.
Full element equality transfers wf-conjuncts almost trivially. Always
prefer this when an operation preserves the touched element (e.g. a
FAILED `wlock_unless_killed` restores its element, so the false branch
gives `old[key] == final[key]` and `unchanged_except` covers the rest).

### Extensional equality of projected sequences/maps

To prove `Seq::new(n, f) =~= Seq::new(n, g)`, prove element-wise:

```rust
assert forall|i: int| 0 <= i < n implies #[trigger] f(i) == g(i) by { ... };
```

Then `=~=` closes it. For a struct of two such fields (e.g. `KernelU`
with `cpu_array: Seq` + `process_map: Map`), prove each field `=~=` and
the struct equality follows.

To use `unchanged_except` (range `0 <= i < N`) over a projection range
`0 <= i < view().len()`, you need `view().len() == N` — get it from
`lemma_view_len`.

## TCB axiom design

When you cannot derive a fact from primitives, add a NARROW
`external_body` axiom. Rules:

1. **One fact per axiom.** Don't bundle "everything is preserved" into one
   lemma; expose one specific fact (e.g. "this fold equals that fold under
   pointwise equality").
2. **Concrete signature, not generic.** Verus's higher-order matching
   doesn't reliably unify `f(x)` against complex expressions. Inline the
   field access in the lambda body of the post-condition. Match the
   user's `fold_change_mem_4k_lemma` template:

   ```rust
   #[verifier::external_body]
   pub proof fn lemma_X_preserved(s: Set<P>, pre: Map<...>, post: Map<...>)
       requires forall|p: P| s.contains(p) ==> pre[p].field == post[p].field,
       ensures s.fold(0, |sum, p| sum + post[p].field)
              == s.fold(0, |sum, p| sum + pre[p].field),
   {}
   ```

3. **Document the soundness rationale in the doc comment.** State why
   this should be true ("induct on s, base case 0==0, insert step uses
   lemma_fold_insert plus IH").
4. **Verify everything else on top.** Each "broad" preservation lemma
   should be a verified `proof fn` whose body uses the narrow
   `external_body` axioms plus reveals + helper lemmas.

VeriFlat's `spec_util.rs` follows this discipline: 4 narrow trusted set-fold
axioms (one per page-size pointwise eq + one change-one for 4k) plus 2
verified preservation lemmas (`lemma_container_process_allocator_quota_wf_preserved_for_*`)
that build on them.

## Failure strategies

### Assertion failures

1. If conjunction (`A && B && C`), split into separate asserts. Reveal
   relevant opaque specs per conjunct.
2. Find any vstd lemma with `mcp_verus_mcp_server_search_vstd_lemmas` —
   broadcast use the individual lemma, not a broad group.
3. If no lemma helps, try method lemmas directly (e.g.,
   `seq.lemma_seq_skip_skip(i as int)`).
4. Use `assert(...) by { ... }` and `#[trigger]` annotations.

### Loop invariant failures

At the failure point, add an `assert` restating the invariant. Converts
to an assertion failure — apply the assertion strategy.

### Precondition failures

Run with `--expand-errors` to identify which `requires` clause failed.
Add an `assert` for it before the call site.

For VeriFlat, the most common `requires` failures are:

- Missing `reveal(opaque_spec)` at the call site.
- Wrong phase of `LocalContext` (`Acquire` vs `Release`).
- Wrong lock-id ordering (`lock_id_acyclic` not satisfied).

### Postcondition failures

Run with `--expand-errors`. Use `assume(false)` on different exit paths
to isolate the failing one. At the failing exit, assert the ensures
clause.

### Bidirectional invariants are the hard case

A bidirectional relation (e.g. `container_cpu_wf`: container→cpu AND
cpu→container) is hard to re-establish through an abstraction boundary.
The reverse direction's `forall` may refuse to fire even with the
trigger term present and the spec revealed.

If you hit this, prefer keeping the re-establishment in the SAME context
as the fresh lock-operation ensures (an inline proof) rather than
abstracting it into a lemma with view/element-equality preconditions.
Then tame the resulting query-size with helper lemmas for the OTHER,
non-bidirectional conjuncts (which factor cleanly).

## Threading tracked state through helpers

A by-value `tracked mut x: Tracked<T>` parameter does NOT export its
final value: `old(x)` is rejected, and `ensures x@ ...` refers to the
ENTRY value. Asserts inside the body can pass while the identical
postcondition fails — the tell-tale sign.

Fix: thread tracked state as `Tracked(x): Tracked<&mut T>` (destructured
param). Then in `ensures` use `final(x)` for post-state (and `old(x)`
for pre). Inside the body call methods directly on `x` (it's `&mut T`).

Call sites:
- Caller holds `Tracked<T>` by value: pass `Tracked(caller.borrow_mut())`.
- Caller already has `&mut T` (received as `Tracked(x): Tracked<&mut T>`):
  pass `Tracked(&mut *x)`.

You CANNOT reassign a `tracked` place in exec context (`steps =
self.helper(...)` errors). Use `&mut` threading.

`&mut self`'s post-state is `final(self)` (works in both exec and proof
fns). For `Tracked(g): Tracked<&mut U>`, post is `final(g)`. For
`Tracked(g): Tracked<&mut int>`, it's `*final(g)`.

## Closed-spec opacity across modules

A `closed spec fn` body is invisible OUTSIDE its defining module, even
via another closed spec. Example: `LockedArray::inv()` (= `array.wf()` =
`seq.len() == N`) and `LockedArray::view()` are both closed, so
`view().len() == N` is NOT derivable in client code from `inv()`.

Fix: add an ADDITIVE helper in the defining module:

```rust
pub proof fn lemma_view_len(&self)
    requires self.inv()
    ensures self.view().len() == N
{}
```

This changes no existing spec, is sound, and gives clients the missing
fact.

## Stale files (do NOT spend time fixing)

These exist on disk but are NOT in the module tree, so verification
errors there are inert:

- `src/kernel/cpu_tlb.rs` (active version is in `kernel/cpu_tlb_management/`).
- `src/kernel/memory_management/pagetable_tlb_spec.rs` (entirely
  commented out).
- `src/allocator/spec_define.rs` (entirely commented out).

## Reveal scoping (a recurring foot-gun)

`reveal(foo)` is lexically scoped to the enclosing proof block. It does
NOT propagate into nested `assert ... by { }` or `assert forall ... by
{ }` sub-blocks. Re-issue `reveal(foo)` inside each nested `by` block
that needs it.

## Linearization model — quick reference

The model has TWO atomicity levels:
- **Kernel-view** (`kernel_view_locking_state`): Acquire/Release per atomic
  section. Acquire = locks may be taken. Release = no more lock acquires;
  only releases. Flipped by `begin_user_view_step`.
- **User-view** (`user_view_locking_state`): Acquire/Release per syscall.
  Same shape. Flipped both directions by begin/end_user_view_step.
- `kernel_step_boundary`: ends a kernel section, lets concurrent threads
  run, starts a new section. Held objects pinned across boundary; unheld
  objects can change arbitrarily.

The `KernelSteps` ledger tracks user-view atomic transitions, with a
`snap_shot: KernelU` field that catches U-mutations not bracketed by
`begin/end_user_view_step`. See `veriflat-project-notes.md` for the
operational details.

## Project resources

- `Methodology.md` (project root) — conceptual model.
- `LockId.md` — lock ordering scheme.
- `SystemCalls.md` — syscall lock-acquire orders.
- `README.md` — high-level overview.
- `.kiro/steering/veriflat-project-notes.md` — operational notes (module
  layout, RwLock generics, conventions, KernelSteps discipline, current
  state of syscalls).
- vstd library: `mcp_verus_mcp_server_search_vstd_lemmas` for seq/map/set
  lemmas.
- Verus guide: `mcp_verus_mcp_server_read_verus_guide` for triggers,
  quantifiers, etc.

## MCP tools (when available)

The `verus-mcp-server` tools (`verify_and_diagnose`, `verify_all`,
`search_vstd_lemmas`, `read_verus_guide`) provide structured output and
automated proof advice. They run on macOS via `./verus.sh`.

When MCP tools are unavailable (on this machine they sometimes fail with
`./verus.sh: No such file or directory`), drive Verus directly with
`./verify.sh`.
