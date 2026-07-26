---
name: feedback_proof_simplification_methodology
description: "Systematic approach to eliminating redundant proof code: trigger-first diagnosis, delete-and-verify, minimal irreducible core"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: current
---

## Proof Simplification Hierarchy

When simplifying Verus proof code, apply in this order:

### 1. Fix triggers FIRST (eliminates entire assert forall blocks)

Most bridging `assert forall ... by { reveal(...) }` exist because a callee's
postcondition forall trigger didn't fire. Fix the trigger on the CALLEE, then
delete the bridging assert on the CALLER.

**Diagnostic:** if removing a bridging assert breaks verification, check whether
the callee's postcondition forall has an aggressive post-state trigger. If not,
add one (exec fn triggers are free to modify — small blast radius).

### 2. Delete debugging asserts (STEP1/STEP2/... comments are tells)

Any assert with a comment like `// STEP1: after wlock_all` or `// after scan`
is a debugging aid. Delete and verify. These are never proof content.

### 3. Delete framing asserts that ensures already provide

`assert(self.cpu_array == old(self).cpu_array)` after a function call is redundant
if the called function's ensures already frames cpu_array. Delete and verify.

### 4. Merge duplicate asserts

Two `assert forall|c: CpuId|` with the same antecedent but different consequents
(dom-only + value) → merge into one with combined consequent.

### 5. Remove duplicate Page/Process lock_id asserts

Same assert appearing twice in one proof block → delete the second occurrence.

## What Is Irreducible

After all the above, the remaining proof code is minimal:

- **Pre-boundary scoped reveals** (`assert(X) by { reveal(P) }`): opaque predicate
  cost. Provides ground facts for boundary's held-object forall triggers.
- **wunlock precondition asserts** (cache perms forall): exec call precondition
  that requires explicit perm facts not derivable from inv().
- **kernel_u_eq proof**: postcondition requires, uses ghost captures legitimately.
- **Lock ordering asserts** (spec_gt, lock_id comparisons): exec call preconditions
  for wlock that require arithmetic reasoning.

## Anti-Patterns to Grep For

```bash
# Debugging asserts (always removable)
grep -n "// STEP\|// after\|// Post-" src/kernel/implementation/*.rs

# Duplicate asserts (same line appearing twice in a proof block)
# Framing asserts after calls (redundant with ensures)
grep -n "assert(self\.\w* == old(self)\.\w*)" src/kernel/implementation/*.rs

# Bridging assert foralls (fix trigger on callee, then delete)
grep -n "assert forall.*by {" src/kernel/implementation/*.rs
```

## Session Results (allocate_free_4k_page.rs)

| Category | Lines removed |
|----------|--------------|
| Scheduler bridging assert forall × 4 paths | -32 |
| Cpu bridging assert forall × 4 paths | -32 |
| Post-boundary lock_map value asserts | -16 |
| Post-boundary framing asserts | -8 |
| STEP debugging asserts | -4 |
| Duplicate asserts | -6 |
| **Total** | **~98 lines** |

All enabled by adding 2 aggressive triggers to boundary spec fns.
