---
name: feedback_aggressive_trigger_eliminates_bridging
description: "Open spec fn foralls auto-trigger with aggressive post-state triggers (post.X_map.spec_index(x)), eliminating ALL bridging assert foralls"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: current
---

## Core Discovery

Bridging `assert forall ... by { reveal(...) }` blocks after boundary calls are
**trigger failures**, not logical gaps. Fix the trigger, delete the assert.

**Before (57 lines of bridging asserts across 4 paths):**
```rust
self.kernel_step_boundary(&mut *lctx, &mut *steps);
assert forall|s: RwLockSchedulerPtr| #![auto]
    old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))
    implies lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
        && ... by {
    reveal(KernelK::locked_objects_match_lctx);
    reveal(scheduler_locked_match_lctx);
};
// ... same for Cpu ...
```

**After (zero bridging asserts):**
```rust
self.kernel_step_boundary(&mut *lctx, &mut *steps);
// solver auto-instantiates boundary_schedulers_preserved / boundary_cpus_preserved
```

## The Fix: Aggressive Post-State Triggers

Open spec fn internal foralls need triggers that match terms the caller
**always has after the call**. Pre-state triggers (`lctx.lock_map().dom().contains(...)`)
fail because boundary's `old(lctx)` ≠ caller's `old(lctx)` (lock ops modify lctx
between caller entry and boundary call).

**Add post-state triggers:**
```rust
pub open spec fn boundary_schedulers_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
    forall|s: RwLockSchedulerPtr|
        #![trigger lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))]  // pre-side
        #![trigger pre.scheduler_map.spec_index(s).locked_by(lctx)]            // pre-side
        #![trigger pre.scheduler_map.dom().contains(s)]                        // pre-side
        #![trigger post.scheduler_map.dom().contains(s)]                       // post-side
        #![trigger post.scheduler_map.spec_index(s)]                           // AGGRESSIVE
        ...
}

pub open spec fn boundary_cpus_preserved(pre: &KernelK, post: &KernelK, lctx: &LocalContext) -> bool {
    forall|c: CpuId|
        #![trigger lctx.lock_map().dom().contains(KernelObjId::Cpu(c))]
        #![trigger pre.cpu_array[c]@.locked_by(lctx)]
        #![trigger post.cpu_array[c]@]                                         // AGGRESSIVE
        ...
}
```

**Why it works:** After boundary, the caller always has `self.scheduler_map.spec_index(s)`
and `self.cpu_array[c]@` in scope (from postcondition or inv()). The aggressive trigger
fires from these terms, instantiating the open spec fn's internal forall automatically.

## What CANNOT Be Eliminated

Pre-boundary scoped reveals are **minimal and load-bearing**:
```rust
assert(lctx.lock_map().dom().contains(KernelObjId::Process(process_ptr))) by {
    reveal(process_locked_match_lctx);
};
```
These provide ground facts for the boundary's held-object forall triggers.
They are NOT bridging asserts — they are scoped reveals exposing one fact from
an opaque predicate (`locked_objects_match_lctx`). This is the irreducible cost
of opaque predicates.

## Exec Function Postcondition Triggers

Exec function pre/post triggers only affect callers (small blast radius).
Feel free to add 4-way triggers:
```rust
forall|s: RwLockSchedulerPtr|
    #![trigger old(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
    #![trigger final(lctx).lock_map().dom().contains(KernelObjId::Scheduler(s))]
    #![trigger old(self).scheduler_map.spec_index(s).locked_by(old(lctx))]
    #![trigger final(self).scheduler_map.spec_index(s).locked_by(final(lctx))]
    ...
```
This ensures callers can instantiate from ANY direction (old/final × lock_map/locked_by).

## Diagnostic Rule

When you see a bridging `assert forall ... by { reveal(...) }` after a function call:
1. Check if the callee's postcondition forall has an aggressive post-state trigger
2. If not, ADD the trigger (exec fn triggers are free to modify)
3. Delete the bridging assert
4. Verify

If it still fails: the issue is likely multi-step lock_map chaining (solver can't
prove a key survived N lock ops). In that case, the pre-boundary scoped reveal is
the minimal fix.
