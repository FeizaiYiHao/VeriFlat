---
name: project_boundary_forall_grouping
description: "kernel_step_boundary ensures grouped into 9 categorized open spec fns with aggressive triggers for auto-instantiation"
metadata: 
  node_type: memory
  type: project
  originSessionId: current
---

## Structure

`kernel_step_boundary` ensures uses 9 open spec fns (in `kernel_k_define_spec.rs`):

| spec fn | content |
|---------|---------|
| `boundary_containers_preserved` | rodata + held-object |
| `boundary_processes_preserved` | rodata + held-object |
| `boundary_threads_preserved` | held-object |
| `boundary_endpoints_preserved` | held-object |
| `boundary_schedulers_preserved` | held-object |
| `boundary_pagetables_preserved` | held-object |
| `boundary_pages_preserved` | held-object |
| `boundary_cpus_preserved` | held-object |
| `boundary_allocators_preserved` | quota + pool + cache (per-size split) |

Each takes `(pre: &KernelK, post: &KernelK, lctx: &LocalContext)`.

## Trigger Design

Held-object foralls use **disjunctive antecedent** + **multi-path triggers**:

```rust
forall|s: RwLockSchedulerPtr|
    #![trigger lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))]  // lock_map path
    #![trigger pre.scheduler_map.spec_index(s).locked_by(lctx)]            // locked_by path
    #![trigger pre.scheduler_map.dom().contains(s)]                        // dom path (pre)
    #![trigger post.scheduler_map.dom().contains(s)]                       // dom path (post)
    #![trigger post.scheduler_map.spec_index(s)]                           // AGGRESSIVE (post)
    (lctx.lock_map().dom().contains(KernelObjId::Scheduler(s))
        || (pre.scheduler_map.dom().contains(s) && pre.scheduler_map.spec_index(s).locked_by(lctx)))
    ==> post.scheduler_map.dom().contains(s) && post.scheduler_map[s] == pre.scheduler_map[s]
```

**Key principles:**
- Antecedent uses `||` (disjunction): lock_map membership OR (dom + locked_by)
- Triggers cover BOTH pre-side and post-side terms
- Aggressive post-state trigger (`post.X_map.spec_index(x)`) ensures caller
  auto-instantiates after boundary call (caller always has post-state in scope)
- Allocator foralls split by size (SZ4k/SZ2m/SZ1g) for locked_by triggers
  (sz variable prevents single generic locked_by trigger)

## Boundary Ensures Core Guarantees

```
final(self).inv()
final(lctx).lock_map() == old(lctx).lock_map()          // lock_map fully preserved
final(self).locked_objects_match_lctx(final(lctx))      // match_lctx re-established
final(self).root_container == old(self).root_container   // rodata scalars
final(self).default_pagetable == old(self).default_pagetable
boundary_X_preserved(old(self), final(self), old(lctx))  // per-subsystem
```

## What Boundary Does NOT Guarantee

- `scheduler_map.dom() == old` — other threads can create/delete unlocked schedulers
- `container_map.dom() == old` — same for containers
- Only **locked** objects are preserved (via held-object foralls)
- Unlocked objects may change arbitrarily (interleaving semantics)
