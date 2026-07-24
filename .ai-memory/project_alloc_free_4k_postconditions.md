---
name: project_alloc_free_4k_postconditions
description: "allocate_free_4k_page's functional postconditions are now proven; the scan_caches_and_alloc spec-gap fix + the cost-wall-was-a-mirage lesson"
metadata: 
  node_type: memory
  type: project
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

`allocate_free_4k_page` (in `kernel/implementation/allocate_free_4k_page.rs`) now
proves its FULL functional postconditions (previously commented as "clean fast
path" WIP): `inv()`, held-process dom+`wlocked_by(final(lctx))`, phase→Acquire,
user-view phase preserved, `locked_objects_match_lctx`, `steps` preserved,
`snap_shot` refreshed, `page_ptr_valid(ret)`. 14 verified, 0 errors; full crate 459.

**Two things were needed:**
1. **A spec-gap fix in `scan_caches_and_alloc`** (the real blocker, found via
   full-budget diagnostic): its success branch ensured page/cache lock state but
   said NOTHING about `final(self).process_map[process_ptr]`, so the held process's
   lock state was unconstrained after the scan → the `found` path couldn't prove
   `wlocked_by(final(lctx))`. Fix: forward the process-held facts from the internal
   `pop_stage_4k_page` call into scan's success ensures (dom-contains, `wlocked_by`,
   `being_killed()==false`, lock_id match). Sound + cheap (scan 288K rlimit) — NOT
   full byte-equality (pop stages a page into temp_alloc_cache, moving the payload
   view; only lock state is preserved).
2. **A dom-contains assert before each of the 4 return-path `kernel_step_boundary`
   calls**: `assert(lctx.lock_map().dom().contains(Process(process_ptr))) by {
   reveal(process_locked_match_lctx); }` — the premise the boundary's held-object-
   preservation quantifier needs to fire. All 4 delete-and-reverify load-bearing.

**KEY LESSON — a "cost wall" can be a proof-gap mirage.** Before the scan fix, the
fn blew past the 30M default rlimit and hit 54M in a 17-min run before finally
reporting `postcondition not satisfied`. That looked like a cost problem needing
spinoff/rlimit-bump/helper-refactor. It was NOT: the SMT solver was flailing trying
to prove an UNPROVABLE goal (the missing scan ensures). Once the genuine gap was
closed, the fn proves all postconditions at **3.63M rlimit** (vs 2.25M inv-only —
just +1.38M for all 8), well under the default ceiling. No spinoff, no rlimit bump,
no helper factoring needed. **Diagnostic order: when a green-with-weak-postconditions
fn explodes on adding postconditions, run it to completion at high rlimit and read
the actual error FIRST — a `postcondition not satisfied` hiding behind an rlimit
timeout means fix the gap, not the budget.** See [[project_alloc_free_4k_rlimit_drivers]].
