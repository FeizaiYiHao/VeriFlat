---
name: feedback_cost_wall_is_usually_a_bug
description: "A postcondition that \"won't close at any rlimit\" is usually an un-fired trigger, not a size limit — assert the trigger term first"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

A proof obligation that fails **even at rlimit(300M)/200s+** is almost never a
genuine "function too large" cost wall — it is usually a **postcondition whose
trigger never fired**, so the solver flails on an un-instantiated goal.

**Diagnosis proven twice this session:**
1. `allocate_free_4k_page` Option-B (page returned write-locked): the
   `lock_map`-membership ensures failed at 300M rlimit. The fix was ONE line per
   path: `assert(lctx.lock_map().dom().contains(KernelObjId::Page(page_index)))`
   before each `kernel_step_boundary`, so the boundary's held-page framing forall
   (`forall|i| lock_map.dom().contains(Page(i)) ==> final.page_array[i]@ == old...`)
   instantiates at `i = page_index`. rlimit collapsed **272M → 5.27M** (the 71M
   flailing I first saw was the solver thrashing on the un-triggered postconditions).
2. Earlier: a redundant `assert(forall|k| P(k)) by { assert forall|k| P(k) by{} }`
   (outer conclusion == inner conclusion) was pure E-matching pollution over the
   whole nested proof — collapsing to just the inner forall cut alloc rlimit
   **272M → 133M (−51%)**.

**Rule:** before concluding "needs decomposition" or "needs a higher rlimit budget"
or "needs spinoff_prover", check whether the failing quantified postcondition has
its **trigger term asserted in scope**. Assert the membership / trigger term the
forall keys on, right before the obligation. This is the same lever as the
reveal-scoping rule in verus-style.md. "Fix the trigger, not the budget" —
mirrors [[project_alloc_free_4k_postconditions]]'s "cost wall was a proof-gap
mirage". Also: `assert(forall|k| P(k)) by { assert forall|k| P(k) by {...} }` where
outer==inner is NEVER proof content — grep for and delete that shape.
