---
name: feedback_lemma_scoping
description: When scoping a lemma call into an assert-by helps rlimit vs when it hurts
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

A bare `lemma(...)` at `proof {}`/function scope pollutes the SMT context like a
bare `reveal` — but ONLY as strongly as its `ensures` shape (a non-`external_body`
proof fn contributes only its ensures to the caller; the body is checked
separately). So scoping payoff depends on the ensures:

- **`forall`-quantified ensures** (the `_forall`-suffixed lemmas) = a genuine
  reveal-like E-matching rule spanning the whole function → scoping into the
  consuming `assert(<goal>) by { lemma(...); }` is a real win. (In
  allocate_free_4k_page these were ALREADY all scoped.)
- **Ground-equality ensures** (e.g. `kernel_no_change_to_user_view_fields_imply_kernel_u_eq`
  → `kernel_k_to_kernel_u(*pre)==kernel_k_to_kernel_u(*post)`) = minimal pollution.

**Why:** How you scope a ground-fact lemma matters and can BACKFIRE:
- Merging it into an ALREADY-EXISTING consumer assert (no new goal) can win — e.g.
  folding `lemma_scan_fail_pool_nonempty` into the existing `...pool...len()>0 by {}`
  saved −72,660 rlimit on `allocate_free_4k_page`.
- Wrapping it in a BRAND-NEW `assert(<the ground eq>) by { lemma(); }` LOSES —
  the new assertion is itself a separate proof goal whose cost exceeds the
  pollution removed. Tested on the fast-path `kernel_no_change` pair: **+151,589**
  rlimit (worse). Reverted.

**Rule:** scope a lemma into a consumer that ALREADY EXISTS; never invent a new
`assert by` just to hold a ground-fact lemma. And a function-scope `reveal` that
feeds exec-call preconditions across the fn (e.g. `reveal(allocator_perms_wf)` at
the top of `allocate_free_4k_page`) is load-bearing — delete-and-reverify fails
2 preconditions — leave it. See [[project_alloc_free_4k_rlimit_drivers]] for what
actually dominates (deep quantifiers + Set fold axioms, not ground lemmas).
