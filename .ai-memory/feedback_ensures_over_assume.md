---
name: feedback_ensures_over_assume
description: "When a fact is lost across &mut borrows / helper calls, strengthen the callee's ensures — don't assume() it"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

When a manifestly-true fact fails to verify because it was **lost across a `&mut`
borrow or a helper call** (e.g. `perm.thread_id() == lctx.thread_id()`,
`obj.wlocked_by(lctx)`, a held object surviving an internal `kernel_step_boundary`),
the fix is to **add the fact to the callee's `ensures`**, NOT to `assume()` it in
the caller. The callee already maintains the fact; state it so it crosses the
borrow.

**Why:** an `assume()` left in a green proof reads as embarrassing (the user's word)
and is a soundness hole. Verus loses tracked-value facts (perm fields, lock state)
across `&mut LocalContext` / `&mut self` boundaries because the callee's contract
didn't carry them forward — the honest, sound fix is a contract completion.

**How to apply (the recipe that took `add_new_thread` from 16 assumes → 0):**
1. Identify which callee's `&mut` borrow drops the fact (`allocate_free_4k_page`,
   `create_thread_from_staged_page`, a `wunlock_*`).
2. Add the fact to THAT function's `ensures`. It's almost always free to prove
   there because the function genuinely maintains it (never writes the field).
   Concretely landed: alloc gained `final(lctx).thread_id() == old`, held-process
   `being_killed`/`view_rodata`/perm-match, held-scheduler + held-cpu survival
   foralls; `create_thread` gained `locked_objects_match_lctx(final)`,
   `cpu_array == old`, `lock_map == old.insert(Thread(page_ptr))`,
   `ret.1.thread_id() == final(lctx).thread_id()`.
3. Re-verify: the caller's obligation now closes from the strengthened ensures.

**When a real inline proof is genuinely too tedious** (multi-boundary lock_map-key
bookkeeping through a removal loop): a NARROW `#[verifier::external_body]` stub
lemma with a precise `//@Xiangdong PENDING PROOF` note is the accepted fallback
(the user blessed this pattern for the `len ≤ NUM_PAGES` bounds and the
`lemma_alloc_preserves_held_{scheduler,cpu}` framing lemmas). A named, localized
stub lemma is FINE; a bare `assume()` buried in a function body is NOT. See
[[feedback_proof_gaps]] — flag before inventing an axiom, but a stub matching an
already-blessed pattern is in-bounds.

See [[project_thread_wiring_milestone]] for the full worked example.
