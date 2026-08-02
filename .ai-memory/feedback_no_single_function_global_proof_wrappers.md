---
name: feedback_no_single_function_global_proof_wrappers
description: Never replace one implementation's complete local proof with a global wrapper lemma used only by that function
metadata:
  node_type: memory
  type: feedback
  originSessionId: current
---

Do not create a global proof lemma whose purpose is to make implementation
callsites look like:

```rust
assert(self.inv()) by {
    lemma_no_change_imply_kernel_inv_for_this_function_forall();
};
```

This prohibition also covers a lemma shared by a lock/unlock pair or several
closely related wrappers if it packages the complete `KernelK::inv()`, a whole
subsystem invariant, or all of their conjunct proofs. Examples that must not
exist are `kernel_inv_preserved_for_process_lock_op` and
`memory_management_inv_preserved_for_page_lock_op`.

If the lemma merely moves invariant re-establishment or a reveal sequence into
a global body, it has not improved automation. It has hidden the difficult
proof, polluted the global proof API, and made the real dependency harder to
inspect. Keep such proof at each implementation callsite.

A global lemma is appropriate only when it states one genuinely reusable
field-framing, individual-invariant, or mathematical fact consumed by multiple
implementations, or when it handles an unavoidable Verus limitation such as a
fold/quantified fact. Existing reusable `*_preserves_invariant_fields` and
single-invariant no-change lemmas are fine; a whole-kernel or whole-subsystem
wrapper around them is not.

Before adding a global lemma, inspect its consumers. If it is tailored to one
implementation and would have only that consumer, prove the goal in place
unless Xiangdong explicitly asks for the global abstraction.
