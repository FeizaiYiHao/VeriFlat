---
name: feedback-proof-gaps
description: Always notify the user when a proof gap or spec gap is discovered rather than silently working around it
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 50f47949-7957-453d-9a5a-892d4a7e7c9c
---

When a proof gap or spec gap is discovered (e.g., a missing postcondition in a trusted spec like `wlock_ensures`/`wunlock_ensures`, or a lemma that must remain `external_body` due to Verus limitations like `Map::new` extensional equality), always flag it to the user before working around it.

**Why:** The user is the domain expert on what should be provable vs. what is a genuine Verus limitation. They may be able to fix the underlying spec (as happened with `being_killed()` preservation in `wlock_ensures`/`wunlock_ensures`) rather than accepting an `external_body` workaround.

**How to apply:** Before adding any `#[verifier::external_body]` axiom or `assume`-style workaround, explain to the user: (1) what property can't be proved, (2) whether it's a spec gap (fixable by strengthening postconditions) or a Verus limitation (e.g., extensional equality on `Map::new`/`Seq::new`), and (3) what the narrow TCB axiom would look like if they choose to accept it.
