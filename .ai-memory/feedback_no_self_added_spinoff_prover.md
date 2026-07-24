---
name: feedback-no-self-added-spinoff-prover
description: Never add
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

Do NOT add `#[verifier::spinoff_prover]` to any new wrapper / helper / proof fn on
your own initiative. Whether a function is spun off to its own SMT context is
Xiangdong's decision, applied only when he directs it.

**Why:** Many existing wrappers carry `#[verifier::spinoff_prover]` because HE added
them — that is not a license to sprinkle it on new code. The old guide text said
"spinoff_prover on every wrapper/helper/proof fn"; that has been corrected in
`.kiro/steering/verus-style.md` and `.claude/commands/style-check.md` to
"do NOT add on your own." I had added it to a new framing lemma
(`per_container_process_tree_wf_preserved_for_tree_fields_eq`) and removed it on his
correction — the lemma verifies fine without it.

**How to apply:** Write new proof fns / wrappers WITHOUT the attribute. If one is slow
enough that you think it genuinely wants spinoff (or an rlimit bump), FLAG it and ask —
present the timing / rlimit evidence and let him decide. A self-added
`#[verifier::spinoff_prover]` is a style violation to raise, not a default; its ABSENCE
on a new fn is never a violation. Same ask-first reflex as
[[feedback-ask-before-invariant-triggers]].
