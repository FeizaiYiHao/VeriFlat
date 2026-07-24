---
name: user_xiangdong
description: Who Xiangdong is and how he wants the VeriFlat verification work done
metadata: 
  node_type: memory
  type: user
  originSessionId: 11731d4e-6c71-43b7-b3d9-440871f93b17
---

Xiangdong owns VeriFlat (Verus-verified microkernel). He is the verification
architect — he makes the spec/invariant/TCB/lock-hierarchy calls; the agent
executes proofs and flags decisions.

**How he works:**
- **One narrow deliverable at a time** — a single wrapper, lemma, or wiring step.
  Don't sprawl. He builds the working knowledge incrementally.
- **Corrects fast and expects the agent to internalize it.** He caught: a wrong
  lock-ordering claim ("we never lock the thread — it's a MINT"), the "16 assumes
  — a little embarrassing" (→ discharge them, don't leave them), and an inflated
  token estimate (→ he expects numbers to be double-checked, not hand-waved).
- **Blesses specific escape hatches explicitly, then expects them reused, not
  re-litigated:** narrow `#[verifier::external_body]` stub lemmas with
  `//@Xiangdong PENDING PROOF` notes ("introduce the lemmas, don't prove for now"),
  TCB-contract strengthening ("you can narrow the TCB"), invariant facts he states
  ("rodata never changes between concurrent steps"). See [[feedback_ensures_over_assume]].
- **Decisions are HIS:** invariant/trigger changes ([[feedback_ask_before_invariant_triggers]]),
  `#[verifier::spinoff_prover]` ([[feedback_no_self_added_spinoff_prover]]),
  lock-hierarchy/major assignments, linearization model. When blocked on one of
  these, present options crisply (AskUserQuestion) and act on his pick.
- **Values honesty over polish:** report failing obligations with the real output,
  say what's stubbed, don't claim done when it's assumed. A green proof resting on
  hidden `assume()`s is worse than an honest partial.

**Style:** terse, direct questions ("but 16 assumes?", "are you sure
about X?"). Wants the substantive answer + a recommendation, not a survey. He
reads the code and the numbers himself, so be precise and verifiable.

**Cadence tell:** heavy Claude Code user running LONG single conversations (this
one spanned ~3 weeks / 21k turns). Cost is dominated by cache-reads from the
long-lived context — worth suggesting fresh sessions / earlier compaction for
independent tasks.
