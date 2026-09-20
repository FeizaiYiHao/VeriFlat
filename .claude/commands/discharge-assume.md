---
description: Replace a VeriFlat proof assumption with a real, minimal proof
---

Read `AGENTS.md`, `.codex/skills/veriflat-proof/SKILL.md`, its routed
`references/style-and-discipline.md` and `references/proof-debugging.md`, plus
the verification procedure routed by `.codex/skills/veriflat-build/SKILL.md`.

Use `$ARGUMENTS` to select one function and one assumption. Work on only that
obligation:

1. Reproduce it with the smallest focused verification command.
2. Isolate the proof and split the target until the first missing term or
   `recommends` obligation is visible.
3. Check the producer contract and trigger chain, then existing generic lemmas
   and the smallest scoped reveal set.
4. Use analogous live proofs as evidence, not as recipes to transplant
   wholesale.
5. Remove the assumption and retain only fail-on-delete proof.

Do not add another assumption, hidden witness, model change, common trigger
change, or framing helper unless `AGENTS.md` permits it and any required user
decision has been obtained. Restore all diagnostic cutoffs, run the focused
verification, and report its run number and proof-performance result.
