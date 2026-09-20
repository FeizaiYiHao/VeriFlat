---
name: veriflat-proof
description: Edit, debug, review, and optimize VeriFlat Verus spec, proof, and exec code while preserving its trigger, reveal, framing, and canonical-style rules.
---

# VeriFlat proof work

Use direct operation facts and preserve the model's existing semantics. Do not
hide a difficult callsite inside a new operation-specific helper.

For invariant checks, first try automatic closure without local scaffolding,
then follow the ordered workflow in `references/proof-debugging.md`.

## References

- Before editing, reviewing, or diagnosing Verus spec, proof, or exec code, read
  [references/style-and-discipline.md](references/style-and-discipline.md).
- When diagnosing a verification failure, trigger issue, opaque predicate, or
  cumulative solver cost, also read
  [references/proof-debugging.md](references/proof-debugging.md).
- Only when a single equation exceeds 5 seconds SMT under `--time-expanded`,
  read [references/slow-equation.md](references/slow-equation.md). A single
  equation above 10 seconds must be simplified, context-isolated, or split
  before handoff even if a higher rlimit makes it verify.

For full EOF optimization, define one complete operation-state summary S for
all mutations and required preservation. The main exec equation establishes S
without closing any final post-state invariant, invariant group, or `*_wf` leaf.
Independently verified EOF functions outside the exec equation derive every
final invariant solely from entry invariants, S, and narrow representation
facts already produced by executed callees. Moving or merging inline assertions,
or summarizing only one invariant's dependencies, does not complete EOF.
For a long equation, introducing the operation-specific full-EOF boundary,
adding its independent closure functions, and changing S require no separate
user approval. S may be freely reshaped, including adding, removing,
strengthening, weakening, or reorganizing clauses. Keep S limited to complete
transition/framing facts: never put final invariants or `*_wf` closure in S,
change model semantics, or use this authorization for reusable cross-operation
framing abstractions.

Remove temporary diagnostics immediately. Once verification is green, minimize
added proof scaffolding one item at a time and retain only fail-on-delete proof.
