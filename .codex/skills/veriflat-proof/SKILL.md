---
name: veriflat-proof
description: Edit, debug, review, and optimize VeriFlat Verus spec, proof, and exec code while preserving its trigger, reveal, framing, and canonical-style rules.
---

# VeriFlat proof work

Use direct operation facts and preserve the model's existing semantics. Do not
hide a difficult callsite inside a new operation-specific helper.

## References

- Before editing, reviewing, or diagnosing Verus spec, proof, or exec code, read
  [references/style-and-discipline.md](references/style-and-discipline.md).
- When diagnosing a verification failure, trigger issue, opaque predicate, or
  cumulative solver cost, also read
  [references/proof-debugging.md](references/proof-debugging.md).
- Only when a single equation exceeds 5 seconds SMT under `--time-expanded`,
  read [references/slow-equation.md](references/slow-equation.md).

For full EOF optimization, move the entire invariant-closing tail behind an
explicit transition summary into independently verified proof functions. Merging
inline assertions does not isolate solver context and does not complete EOF.

Remove temporary diagnostics immediately. Once verification is green, minimize
added proof scaffolding one item at a time and retain only fail-on-delete proof.
