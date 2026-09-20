---
description: Measure which VeriFlat proof obligations dominate verification cost
---

Read `AGENTS.md`, `.codex/skills/veriflat-proof/SKILL.md`,
`references/proof-debugging.md`, and the measurement rules routed by
`.codex/skills/veriflat-build/SKILL.md`.

Use `$ARGUMENTS` to select one function. Freeze the source and establish a
focused baseline before changing proof shape. Profile one obligation at a time
by temporarily commenting an unrelated postcondition or proof block, preserving
all producer facts needed by the target. Do not use `assume` or `admit` as an
ablation. A higher rlimit may be used to expose the true cost of a capped
equation; record the old/new ceiling and restore a diagnostic-only change.

Use identical verifier arguments, threads, source, and cache scope. Record both
wall/SMT measurements and rlimit; neither alone establishes a repository-level
speedup. Any single equation above 10 seconds SMT must be simplified, isolated,
or split rather than accepted under a larger ceiling. Restore each diagnostic
variant byte-for-byte before testing the next.

Report every run number, the complete baseline/candidate measurements, observed
variation, and the obligations ranked by measured effect. Leave no profiling
comments, assumptions, logs, snapshots, or temporary rlimit changes.
