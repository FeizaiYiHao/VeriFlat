---
description: Minimize a VeriFlat proof and repair its actual trigger or producer gap
---

Read `AGENTS.md`, `.codex/skills/veriflat-proof/SKILL.md`, its routed
`references/style-and-discipline.md` and `references/proof-debugging.md`, plus
the verification procedure routed by `.codex/skills/veriflat-build/SKILL.md`.

Use `$ARGUMENTS` to select one function or proof. First try automatic closure.
If it fails or reaches rlimit, isolate that proof, split its conjunctions into
temporary assertions, and let Verus expose the first failed term and any unmet
`recommends`.

Then inspect the producer contract and trigger lookup chain before testing an
existing lemma or minimal scoped reveal. Delete assertions, reveals, lemma
calls, and ghosts one at a time and reverify after each deletion. Do not retain
call-site `assert forall`, broad reveal fans, indirect framing helpers, hidden
witnesses, or facts that do not fail on deletion.

Restore every diagnostic cutoff and report the focused run numbers, retained
proof, removed scaffolding, and any unresolved model or trigger decision.
