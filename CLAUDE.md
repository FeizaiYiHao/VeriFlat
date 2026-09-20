# VeriFlat

@AGENTS.md

`AGENTS.md` is the repository-wide authority. Live code wins over every note.
Do not maintain a separate proof, lock-model, or verification policy here.

Before acting, read the matching canonical skill:

- Verus proof work: `.codex/skills/veriflat-proof/SKILL.md`
- Locks, `LocalContext`, and syscall semantics:
  `.codex/skills/veriflat-kernel-model/SKILL.md`
- Build, measurement, style audit, and handoff:
  `.codex/skills/veriflat-build/SKILL.md`

Read only the references routed by the selected skill. Use `.ai-memory/MEMORY.md`
for durable design orientation when its topic matches the task, and re-check it
against live code.

During proof iteration use the focused split-workspace command described by the
build skill. Reserve the full workspace and monolithic verification for the
handoff stages required there.

After substantial `src/` edits verify the smallest relevant target, run the
session-scoped `/style-check`, and follow the build skill's final checks.
