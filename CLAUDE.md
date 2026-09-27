# VeriFlat

@AGENTS.md

`AGENTS.md` is the repository-wide authority. Live code wins over every note.
Do not maintain a separate proof, lock-model, or verification policy here.

`.claude/skills` links to the canonical `.codex/skills/`. Before acting, invoke
the matching skill (`$name` in `AGENTS.md` means the same skill):

- Verus proof work: `veriflat-proof`
- Locks, `LocalContext`, and syscall semantics: `veriflat-kernel-model`
- Build, measurement, style audit, and handoff: `veriflat-build`

Read only the references routed by the selected skill. Use `.ai-memory/MEMORY.md`
for durable design orientation when its topic matches the task, and re-check it
against live code.

During proof iteration use the focused split-workspace command described by the
build skill. Reserve the full workspace and monolithic verification for the
handoff stages required there.

After substantial `src/` edits verify the smallest relevant target and follow
the build skill's final checks. The shared `.codex/hooks/style_gate.py` Stop
hook requires a final style pass over every `src/**/*.rs` file this session
changed; finish again without edits once that pass is clean.
