# VeriFlat project adapter

`AGENTS.md` is authoritative. Live code and contracts are the semantic source
of truth.

Do not duplicate architecture, lock, syscall, or proof rules in Kiro steering.
Read the matching canonical source instead:

- `.codex/skills/veriflat-kernel-model/SKILL.md` for current kernel semantics;
- `.codex/skills/veriflat-proof/SKILL.md` for Verus proof work;
- `.codex/skills/veriflat-build/SKILL.md` for repository architecture and
  verification;
- `.ai-memory/MEMORY.md` for routed durable design orientation.

Read only the references selected by the matching skill and validate notes
against live code before making a design decision.
