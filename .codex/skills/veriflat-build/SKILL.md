---
name: veriflat-build
description: Preserve VeriFlat's split-crate architecture and run its Cargo-Verus verification, performance measurement, style audit, and handoff workflow.
---

# VeriFlat build and verification

Use the same live sources for the monolith and split workspace. Preserve the
user's dirty worktree and do not clean, reset, overwrite, or restage unrelated
changes.

## References

- For crate dependencies, module ownership, public cross-crate items, or build
  structure, read [references/architecture.md](references/architecture.md).
- Before running verification, changing verification arguments, measuring
  performance, or handing off code, read
  [references/verification.md](references/verification.md).

Report every verification run number and distinguish cached, hot, and cold
results accurately.
