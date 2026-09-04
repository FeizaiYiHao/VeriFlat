---
name: veriflat-kernel-model
description: Apply VeriFlat's current lock, LocalContext, mmap_4k, IPC, and syscall semantics when editing or reviewing those kernel paths. Do not use for unrelated repository work.
---

# VeriFlat kernel model

Use the live code as the semantic authority. Do not invent preconditions,
runtime checks, representations, or framing bridges when a proof exposes an
unclear invariant; report the mismatch first.

## References

- For locks, held objects, `LocalContext`, dynamic lock ids, or kernel-step
  framing, read [references/lock-model.md](references/lock-model.md).
- For `mmap_4k`, IPC queues, Pages rendezvous, or related syscall behavior,
  read [references/syscall-semantics.md](references/syscall-semantics.md).

Read only the references relevant to the current task. If both areas interact,
read both before changing their shared boundary.
