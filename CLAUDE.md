# VeriFlat

A microkernel verified with Verus (everything under `src/` is Verus Rust).
Build/verify with `./verify.sh` from the project root.

## Steering docs (auto-loaded via the imports below)

These three files are the working knowledge base. They are imported here so a
fresh session loads them automatically:

- **veriflat-project-notes.md** — durable architecture, conventions, idioms,
  gotchas, and the reference syscall example. Stable; rarely edited.
- **verus-verification.md** — the transferable "how to verify" playbook
  (cost tactics, proof patterns, TCB axiom design, failure strategies).
- **current-work.md** — fast-moving state: current verified count, in-progress
  functions, pointers to history. Update this as work lands.

`.kiro/HISTORY.md` is deliberately NOT imported — it holds spec/proof history
(the "why" behind clauses) and is read on demand, not every session.

@.kiro/steering/veriflat-project-notes.md
@.kiro/steering/verus-verification.md
@.kiro/steering/current-work.md
