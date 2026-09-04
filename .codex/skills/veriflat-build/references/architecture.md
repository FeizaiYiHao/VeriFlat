# Architecture

- Preserve the monolithic `src/lib.rs` build and the split Cargo-Verus
  workspace over the same live sources.
- Dependency order is:
  `kernel_core -> alloc_page -> {new_thread, map_4k}`;
  `map_4k -> {mmap_4k, ipc}`; `kernel_core -> alloc_quota`.
  Syscall crates are terminal and never depend on another syscall crate.
- Kernel core owns shared definitions, invariants, lemmas, locks, primitives,
  and release/finish operations. Allocation, mapping, and syscalls stay in
  their dedicated crates.
- Use ordinary module resolution, private terminal dependency imports, and the
  `split-crates` feature. Do not add `#[path]` roots or Cargo/monolith source
  forks.
- Cross-crate needs make the original item public or convert the original
  method to a standalone function; do not invent bridge lemmas.
