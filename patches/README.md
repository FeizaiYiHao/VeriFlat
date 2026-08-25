# Local Verus patches

## `verus-pipelined-smt.patch`

This patch contains the local Cargo-Verus/Verus experiment that starts the
erasure compile after Rust/VIR generation, before SMT verification finishes.
It is opt-in through `VERUS_PIPELINE_SMT=1`; the ordinary Verus path is
unchanged when the variable is absent.

The patch was generated against Verus commit:

```text
a8751f2b81578a762b42d1fc5a96653601e7363c
```

SHA-256:

```text
d1a71b54c722b3a2bde166b744b4396e2380a8da5ed75d16cb6354f743d95269
```

### Apply

Run these commands from the VeriFlat repository root. The first two commands
make sure the submodule is at the expected base and has no local edits; do not
apply the patch over a dirty Verus tree.

```bash
git -C verus rev-parse HEAD
git -C verus status --short
git -C verus apply --check ../patches/verus-pipelined-smt.patch
git -C verus apply ../patches/verus-pipelined-smt.patch
```

The first command must print the commit above, and the second must print
nothing.

### Rebuild Verus

```bash
cd verus/source
source ../tools/activate
vargo build --release
cd ../..
```

The patched pipeline is enabled only for the Cargo-Verus `verify` subcommand:

```bash
VERUS_PIPELINE_SMT=1 \
  verus/source/target-verus/release/cargo-verus verify <cargo-verus arguments>
```

`verify-workspace.sh` currently invokes Cargo-Verus `focus`, so setting the
variable on that wrapper does not enable this experiment.

### Verify the VeriFlat multi-crate workspace

Run the pipelined performance/reference verification from the VeriFlat root:

```bash
VERUS_PIPELINE_SMT=1 \
  verus/source/target-verus/release/cargo-verus verify \
    --workspace --exclude VeriFlat -- --num-threads 32 --time
```

On the 32-logical-CPU reference machine, keep Cargo's default concurrency.
Measured alternatives `-j 4` with 8 Verus threads and `-j 2` with 16 Verus
threads were slower.  `verify-workspace.sh` remains the focused/workspace
correctness wrapper; it does not measure this patch.

Always state the cache scope with a performance result:

- **Cold vstd and cold VeriFlat crates.**  With the target already containing
  ordinary Rust dependencies, run `cargo clean -p vstd`, then run the command
  above. Cargo invalidates vstd and its VeriFlat dependents. The pipelined
  workspace command uses the ordinary `target` directory; `target/verus-partial`
  belongs to the focused verification path and must not be used for this clean.
- **Hot vstd and cold VeriFlat crates.**  First run the pipelined workspace
  command once so Cargo populates vstd in this exact workspace dependency
  context.  Then preserve vstd while removing the seven VeriFlat packages:

  ```bash
  cargo clean -p veriflat_kernel_core \
    -p veriflat_alloc_page \
    -p veriflat_map_4k \
    -p veriflat_syscall_alloc_quota \
    -p veriflat_syscall_ipc \
    -p veriflat_syscall_new_thread \
    -p veriflat_syscall_mmap_4k
  ```

  Run the pipelined command above.  Do not prewarm vstd through its standalone
  manifest: its Cargo feature/fingerprint context can differ, causing the
  VeriFlat workspace to rebuild vstd.
- **Fully hot.**  An immediate repeat may be a Cargo no-op.  Report it only as
  a cache check, never as a full verification benchmark.

The 2026-08-22 measurements of 27.01 seconds and 15.15 seconds used
`target/verus-partial` for the package clean. They are not cold-pipeline
baselines because the pipeline fingerprints and artifacts remained in ordinary
`target`; the 15.15-second case was reproduced with only five downstream crates
being rebuilt. After merging the model into kernel-core on 2026-08-24, hot
vstd plus all
seven cold VeriFlat crates took 21.80 and 21.62 seconds of external wall time
(21.65 and 21.22 seconds reported by Cargo; 21.71-second external median).
The final retained-architecture acceptance runs took 20.86 seconds externally
(19.93 seconds reported by Cargo) with hot vstd, and 32.42 seconds externally
(31.50 seconds reported by Cargo) with cold vstd. An allocator-independent
mapping-core split was also tested but not retained:
default concurrency took 22.27 and 22.12 seconds, while Cargo -j 2 with 16
Verus threads took 28.67 seconds. Treat these as calibration points, not a
permanent acceptance threshold, and compare only like-for-like cache scopes and
thread settings.

### Remove

If the Verus tree contains only this patch, remove it without resetting the
submodule:

```bash
git -C verus apply --reverse --check ../patches/verus-pipelined-smt.patch
git -C verus apply --reverse ../patches/verus-pipelined-smt.patch
```
