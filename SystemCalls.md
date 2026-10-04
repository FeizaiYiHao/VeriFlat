# System call step specification

This document defines each syscall as a sequence of transitions of the
user-visible kernel state machine `KernelU`. It is the target for the Verus
step specs (`*_step_pre`, `*_step`, `*_syscall_trace`) in the syscall
`*_spec.rs` files. The live code is authoritative for everything else. Each
section ends with the known differences between this target and the current
specs; remove a section's differences list once that syscall conforms.

## 1. Model

- `KernelU` is the projection of `KernelK` sampled at atomic-section
  boundaries. It shows object lock modes (`LockStateU::{Unlocked, ReadLocked,
  WriteLocked}`) on CPUs, containers, processes, threads, endpoints, and page
  tables, but not lock owners, reader counts, or allocator internals. The
  process PCID and the global `kernel_l4_end` are in U (§15).
- A `KernelStep` is `{ old_u, new_u }`. An atomic section whose U projection
  does not change records no step (it stutters). Every recorded step is one
  transition of the whole machine and may interleave with steps of other CPUs.
- A step fires only when its `*_step_pre(old_u, ...)` holds, and then
  `*_step(old_u, new_u, ...)` fixes `new_u`. Lock modes in U give mutual
  exclusion between CPUs: a step that acquires an object requires it to be
  unlocked, so a pagetable write-locked by one mmap blocks another CPU's mmap
  enter step on that pagetable.
- A thread's `syscall_progress` is `Some` exactly while its running syscall
  holds its write lock. It records the syscall's phase and is the holder
  credential for every step after the first.

Notation used below, for a state `u` and the step's `cpu_id`:

| Name | Definition |
|---|---|
| `cpu` | `u.cpu_array[cpu_id]` |
| `T`, `thr` | `cpu.current_thread->Some_0`, `u.thread_map[T]` |
| `P`, `C` | `thr.owning_proc`, `thr.owning_container` |
| `PT(p)` | `u.process_map[p].pagetable->Some_0` |
| `E(i)` | `thr.endpoint_descriptors[i]->Some_0` |
| `prog` | `thr.syscall_progress` |
| `UserVa(u, r)` | `user_va_range(u, r)`: `spec_v2l4index(r.start) >= u.kernel_l4_end` |
| `Unlocked(x)`, `W(x)` | `x.lock_state is Unlocked`, `x.lock_state is WriteLocked` |
| `CS(c)` | the CPU-set lock of container `c`: `Unlocked(CS(c))` is `u.container_map[c].cpu_set_lock is Unlocked` |

`Caller(u, cpu_id)` abbreviates `index_valid(NUM_CPUS, cpu_id)`,
`cpu.state is Running`, `cpu.current_thread is Some`, and `T`, `P`, `C` in
their maps' domains.

## 2. Rules for every step spec

**R1 Parameters.** A step spec takes only:

- `cpu_id`;
- the syscall's user arguments, on the first step of the syscall (for example
  `va`, `range`, `endpoint_index`, `regs`, an amount, or the IPC payload);
  later steps read them from `prog`;
- K-internal choices that U cannot determine, such as schedule's
  `flushed_pcid` and IPC's `flushed_default_pcid`.

A step spec never takes a thread, process, container, endpoint, or pagetable
pointer. Objects created by a step are named through `new_u` (for example the
last element of the parent's `children` or of a process's `owned_threads`).
When U determines a step's outcome (success or a particular error), the spec
computes it from `old_u` instead of taking it as a parameter.

**R2 Derivation.** Every object is reached from `cpu_id` through U: the
caller `T`, then `P`, `C`, `PT(P)`, `E(i)`, an endpoint queue head, a parent's
last child, or a pointer recorded in `prog`. Each derivation must stay valid
until the last step that uses it; the section states which held lock keeps it
stable. When no such chain exists, the pointer is recorded in `prog`.

**R3 First step.** Its pre contains:

- `Caller(u, cpu_id)` and `prog is None`;
- `Unlocked(x)` for every U-visible object `x` the step acquires (a read
  acquire would need only `!W(x)`);
- `!x.killed` for every object the implementation acquires with a
  `*_unless_killed` lock;
- every argument, quota, and state check the implementation performs before
  its first recorded step, stated over U.

A single-step syscall acquires and releases its locks inside the step, so its
pre also requires `Unlocked` for every U-visible object it locks.
alloc_quota_4k and schedule are not issued under a syscall progress: their
pres name `cpu.current_process` and `cpu.owning_container` directly instead of
`Caller` and `prog is None` (§3, §4).

**R4 Later steps.** Each pre contains:

- `prog` in the phase the step consumes;
- `W(x)` for every object the step reads, mutates, or releases under the
  caller's retained locks;
- `Unlocked(x)` for every U-visible object the step newly acquires;
- the phase condition (for example `mapped < len`).

**R5 Locks outside U.** Allocator quota/cache/pool, scheduler, PCID
allocator, PCID-needflush, and page locks are invisible in U. The U fields
they guard are container `quota_*` (allocator quota), container `scheduler`
(scheduler), container `free_pcids` (PCID allocator), and `cpu_tlb` (PCID
needflush). The CPU-set lock is visible as `ContainerU.cpu_set_lock` (`CS(c)`)
and guards the `owning_container` of the container's Off CPUs.

- A step may change such a field without a U-visible lock only when the
  change happens inside that one step. Its pre still states the field's
  precondition (for example a non-empty `free_pcids`).
- When a non-U lock stays held across steps, a U-visible lock that the caller
  holds over the same interval must also cover the guarded fields.
- Exception (approved 2026-09-30): new_process holds the PCID allocator of `C`
  from enter to publish with `C` unlocked (§9), so no U lock covers
  `C.free_pcids` over that interval. Its enter pre states a non-empty
  `free_pcids`, and publish removes exactly one PCID.

**R6 Errors.** A rejection before any recorded change stutters: the trace is
empty and `post == pre`. A rejection with a visible effect is an explicit step
(an IPC peer dequeued and scheduled with the error).

**R7 Traces.** A `*_syscall_trace` is the first step, the phase steps with
exact length bounds, and the exit step, each with its pre and transition.

## 3. alloc_quota_4k — one step

Status: conforms (focused run #27373).

- Arguments: `amount`. A zero amount succeeds with no step.
- U locks acquired and released in the step: `cpu`, container `cpu.owning_container`,
  process `cpu.current_process`. Non-U: the container's 4K allocator quota.

**Step**

- Pre: `index_valid`, `cpu.state is Running`, `cpu.current_process is Some`,
  both objects present; `!killed` for the container and process; `Unlocked`
  for `cpu`, the container, and the process; `container.quota_4k >= amount`;
  `process.quota_4k + amount <= usize::MAX`; `amount > 0`.
- Effect: the container's `quota_4k` decreases by `amount` and the process's
  increases by it (`kernel_u_only_process_quota_4k_changed`).

Stutters: ContainerKilled, ProcessKilled, ContainerQuotaInsufficient,
ProcessQuotaOverflow.

## 4. schedule — one step

Status: conforms (focused run #27374).

- Arguments: entry `regs`. K-internal label: `flushed_pcid`.
- U locks acquired and released in the step: `cpu`, the current process and
  thread when present, and the next thread. Non-U: the container scheduler and
  the PCID-needflush entry.

**Step**

- Pre: `!(cpu.state is Off)`; the container of `cpu` has a non-empty
  scheduler whose head `next` is present, `!next.killed`, `SCHEDULED`, owned
  by that container, and whose process is present; `current_process is Some`
  iff `current_thread is Some`; when a thread runs: it differs from `next`,
  is `RUNNING { cpu_id }`, `!killed`, belongs to the current process, and that
  process is present and `!killed`; `Unlocked` for `cpu`, `next`, and the
  running thread and process when present.
- Effect: `kernel_u_context_switch_changed`: `cpu` runs `next`, the previous
  thread is requeued at the tail, and at most the `(cpu_id, flushed_pcid)`
  TLB entry is flushed.

Stutters: Off, a killed running process or thread (Continue), an empty
scheduler or a killed head (Idle or Continue).

## 4a. cpu_offline_request, cpu_online — one step each

Status: conforms (workspace run #28133, noninterference run #28132).

Both are issued by a running thread on behalf of its container `C`
(`cpu.owning_container`); no permission check beyond container ownership of
`target`. Neither is issued under a syscall progress, so their pres name
`cpu.owning_container` directly (R3).

- Arguments: `target`. An invalid `target` rejects before any lock.
- U locks acquired and released in the step: `cpu` and `CS(C)`; cpu_online
  also acquires `cpu_array[target]` (Off, terminal lock major). Non-U:
  cpu_offline_request holds the request cell `F(C, target)` of `C`'s offline
  request table (lock major 3) across the step.

**cpu_offline_request step**

- Pre: `index_valid` for `cpu_id` and `target`, `cpu.state is Running`, `C`
  present, `Unlocked(cpu)`, `Unlocked(CS(C))`;
  `cpu_array[target].owning_container == C`; `!(cpu_array[target].state is Off)`;
  `!C.cpu_offline_requests[target]`.
- Effect: `C.cpu_offline_requests[target] = true`
  (`kernel_u_cpu_offline_request_changed`). The requester then sends an IPI to
  `target` (no U effect); the target's own check step (§4b) consumes the bit.

Stutters: CpuOwnerMismatch (invalid or foreign `target`), CpuAlreadyOff, and
Success when the bit was already set.

**cpu_online step**

- Pre: `index_valid` for `cpu_id` and `target`, `cpu.state is Running`, `C`
  present, `Unlocked(cpu)`, `Unlocked(CS(C))`, `Unlocked(cpu_array[target])`;
  `cpu_array[target].owning_container == C`; `cpu_array[target].state is Off`.
- Effect: `cpu_array[target].state = Idle` (`kernel_u_cpu_online_changed`);
  the request bit of an Off cpu is already clear. The caller then sends an IPI
  to `target` (no U effect).

Stutters: CpuOwnerMismatch, CpuNotOff.

## 4b. cpu_offline_check — one step before each schedule

Status: conforms (workspace run #28133, noninterference run #28132).

Entry `cpu_offline_check(cpu_id, pt_regs) -> OfflineCheckResult { Continue, Off }`
is run by the trap layer on every cpu right before `syscall_schedule` and on
IPI entry of a non-Off cpu. It is not a syscall: no `Caller`, and `C` is
`cpu.owning_container` (R3). The cpu that goes Off is the one running the
entry (`cpu_id == lctx.cpu_id()`); the trap layer halts it afterwards.

- U locks acquired and released in the step: `cpu`, `CS(C)`, and when the cpu
  is Running also `current_process` and `current_thread`. Non-U: the request
  cell `F(C, cpu_id)` (lock major 3) is held from the read through the whole
  offline, then `C`'s scheduler and `(cpu_id, KERNEL_DEFAULT_PCID)` needflush.

**cpu_offline_check step** (`cpu_offline_check_step`, label
`flushed_default_pcid`)

- Pre: `index_valid(cpu_id)`, `!(cpu.state is Off)`, `C` present,
  `C.cpu_offline_requests[cpu_id]`, `Unlocked(cpu)`, `Unlocked(CS(C))`;
  if `cpu.current_thread is Some(prev)`: `prev` and `cpu.current_process` are
  present, not killed, `Unlocked`, `prev.state == RUNNING { cpu_id }`, and
  `prev.owning_proc == cpu.current_process`.
- Effect (`kernel_u_cpu_went_off_changed`): `cpu.state = Off`,
  `cpu.current_process = cpu.current_thread = None`;
  `C.cpu_offline_requests[cpu_id] = false`; `prev`, if any, becomes
  `SCHEDULED` with `error_code = None`, `trap_frame = Some(pt_regs)` and is
  pushed on `C.scheduler`; `cpu_tlb` keeps its domain, every `(cpu_id, p)`
  entry with `p != KERNEL_DEFAULT_PCID` becomes empty, and
  `(cpu_id, KERNEL_DEFAULT_PCID)` is reset to empty exactly when the label
  `flushed_default_pcid` holds (the cpu was Running and its default-PCID
  needflush bit was set: `cpu_offline_check_flushed_default_pcid`). Nothing
  else changes; the cpu's lock state is Unlocked again at the end.
- Result: `cpu_offline_check_result(u, cpu_id)` is `Off` exactly when the step
  pre holds; the trace predicate `cpu_offline_check_entry_trace` records
  `went_off` and the label.

Stutters (`Continue`, no U step): the cpu is already Off; the request bit is
clear; the running thread or its process is already killed (the bit is kept
and `syscall_schedule` handles the kill). Each stutter leaves U unchanged.

**cpu_online_resume** (`cpu_online_resume(cpu_id) -> OnlineResumeResult
{ StillOff, Resumed }`, no U step)

IPI entry of a cpu that halted after going Off. Under `cpu` it re-reads its
state: while still Off it unlocks and halts again (`StillOff`); once
`syscall_cpu_online` has published Idle it clears the ghost `Cpu.hw_halted`
and returns to the idle loop (`Resumed`), where the trap layer runs
`cpu_offline_check` and `syscall_schedule` as usual. U is unchanged in both
outcomes (`hw_halted` is not projected).

## 5. new_thread, new_thread_with_endpoint — enter, finish

Status: conforms (focused run #27397).

- Arguments: `regs`; for the endpoint variant, `endpoint_index`.
- U locks retained from enter to finish: `cpu`, `P`, `T`, and `E(endpoint_index)`
  for the endpoint variant. Non-U: the container scheduler and the new page.
- Progress: `NewThread { regs, endpoint_index }` between enter and finish.
- Derivation: enter and finish read `P` as `cpu.current_process->Some_0` and
  `C` as `cpu.owning_container`; `W(cpu)` keeps both stable until finish.

**Enter**

- Pre: `Caller`, `prog is None`, `cpu.current_process == Some(P)`,
  `thr.owning_container == cpu.owning_container`, `thr.state == RUNNING { cpu_id }`,
  `!thr.killed`, `!P.killed`, `thr.quota_4k >= 1`; for the endpoint variant,
  `edp_idx_valid(endpoint_index)` and `E(endpoint_index)` present; `Unlocked`
  for `cpu`, `P`, `T`, and the endpoint.
- Effect: write-locks those objects and records `NewThread { regs,
  endpoint_index }`.

**Finish**

- Pre: `prog is NewThread`; `W` for `cpu`, `P`, `T`, and the endpoint at the
  recorded `endpoint_index`.
- Effect: `kernel_u_new_thread_changed`: one 4K quota of `T` funds a new
  `SCHEDULED` thread (the last of `new_u.process_map[P].owned_threads`) with
  the recorded `regs` and optional endpoint; it joins `C`'s thread set and
  scheduler.
  The step unlocks `cpu`, `P`, `T`, and the endpoint and clears `prog`.

Stutters: ProcessKilled, ThreadKilled, NoQuota, a missing endpoint descriptor.

## 6. mmap_4k — enter, directory/leaf steps, exit

Status: conforms (workspace run #27748).

- Arguments: `va`, `range`; `R = mmap_4k_syscall_va_range(va, range)`.
- U locks retained from enter to exit: `cpu`, `T`, `PT(P)`. Non-U: the
  allocator of `C` and the new pages.
- Progress: `Mmap4k { range: R, mapped, directory }`.
- `mmap_4k_locked(u, cpu_id)`: `current_thread is Some`, `T` and `P` present,
  `PT(P)` present, and `W` for `cpu`, `T`, and `PT(P)`.

**Enter** (`mmap_4k_enter_step_pre`, `mmap_4k_enter_step`)

- Pre: `Caller`, `prog is None`, `!thr.killed`, `P` present with a pagetable;
  `Unlocked` for `cpu`, `T`, and `PT(P)`; `R.wf()`, `R.len > 0`, `UserVa(u, R)`,
  `thr.quota_4k >= 4 * R.len`; no VA of `R` in `PT(P).mapping_4k`, and no
  `mapping_2m` or `mapping_1g` leaf of `PT(P)` covers a VA of `R`.
- Effect: write-locks `cpu`, `T`, and `PT(P)`; `prog = Mmap4k { R, 0, None }`.

**Directory** (`mmap_4k_directory_step_pre`, `mmap_4k_directory_step`)

- Pre: `mmap_4k_locked`, `prog is Mmap4k`, `mapped < R.len`, `thr.quota_4k >= 1`.
- Effect: one 4K quota of `T` is consumed; `directory` moves to a deeper level
  (`mmap_4k_directory_rank` increases); `R` and `mapped` are unchanged.

**Leaf** (`mmap_4k_leaf_step_pre`, `mmap_4k_leaf_step`)

- Pre: `mmap_4k_locked`, `prog is Mmap4k`, `mapped < R.len`,
  `thr.quota_4k >= 1`, and `R[mapped]` is unmapped in `PT(P)`.
- Effect: one 4K quota is consumed; `R[mapped]` maps to a present, writable,
  executable entry owned by `C`; `mapped` increases and `directory` resets
  to `None`.

**Exit** (`mmap_4k_exit_step_pre`, `mmap_4k_exit_step`)

- Pre: `mmap_4k_locked`, `prog is Mmap4k`, `mapped == R.len`, `directory is None`.
- Effect: unlocks `cpu`, `T`, and `PT(P)`; clears `prog`.

Trace: `range + 2 <= len <= 4 * range + 2`; enter, then directory or leaf
steps, then exit.

Stutters: argument errors, ThreadKilled, NoQuota, a kernel-range VA (Error),
and VaInUse.

## 7. unmap_4k — enter, leaf/flush/flushed/refund steps, exit

Status: conforms (workspace run #27748).

- Arguments: `va`, `range`; `R` as for mmap.
- U locks retained from enter to exit: `cpu`, `C`, `P`, `PT(P)`, `T`. Non-U:
  PCID needflush and TLB state, and the allocator quota of `C` and its
  ancestors.
- Progress: `Unmap4k { range: R, unmapped, flushed }`.
- `unmap_4k_locked(u, cpu_id)`: `W` for `cpu`, `T`, `P`, `PT(P)`, and `C`.

**Enter**

- Pre: `Caller`, `prog is None`; `!killed` for `T`, `P`, and `C`; `Unlocked`
  for `cpu`, `C`, `P`, `PT(P)`, and `T`; `R.wf()`, `R.len > 0`, `UserVa(u, R)`;
  every VA of `R` is in `PT(P).mapping_4k`.
- Effect: write-locks the five objects; `prog = Unmap4k { R, 0, false }`.

**Leaf**

- Pre: `unmap_4k_locked`, `prog is Unmap4k`, `unmapped < R.len`, `!flushed`,
  `R[unmapped]` mapped in `PT(P)`.
- Effect: removes `R[unmapped]` from `PT(P).mapping_4k`; `unmapped + 1`.

**Flush**

- Pre: `unmap_4k_locked`, `prog is Unmap4k`, `unmapped == R.len`, `!flushed`.
- Effect: exactly one `(cpu', u.process_map[P].pcid)` TLB entry becomes empty
  (`kernel_u_cpu_tlb_cleared`).

**Flushed**

- Pre: as for flush.
- Effect: `flushed = true`.

**Refund**

- Pre: `unmap_4k_locked`, `prog is Unmap4k`, `unmapped == R.len`, `flushed`.
- Effect: one container in `C` or `C.uppertree_seq` gains 4K quota
  (`kernel_u_container_quota_4k_increased`). The ancestors are not locked in
  U; their quota is guarded by allocator quota locks inside the step (R5).

**Exit**

- Pre: `unmap_4k_locked`, `prog is Unmap4k`, `unmapped == R.len`, `flushed`.
- Effect: unlocks the five objects; clears `prog`.

Trace: `range + 3 <= len <= range + NUM_CPUS + MAX_CONTAINER_TREE_DEPTH + 4`.

Stutters: argument errors, ContainerKilled, ProcessKilled, ThreadKilled, and
an unmapped or kernel-range VA.

## 8. share_4k — directory and leaf sub-steps

Status: conforms (map_4k run #27743). Used by new_process, new_container,
and IPC pages. Both steps take only `cpu_id` and derive their objects through
`share_4k_objects`.

- Progress: `Share4k { source_range, target_range, shared, origin }`. The
  origin selects the objects:

| Origin | Source `S` | Target `D` | Quota thread `Q` | Target container `TC` | Transfer source |
|---|---|---|---|---|---|
| `NewProcess(record)` | `P` | `record.child` | `T` | `C` | none |
| `NewContainer(record)` | `P` | `u.container_map[CC].root_process`, `CC = record.child_container` | `T` | `CC` | `C` |
| `IpcPages { peer }` | sender's process | receiver's process | receiver | receiver's container | none |

  In IpcPages, the caller sends when `peer.state` is RECEIVING; the sender and
  receiver are the caller and `peer` accordingly.
- Stability: publish records the child (or child container) in the origin, so
  no step relies on `children.last()`. The IPC peer stays locked by the caller.
  `share_4k_locked`, part of both pres, also requires `W(peer)` for origin
  IpcPages.

**Directory**

- Pre: `prog is Share4k`, `shared < source_range.len`, `W(Q)`,
  `Q.quota_4k >= 1`, `W(PT(D))`; with a transfer source, `W` for it and for
  `TC`.
- Effect: `Q.quota_4k - 1`; with a transfer source, exactly one page moves
  from its `owned_pages` to `TC.owned_pages`.

**Leaf**

- Pre: `prog is Share4k`, `shared` below both range lengths, `S != D`,
  `W(PT(S))`, `W(PT(D))`, `source_range[shared]` mapped in `PT(S)`,
  `target_range[shared]` unmapped in `PT(D)`.
- Effect: copies the source entry to `target_range[shared]` in `PT(D)`;
  `shared + 1`.

## 9. new_process, new_process_with_endpoint, new_process_with_iommu_and_endpoint

Status: conforms (workspace run #27748). Steps: enter, publish, share steps,
finish.

- Arguments: `va`, `range`, `regs`, optional `endpoint_index`; the entry point
  fixes `with_iommu`. `base = 6` with IOMMU, otherwise `4`; the publish cost is
  `base - 1`.
- U locks: enter write-locks `cpu`, `P`, `PT(P)`, `T`, and the endpoint; the
  container `C` is never locked. Publish releases `P` and creates the child
  `D` and `PT(D)` (and its IOMMU table) write-locked. Finish releases the
  rest. Non-U: the PCID allocator (enter to publish, guards `C.free_pcids`;
  the R5 exception), the scheduler, the allocator, and the staged pages. `C.owned_processes` is
  lock-free ghost state, so publish adds `D` without `C`'s lock. A future
  container kill must not rely on a one-shot snapshot of `owned_processes`.
- Progress: `NewProcess(NewProcessProgress { range, regs, endpoint_index,
  with_iommu, child: None })`, then `Share4k` whose origin is the same record
  with `child: Some(D)`.

**Enter**

- Pre: `Caller`, `prog is None`; `!killed` for `P`, `T`; `Unlocked` for
  `cpu`, `P`, `PT(P)`, `T`, and the endpoint; `R.wf()`, `R.len > 0`,
  `R.len <= (usize::MAX - base) / 3`, `UserVa(u, R)`; `C.free_pcids` is
  nonempty; the endpoint descriptor is present when requested;
  `thr.quota_4k >= base + 3 * R.len`; every VA of `R` is mapped in `PT(P)`.
- Effect: write-locks those objects; records `NewProcess`.

**Publish**

- Pre: `prog is NewProcess`; `W` for `cpu`, `P`, `PT(P)`, `T`.
- Effect: creates `D` as the last child of `P` with empty write-locked tables,
  depth `P.depth + 1`, and `P`'s ancestry; updates ancestor `subtree_set`s;
  adds `D` to `C.owned_processes`; removes exactly one PCID from
  `C.free_pcids`; `thr.quota_4k - (base - 1)`; unlocks `P`;
  `prog = Share4k { R, R, 0, NewProcess(record with child: Some(D)) }`.

**Share steps**: §8 with origin NewProcess.

**Finish**

- Pre: `prog is Share4k` with origin NewProcess and `shared == R.len`; `W`
  for `cpu`, `PT(P)`, `D`, `PT(D)`, `D`'s IOMMU table when present, `T`, and
  the endpoint.
- Effect: `kernel_u_new_thread_changed` creates the child's first thread
  `D.owned_threads.last()` with `regs` and the endpoint; unlocks `cpu`,
  `PT(P)`, `D`, `PT(D)`, the IOMMU table, `T`, and the endpoint; clears `prog`.

Trace: `range + 3 <= len <= 4 * range + 3`.

Stutters: argument errors, NoPcid, ProcessKilled, ThreadKilled, a missing
endpoint, NoQuota, and an unmapped or kernel-range source VA. new_process does
not check whether `C` is killed.

## 10. new_container — enter, publish, share steps, finish

Status: conforms (workspace run #27748).

- Arguments: `va`, `range`, `funding`, `process_quota`, `transfer_cpu`, `regs`.
- U locks: enter write-locks `cpu`, `C`, `CS(C)`, `P`, `PT(P)`, `T`. Publish
  acquires and releases `transfer_cpu`, releases `CS(C)`, and creates the
  child container `CC` (with `CS(CC)` unlocked), its root process `D`, and
  `PT(D)` write-locked. Finish releases the rest. Non-U: the PCID allocator
  and 2M tails, the schedulers, and the staged pages.
- Progress: `NewContainer(NewContainerProgress { range, funding,
  process_quota, transfer_cpu, regs, child_container: None })`, then `Share4k`
  whose origin is the same record with `child_container: Some(CC)`.

**Enter**

- Pre: `Caller`, `prog is None`; `!killed` for `C`, `P`, `T`; `Unlocked` for
  `cpu`, `C`, `CS(C)`, `P`, `PT(P)`, `T`; `R.wf()`, `R.len > 0`,
  `R.len <= (usize::MAX - 9) / 3`, `UserVa(u, R)`; `transfer_cpu < NUM_CPUS`;
  `process_quota <= funding <= usize::MAX - 9 - 3 * R.len`;
  `C.depth < MAX_CONTAINER_TREE_DEPTH`;
  `thr.quota_4k >= 9 + funding + 3 * R.len` and `thr.quota_2m >= 2`; every VA
  of `R` is mapped in `PT(P)`; `cpu_array[transfer_cpu]` is Off and owned by `C`.
- Effect: write-locks those objects; records `NewContainer`.

**Publish**

- Pre: `prog is NewContainer`; `W` for `cpu`, `C`, `CS(C)`, `P`, `PT(P)`,
  `T`; `Unlocked(cpu_array[transfer_cpu])`, which is Off and owned by `C`.
- Effect: `kernel_u_container_root_created`: `CC` becomes the last child of
  `C`, with root process `D`. `C` and each container of `C.uppertree_seq` gain
  `CC` in `subtree_set`; `2 * 512 + 9 + funding` pages of `C.owned_pages`,
  including `CC`, `D`, and `CC.cpu_set`, move to `CC.owned_pages`. `T` pays
  `8 + funding` 4K quota and 2 of 2M quota; `CC` receives
  `funding - process_quota` and `D` receives `process_quota`. `transfer_cpu`
  moves to `CC` and stays unlocked; `CS(C)` is released;
  `prog = Share4k { R, R, 0, NewContainer(record with child_container: Some(CC)) }`.

**Share steps**: §8 with origin NewContainer.

**Finish**

- Pre: `prog is Share4k` with origin NewContainer and `shared == R.len`; `W`
  for `cpu`, `C`, `CC`, `P`, `PT(P)`, `D`, `PT(D)`, `T`.
- Effect: `kernel_u_new_thread_changed`: creates the root thread
  `D.owned_threads.last()` with `regs`, adds it to `CC.owned_threads` and the
  tail of `CC.scheduler`, and charges `T` one 4K quota; unlocks `cpu`, `C`,
  `CC`, `P`, `PT(P)`, `D`, `PT(D)`, `T`; clears `prog`.

Trace: `range + 3 <= len <= 4 * range + 3`.

Stutters: argument errors, ContainerKilled, depth overflow, ProcessKilled,
ThreadKilled, NoQuota, a bad source range, CpuOwnerMismatch, CpuNotOff.

## 11. IPC ordinary: send/receive empty, no_block, cpu — one step

Status: conforms (workspace run #27751).

- Arguments: `endpoint_index`, the payload, the waiting direction fixed by the
  entry point, `regs`; K-internal label `flushed_default_pcid`.
- `IpcCaller(u, cpu_id, i)`: `Caller`, `prog is None`,
  `cpu.current_process == Some(P)`, `thr.state == RUNNING { cpu_id }`,
  `!thr.killed`, `!P.killed`, `edp_idx_valid(i)`, `E(i)` present,
  `T` not in `E(i).queue`, and `Unlocked` for `cpu`, `P`, `T`, `E(i)`.
- Stutters: ProcessKilled, ThreadKilled, InvalidEndpoint, PeerKilled (a killed
  peer stays queued), and for no_block the NoPeer and SameDirection results.

**Block** (blocking entry points)

- Pre: `IpcCaller`; `E(i).queue` is empty or waits in the caller's direction.
- Effect: `kernel_u_ipc_block_changed`: `T` waits on `E(i)` with the payload
  and `regs`, the CPU goes idle, and the `(cpu_id, KERNEL_DEFAULT_PCID)` TLB
  entry is flushed when `flushed_default_pcid`.

**Rendezvous**

- Pre: `IpcCaller`; the queue head `peer = E(i).queue[0]` waits in the
  opposite direction, differs from `T`, is present, `!peer.killed`, blocks on
  `E(i)`, and its container is present; `Unlocked(peer)`. A Cpu payload whose
  result is neither TypeMismatch nor SameContainer also needs `Unlocked(CS)`
  for the caller's and the peer's containers, and a successful CPU transfer
  needs `Unlocked` for the transferred Off CPU.
- Result (`ipc_rendezvous_result`): TypeMismatch unless `peer` waits in the
  opposite direction with a matching payload kind; for Cpu, SameContainer,
  CpuOwnerMismatch (the CPU is not the sender container's), CpuNotOff, then
  Success for the sender and SuccessUsize for the receiver; for Endpoint,
  EndpointSourceInvalid, EndpointTargetInUse; for Pages, TypeMismatch on
  unequal lengths and SameProcess. Success on an Endpoint or Pages payload
  takes no step here and enters §12 or §13; otherwise the syscall returns
  this result.
- Effect: `kernel_u_ipc_rendezvous_changed`: `peer` is dequeued and scheduled
  with `ipc_peer_result`. For a CPU payload whose checks pass, the Off CPU
  moves to the receiver's container.

## 12. IPC endpoint — transit, finish

Status: conforms (workspace run #27613, monolith run #27612).

- Arguments: `endpoint_index` (the channel), `payload_index`, the direction.
- U locks: transit acquires `cpu`, `P`, `T`, `peer` (retained) and the channel
  (released inside the step). Finish acquires and releases the payload
  endpoint. Non-U: the peer's scheduler.
- Progress: `IpcEndpoint { peer, caller_sends, payload_index }`. The sender is
  `T` when `caller_sends`, otherwise `peer`; the receiver is the other one. The
  source index is `payload_index` on the caller's side and the peer's
  `ipc_payload.endpoint_index` on the peer's side; the target index is the
  other one. The payload endpoint is the sender's descriptor at the source
  index.

**Transit**

- Pre: the §11 rendezvous pre for the channel; `edp_idx_valid(payload_index)`;
  the peer waits in the opposite direction with an Endpoint payload; the
  source descriptor is present and the target descriptor is empty.
- Effect: write-locks `cpu`, `P`, `T`, `peer`; dequeues `peer` into
  `IPC_ENDPOINT_TRANSIT` with no blocking endpoint; records `IpcEndpoint`.

**Finish**

- Pre: `prog is IpcEndpoint`; `W` for `cpu`, `P`, `T`, `peer`; the payload
  endpoint is present and `Unlocked`.
- Result (`ipc_endpoint_finish_result`): Success when the payload endpoint's
  container is the receiver's container or in its `uppertree_seq`, otherwise
  EndpointOwnerMismatch. The syscall returns this result.
- Effect: on Success the receiver's descriptor at the target index becomes the
  payload endpoint and the endpoint gains that owner. `peer` is scheduled with
  the result and an Empty payload and joins its container's scheduler. The
  step unlocks `cpu`, `P`, `T`, `peer`, and the payload endpoint and clears
  `prog`.

Single rendezvous error steps (§11): EndpointSourceInvalid,
EndpointTargetInUse, TypeMismatch.

## 13. IPC pages — enter, lock tables, check, share steps, unlock tables, finish

Status: conforms (workspace run #27816).

- Arguments: `endpoint_index` (the channel), `va`, `range`, `regs`; the entry
  point fixes the direction. `R = VaRange4K { start: va, len: range }` is the
  caller's payload. `regs` and the K-internal `flushed_default_pcid` serve only
  the §11 block step. Every later step takes only `cpu_id`.
- U locks: enter write-locks `cpu`, `P`, `T`, `peer`, and the channel
  `E(endpoint_index)`. Lock tables write-locks both processes' page tables; a
  failed check or unlock tables releases them; finish releases the rest.
  Non-U: the peer's scheduler, and the receiver container's allocator and the
  new directory pages in directory steps.
- Progress: `IpcPages { source_range, target_range, peer, locked: false,
  released: None }` from enter to lock tables, and `locked: true` from lock
  tables to check; after a passed check `Share4k { source_range,
  target_range, shared, origin: IpcPages { peer } }`; then `IpcPages { ..,
  locked: false, released: Some(result) }` from a failed check or unlock
  tables to finish. `locked` is the holder credential for both tables: U lock
  modes carry no owner, so another cpu's locked tables never satisfy this
  caller's check pre.
  `source_range` is the sender's range, `target_range` the receiver's, and
  `len = source_range.len`.
- Derivation: `peer` is recorded in `prog`; the channel is
  `peer.blocking_endpoint_ptr`; the caller sends exactly when `peer.state` is
  RECEIVING (`ipc_pages_sender`, `ipc_pages_receiver`); the source and target
  processes are the sender's and receiver's `owning_proc`. These hold until
  finish because `peer` stays write-locked and heads the write-locked channel.
- `ipc_pages_held(u, cpu_id)`: `prog is IpcPages`; `cpu`,
  `cpu.current_process`, `T`, `peer`, and the channel are present and `W`.
- `ipc_pages_tables_in(u, cpu_id, s)`: the source and target processes differ,
  are present with page tables, and both tables have lock mode `s`.
- Page-table view: `PageTableU` shows only present leaves.
  `pagetable_hidden_leaves_only_when_wlocked` (in `pagetable_perms_wf`) makes
  every table with a non-present leaf write-locked, so a table that is not
  write-locked satisfies `leaves_present` and its U view equals its full 4K,
  2M, and 1G mapping. Lock tables keeps `leaves_present`, so the check reads
  the mappings the implementation checks.

**Enter** (`ipc_pages_enter_step_pre`, `ipc_pages_enter_step`)

- Pre: `R.wf()`, `R.len > 0`; the §11 rendezvous pre for payload
  `Pages { R }` with `peer = E(endpoint_index).queue[0]`;
  `ipc_rendezvous_result` is Success: `peer` waits in the opposite direction
  with a Pages payload of the same length, and the sender's and receiver's
  processes differ.
- Effect: write-locks `cpu`, `P`, `T`, `peer`, and the channel;
  `prog = IpcPages { source_range, target_range, peer, locked: false, released: None }`, where
  the caller's `R` is the source range when it sends and the target range
  otherwise, and `peer.ipc_payload`'s range is the other.

**Lock tables** (`ipc_pages_lock_tables_step_pre`, `ipc_pages_lock_tables_step`)

- Pre: `ipc_pages_held`, `!locked`, `released is None`,
  `ipc_pages_tables_in(Unlocked)`.
- Effect: both page tables become WriteLocked and `prog.locked` becomes true.

**Check** (`ipc_pages_check_step_pre`, `ipc_pages_check_step`)

- Pre: `ipc_pages_held`, `locked`, `released is None`,
  `ipc_pages_tables_in(WriteLocked)`.
- Result (`ipc_pages_check_result`, from `old_u` in the implementation's
  order): Error unless `UserVa` for the source range; SourceUnmapped unless
  every source page is in the source table's `mapping_4k`; NoQuota when the
  receiver's `quota_4k < 3 * len`; Error unless `UserVa` for the target range;
  VaInUse unless the target is free (`ipc_pages_target_free`: no 4K leaf from
  its first to its last page and no 1G, 2M, or 4K leaf covering one of its
  pages); PageOwnerMismatch unless the owner of every source page is the
  receiver's container or in its `uppertree_seq`; otherwise Success.
- Effect: on Success, `prog = Share4k { source_range, target_range, 0,
  IpcPages { peer } }` and nothing else changes. Otherwise both tables become
  Unlocked and `prog = IpcPages { .., locked: false, released: Some(result) }`. The
  implementation's per-page owner-check boundaries change no U state and
  stutter.

**Share steps**: §8 with origin IpcPages, `len` to `4 * len` of them.

**Unlock tables** (`ipc_pages_unlock_tables_step_pre`, `ipc_pages_unlock_tables_step`)

- Pre (success only): `share_4k_locked` (which for origin IpcPages also
  requires `peer` present and `W`), origin IpcPages, `shared == len`;
  the source and target processes named by `share_4k_objects` differ, are
  present with page tables, and both tables are `W`.
- Effect: both tables become Unlocked;
  `prog = IpcPages { source_range, target_range, peer, locked: false, released: Some(Success) }`.

**Finish** (`ipc_pages_finish_step_pre`, `ipc_pages_finish_step`)

- Pre: `ipc_pages_held`, `!locked`, `released is Some`, the channel's queue is non-empty
  with head `peer`, and `peer`'s container is present.
- Effect: `peer` becomes SCHEDULED with no blocking endpoint, an Empty payload,
  and the recorded result as `error_code`; it leaves the channel queue and
  joins its container's scheduler. The step unlocks `cpu`, `P`, `T`, `peer`,
  and the channel and clears `prog`. The syscall returns the same result.

Trace (`ipc_pages_syscall_trace`): CpuIdle is the §11 block step; SameProcess
and TypeMismatch (including unequal lengths) are one §11 rendezvous error step.
Both also state `R.wf()` and `R.len > 0`, the argument checks made before the
step.
After a passed rendezvous, success is enter, lock tables, check, share steps,
unlock tables, finish (`len + 5 <= steps <= 4 * len + 5`); a failed check is
enter, lock tables, check, finish (4 steps), and the syscall returns the check
result. Every step changes a non-lock field (`prog`, or the receiver's
`quota_4k` in a directory step), so the nonlock view has `len + 5` to
`4 * len + 5` steps on success and 4 on a failed check.

Stutters: argument errors (Error before any step), ProcessKilled,
ThreadKilled, InvalidEndpoint, and PeerKilled.

## 14. Syscall entry list

| Entry point | Section |
|---|---|
| `syscall_alloc_quota_4k` | §3 |
| `syscall_schedule` | §4 |
| `syscall_cpu_offline_request`, `syscall_cpu_online` | §4a |
| `cpu_offline_check` (trap-layer entry, before every `syscall_schedule`) | §4b |
| `cpu_online_resume` (trap-layer IPI entry of a halted cpu) | §4b |
| `syscall_new_thread`, `syscall_new_thread_with_endpoint` | §5 |
| `syscall_mmap_4k` | §6 |
| `syscall_unmap_4k` | §7 |
| `syscall_new_process`, `syscall_new_process_with_endpoint`, `syscall_new_process_with_iommu_and_endpoint` | §9 |
| `syscall_new_container` | §10 |
| `syscall_send_empty`, `syscall_receive_empty`, `syscall_send_empty_no_block`, `syscall_receive_empty_no_block`, `syscall_send_cpu`, `syscall_receive_cpu` | §11 |
| `syscall_send_endpoint`, `syscall_receive_endpoint` | §11, §12 |
| `syscall_send_pages`, `syscall_receive_pages` | §11, §13 |

## 15. Approved representation changes

These changes were approved on 2026-09-29 and are all applied.

| Variant | Current | Approved | Needed by |
|---|---|---|---|
| `NewThread` | applied | `{ regs, endpoint_index: Option<EndpointIdx> }` | new_thread finish (R1, R4) |
| `NewProcess` | applied | `NewProcess(NewProcessProgress { range, regs, endpoint_index, with_iommu, child: Option })` | publish, finish |
| `NewContainer` | applied | `NewContainer(NewContainerProgress { range, funding, process_quota, transfer_cpu, regs, child_container: Option })` | publish, finish |
| `Share4k` | applied | adds `origin: NewProcess(NewProcessProgress) \| NewContainer(NewContainerProgress) \| IpcPages { peer }` | share steps, finish, IPC pages unlock tables |
| `IpcEndpoint` | applied | `{ peer, caller_sends, payload_index }` | finish |
| `IpcPages` | applied | `{ source_range, target_range, peer, locked: bool, released: Option<RetValueType> }` (`locked` approved 2026-09-30) | lock tables, check, unlock tables, finish |

`ContainerU.cpu_set_lock` (approved 2026-09-30) projects the container's
CPU-set lock mode; new_container (§10) and IPC Cpu (§11) state it.

`ContainerU.cpu_offline_requests: Seq<bool>` (approved 2026-10-03 with the cpu
hotplug plan) projects the container's per-cpu offline request table
(`cpu_offline_requests_of(cpu_offline_mp[cpu_offline_flags_ptr(c)])`); the
table lives in the second 4K of the container's 2M page, its cells are locked
per cpu (major 3) and are not U-visible. new_container publishes it all-false
(§10); cpu_offline_request sets one bit (§4a); cpu_offline_check clears it
when the cpu goes Off (§4b).

Kernel representation changes for cpu hotplug (approved 2026-10-03, applied):
`KernelK.cpu_offline_mp: UnLockedMap<RwLockCpuOfflineFlagsPtr, CpuOfflineFlags>`
holds every container's table at `cpu_offline_flags_ptr(c) = c + 4096`, with
`cpu_offline_flags_wf` (cells aligned, `Off ⇒ !requested`) and
`container_cpu_offline_flags_wf` (container ↔ table); the cell locks form the
new family `CPU_OFFLINE_FLAG_LOCK_MAJOR = 3` (`KernelObjId::CpuOfflineFlag`,
`LocalContext.cpu_offline_flag_lock_map`). `Cpu.hw_halted: Ghost<bool>`
(`CpuView.hw_halted`) records whether the hardware is halted: set when the cpu
publishes Off (§4b), cleared by `cpu_online_resume`; it is not U-visible and
no invariant depends on it. Trusted primitives: `CpuTLB::flush_all_local_pcids`
(external_body; empties every TLB entry of the calling cpu except
`KERNEL_DEFAULT_PCID`), `send_ipi`, `halt_until_ipi` (empty stubs).

Kernel representation change (applied): `Container.owned_processes` moved to
the lock-free `ContainerGhost`, so new_process publishes a child without the
container lock, and `wlock_pcid_allocator` no longer requires it.

U projection changes:

- `ProcessU.pcid` (applied): the process's PCID from `ProcessRO.pcid`. The
  unmap flush step names the flushed TLB entries through it, so no `pcid`
  parameter remains.
- `KernelU.kernel_l4_end` (applied): the first user L4 index, projected from
  `dflt_pt.kernel_l4_end`. The kernel invariant makes every pagetable's
  `kernel_l4_end` equal to it, and no operation changes it. Pres compare L4
  indices (`UserVa`) exactly as the implementation's prechecks do. A raw VA
  comparison would differ, because `spec_va_4k_valid` does not bound the bits
  above 47 that `spec_v2l4index` masks off.

## 16. Decisions

1. Later steps read syscall arguments from `prog` (R1), using the §15 fields.
2. The unmap flush PCID comes from `ProcessU.pcid`.
3. The user-VA bound is `KernelU.kernel_l4_end`, compared through `UserVa`.
4. CPU hotplug (2026-10-03): offline requests are per-container cells locked
   per cpu (major 3, held through the whole offline); no permission check
   beyond container ownership of the target; the target cpu offlines itself in
   `cpu_offline_check` right before each schedule, requeueing its running
   thread and deferring to `syscall_schedule` when that thread or its process
   is killed; `syscall_cpu_online` publishes Idle and sends the IPI, and the
   woken cpu only clears `hw_halted` (re-halting while still Off); there is no
   `Offlining` state.
