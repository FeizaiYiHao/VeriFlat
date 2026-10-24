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

**R5 Locks outside U.** Allocator quota/cache/pool, scheduler shard, PCID
allocator, PCID-needflush, and page locks are invisible in U. The U fields
they guard are container `quota_*` (allocator quota), container `scheduler`
(one run queue per cpu, `scheduler[c]` guarded by shard `c`), container
`free_pcids` (PCID allocator), and `cpu_tlb` (PCID needflush). The CPU-set lock is visible as `ContainerU.cpu_set_lock` (`CS(c)`)
and guards the `owning_container` of the container's Off CPUs.

- A step may change such a field without a U-visible lock only when the
  change happens inside that one step. Its pre still states the field's
  precondition (for example a non-empty `free_pcids`).
- When a non-U lock stays held across steps, a U-visible lock that the caller
  holds over the same interval must also cover the guarded fields.
- Exception (approved 2026-09-30): new_process holds the PCID allocator of `C`
  from enter to publish with `C` unlocked (§9), so no U lock covers
  `C.free_pcids` over that interval. Its enter pre states a non-empty
  `free_pcids`, and publish removes exactly one PCID. The allocator's major
  (107) sits above `T` (106): it is taken after `P` and `T`, so a process's
  last exiting thread can release the PCID under `P` and `T` (§17).

**R6 Errors.** A rejection before any recorded change stutters: the trace is
empty and `post == pre`. A rejection with a visible effect is an explicit step
(an IPC peer dequeued and scheduled with the error).

**R7 Traces.** A `*_syscall_trace` is the first step, the phase steps with
exact length bounds, and the exit step, each with its pre and transition.

**R8 Idle cpu.** Every syscall entry write-locks its cpu first and returns
`CpuIdle` with an empty trace and `post == pre` when the cpu is no longer
Running or is `killed`: a kill evicted its thread between the trap and the
lock, or a killer holds the cpu marked while it evicts the thread (§18). A
marked cpu is never waited for: `wlock_cpu` returns at once, so the cpu
reaches user mode or the idle `hlt` and takes the eviction IPI. Entries
that check their arguments before locking (mmap_4k, unmap_4k, new_process,
new_container, the hotplug `target` index, the IPC pages range) report
argument errors first. The result specs and traces state this as their first
branch (after the argument checks); IPC traces that classify `CpuIdle` as a
block step take that branch only when the cpu is Running at entry.

## 3. alloc_quota_4k, alloc_quota_2m — one step each

Status: conforms (alloc_quota_4k focused run #27373; alloc_quota_2m workspace
run #28754, monolith run #28755, noninterference run #28756).

- Arguments: `amount`. A zero amount succeeds with no step.
- U locks acquired and released in the step: `cpu`, container `cpu.owning_container`,
  process `cpu.current_process`. Non-U: the container's 4K allocator quota.
- alloc_quota_2m is the same step over `quota_2m`
  (`kernel_u_only_process_quota_2m_changed`) with the same locks and stutters.

**Step**

- Pre: `index_valid`, `cpu.state is Running`, `cpu.current_process is Some`,
  both objects present; `!killed` for the container and process; `!zombie`
  for the container; `Unlocked`
  for `cpu`, the container, and the process; `container.quota_4k >= amount`;
  `process.quota_4k + amount <= usize::MAX`; `amount > 0`.
- Effect: the container's `quota_4k` decreases by `amount` and the process's
  increases by it (`kernel_u_only_process_quota_4k_changed`).

Stutters: CpuIdle (cpu not Running or killed), ContainerKilled, ContainerZombie, ProcessKilled,
ContainerQuotaInsufficient, ProcessQuotaOverflow.

## 3a. alloc_thread_quota_4k, alloc_thread_quota_2m — one step each

Status: conforms (alloc_thread_quota_4k workspace run #28692, noninterference
run #28688; alloc_thread_quota_2m workspace run #28754, monolith run #28755,
noninterference run #28756).

- Arguments: `amount`. A zero amount succeeds with no step.
- U locks acquired and released in the step: `cpu`, process `cpu.current_process`,
  thread `cpu.current_thread`. The container is not locked.
- alloc_thread_quota_2m is the same step over `quota_2m`
  (`kernel_u_only_process2thread_quota_2m_changed`) with the same locks and
  stutters.

**Step**

- Pre: `index_valid`, `cpu.state is Running`, `cpu.current_process is Some`,
  `cpu.current_thread is Some`, both objects present; `!killed` for the process
  and thread; `Unlocked` for `cpu`, the process, and the thread;
  `process.quota_4k >= amount`; `thread.quota_4k + amount <= usize::MAX`;
  `amount > 0`.
- Effect: the process's `quota_4k` decreases by `amount` and the thread's
  increases by it (`kernel_u_only_process2thread_quota_4k_changed`).

Stutters: CpuIdle (cpu not Running or killed), ProcessKilled, ThreadKilled, NoQuota, ThreadQuotaOverflow.

## 4. schedule — one step

Status: conforms (focused run #27374).

- Arguments: entry `regs`. K-internal label: `flushed_pcid`.
- U locks acquired and released in the step: `cpu`, the current process and
  thread when present, and the next thread. Non-U: shard `cpu_id` of the
  container scheduler and the PCID-needflush entry.

**Step**

- Pre: `!(cpu.state is Off)`; shard `cpu_id` of the container's scheduler is
  non-empty and its head `next` is present, `!next.killed`, `SCHEDULED`, owned
  by that container, and whose process is present; `current_process is Some`
  iff `current_thread is Some`; when a thread runs: it differs from `next`,
  is `RUNNING { cpu_id }`, `!killed`, belongs to the current process, and that
  process is present and `!killed`; `Unlocked` for `cpu`, `next`, and the
  running thread and process when present.
- Effect: `kernel_u_context_switch_changed`: `cpu` runs `next` with
  `next.last_cpu = cpu_id`, the previous thread is requeued at the tail of
  shard `cpu_id` as `SCHEDULED { cpu_id }`, and at most the
  `(cpu_id, flushed_pcid)` TLB entry is flushed.

Stutters: Off, a `killed` cpu (Idle), a killed running process or thread (Continue), an empty shard
`cpu_id` or a killed head (Idle or Continue). After Idle the trap layer runs
`rebalance_pull` (§4c).

## 4a. cpu_offline_request, cpu_online, and their child variants — one step each

Status: conforms (own variants workspace run #28133, noninterference run
#28132; child variants workspace run #28754, monolith run #28755,
noninterference run #28756).

All four are issued by a running thread of container `P`
(`cpu.owning_container`). The own variants `cpu_offline_request(target)` and
`cpu_online(target)` act on a cpu of `C = P`. The child variants
`cpu_offline_request_child(i, target)` and `cpu_online_child(i, target)` act on
a cpu of `P`'s direct child `C = P.children[i]`; a grandchild's cpu is
rejected. There is no other permission check. None is issued under a syscall
progress, so their pres name `cpu.owning_container` directly (R3).

- Arguments: `target`, and the child index `i` for the child variants. An
  invalid `target` rejects before any lock.
- Each call is one atomic section with two-phase locking. In lock order:
  - `cpu`;
  - on the child variants, `P` (`wlock_container_unless_killed`), which keeps
    `P.children` stable;
  - on cpu_offline_request, the non-U request cell `F(C, target)` of `C`'s
    offline request table (lock major 104);
  - `CS(C)`;
  - on cpu_online, `cpu_array[target]` (Off, terminal lock major).

  The request cell, `CS(C)`, `P`, and `cpu` are all released inside the step.

**cpu_offline_request step** (`cpu_offline_request_step`,
`cpu_offline_request_child_step`)

- Pre: `index_valid` for `cpu_id` and `target`, `cpu.state is Running`, `C`
  present, `Unlocked(cpu)`, `Unlocked(CS(C))`;
  `cpu_array[target].owning_container == C`; `!(cpu_array[target].state is Off)`;
  `!C.cpu_offline_requests[target]`.
- The child pre names `C` as `cpu_array[target].owning_container` and adds:
  `P` present, `Unlocked(P)`, `!P.killed`, `!P.zombie`, and `C.parent == Some(P)`.
- Effect: `C.cpu_offline_requests[target] = true`
  (`kernel_u_cpu_offline_request_changed`). On the child variant, the lock of
  `P` is released inside the step, so `P` is unchanged in U. The requester then sends an IPI to
  `target` (no U effect); the target's own check step (§4b) consumes the bit.

Stutters:
- CpuOwnerMismatch: an invalid or foreign `target`; on the child variant also
  `i >= P.children.len()` or a `target` that `P.children[i]` does not own;
- CpuIdle: after the `target` index check, a cpu no longer Running;
- ContainerKilled: child variant only, when `P` is killed;
- ContainerZombie: child variant only, when `P` is a zombie;
- CpuAlreadyOff;
- Success, when the bit was already set.

**cpu_online step** (`cpu_online_step`, `cpu_online_child_step`)

- Pre: `index_valid` for `cpu_id` and `target`, `cpu.state is Running`, `C`
  present, `Unlocked(cpu)`, `Unlocked(CS(C))`, `Unlocked(cpu_array[target])`;
  `cpu_array[target].owning_container == C`; `cpu_array[target].state is Off`.
  The child pre adds the same `P` conditions as the child request.
- Effect: `cpu_array[target].state = Idle` (`kernel_u_cpu_online_changed`);
  the request bit of an Off cpu is already clear. The caller then sends an IPI
  to `target` (no U effect).

Stutters: CpuOwnerMismatch for an invalid `target` index, CpuIdle (cpu not Running or killed), CpuOwnerMismatch (with the same child cases), ContainerKilled and
ContainerZombie (child variant), CpuNotOff.

## 4b. cpu_offline_check — one step before each schedule

Status: conforms (workspace run #28133, noninterference run #28132).

Entry `cpu_offline_check(cpu_id, pt_regs) -> OfflineCheckResult { Continue, Off }`
is run by the trap layer on every cpu right before `syscall_schedule` and on
IPI entry of a non-Off cpu. It is not a syscall: no `Caller`, and `C` is
`cpu.owning_container` (R3). The cpu that goes Off is the one running the
entry (`cpu_id == lctx.cpu_id()`); the trap layer halts it afterwards.

- U locks acquired and released in the step: `cpu`, `CS(C)`, and when the cpu
  is Running also `current_process` and `current_thread`. Non-U: the request
  cell `F(C, cpu_id)` (lock major 104) is held from the read through the whole
  offline, then shard `cpu_id` of `C`'s scheduler and
  `(cpu_id, KERNEL_DEFAULT_PCID)` needflush.

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
  `SCHEDULED { cpu_id }` with `error_code = None`, `trap_frame = Some(pt_regs)`
  and is pushed on `C.scheduler[cpu_id]`; `cpu_tlb` keeps its domain, every `(cpu_id, p)`
  entry with `p != KERNEL_DEFAULT_PCID` becomes empty, and
  `(cpu_id, KERNEL_DEFAULT_PCID)` is reset to empty exactly when the label
  `flushed_default_pcid` holds (the cpu was Running and its default-PCID
  needflush bit was set: `cpu_offline_check_flushed_default_pcid`). Nothing
  else changes; the cpu's lock state is Unlocked again at the end.
- Result: `cpu_offline_check_result(u, cpu_id)` is `Off` exactly when the step
  pre holds; the trace predicate `cpu_offline_check_entry_trace` records
  `went_off` and the label.

Stutters (`Continue`, no U step): the cpu is already Off or `killed`; the request bit is
clear; the running thread or its process is already killed (the bit is kept
and `syscall_schedule` handles the kill). Each stutter leaves U unchanged.

**cpu_online_resume** (`cpu_online_resume(cpu_id) -> OnlineResumeResult
{ StillOff, Resumed }`, no U step)

IPI entry of a cpu that halted after going Off. Under `cpu` it re-reads its
state: while still Off it unlocks and halts again (`StillOff`, also returned at once for a `killed` cpu); once
`syscall_cpu_online` has published Idle it clears the ghost `Cpu.hw_halted`
and returns to the idle loop (`Resumed`), where the trap layer runs
`cpu_offline_check` and `syscall_schedule` as usual. U is unchanged in both
outcomes (`hw_halted` is not projected).

## 4c. rebalance_pull — one step

Status: conforms (focused run #28512).

Entry `rebalance_pull(cpu_id) -> RebalanceResult { Nothing, Pulled { thread_ptr } }`
is run by the trap layer on an Idle cpu after `syscall_schedule` returns Idle.
It is not a syscall: no `Caller`, and `C` is `cpu.owning_container`. Let
`Q = C.scheduler` and `v = first_nonempty_shard(Q, 0, cpu_id)`, the lowest
shard other than `cpu_id` whose queue is non-empty.

- U locks acquired and released in the step: `cpu` and the moved thread.
  Non-U: shards `0..=v` of `C`'s scheduler in cpu-id order, and shard `cpu_id`
  when `v < cpu_id`.

**Step** (`rebalance_pull_step_pre`, `rebalance_pull_step`)

- Pre: `cpu.state is Idle`, `C` present, `Q[cpu_id]` empty, `v is Some`,
  `t = Q[v][0]` present, `!t.killed`, `t.state == SCHEDULED { v }`, owned by
  `C`; `Unlocked(cpu)`, `Unlocked(t)`.
- Effect (`kernel_u_rebalance_pull_changed`): `Q[v] = Q[v].skip(1)`,
  `Q[cpu_id] = seq![t]`, `t.state = SCHEDULED { cpu_id }`; nothing else
  changes.
- Result: `rebalance_pull_syscall_result(u, cpu_id)` is `Pulled { t }` exactly
  when the step pre's non-lock conditions hold; the trace predicate
  `rebalance_pull_syscall_trace` records whether it pulled. After `Pulled` the
  trap layer runs `syscall_schedule` again; after `Nothing` it halts until an
  IPI or tick and retries.

Stutters (`Nothing`, no U step): the cpu is not Idle; `Q[cpu_id]` is
non-empty; every other shard is empty; the head `Q[v][0]` is killed.

## 4d. pci_attach_dma — one step

Status: conforms (workspace run #28638).

Issued by a running thread for its process `P` (`cpu.current_process`);
the B/D/F `(bus, device, function)` must name a PCI function `P` owns, and
`P` must have an IOMMU table. There is no detach syscall: a transfer (§11)
detaches.

- Arguments: `bus`, `device`, `function`; the trap layer guarantees
  `pci_bdf_valid`.
- U locks acquired and released in the step: `cpu`, `P`. Non-U: the root
  table lock (major `IOMMU_ROOT_TABLE_LOCK_MAJOR`), taken after `P` and held
  across the checks and the attach.
- Pre: `index_valid(cpu_id)`, `cpu.state is Running`, `P` present,
  `Unlocked(cpu)`, `Unlocked(P)`, `!P.killed`,
  `P.owned_pci_functions.contains((bus, device, function))`,
  `P.iommu_table is Some`, `!iommu_root_table.attached[bus][device][function]`.
- Effect: `iommu_root_table.attached[bus][device][function] = true`
  (`kernel_u_pci_attach_changed`). In K the context entry points at the root
  of `P`'s IOMMU table (`ProcessRO.iommu_cr3`), in the BDF-encoded VT-d
  domain `pci_bdf_did`; that IOTLB domain is already empty, because a
  detached function's domain is empty.

Stutters (in this order): CpuIdle (cpu not Running or killed), ProcessKilled, PciOwnerMismatch, PciNoIommuTable,
PciAlreadyAttached.

## 5. new_thread, new_thread_with_endpoint — enter, finish

Status: conforms (focused run #27397).

- Arguments: `regs`; for the endpoint variant, `endpoint_index`.
- U locks retained from enter to finish: `cpu`, `P`, `T`, and `E(endpoint_index)`
  for the endpoint variant. Non-U: shard `cpu_id` of the container scheduler
  and the new page.
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
  `SCHEDULED { cpu_id }` thread (the last of `new_u.process_map[P].owned_threads`)
  with `last_cpu = cpu_id`, the recorded `regs` and optional endpoint; it joins
  `C`'s thread set and the tail of `C.scheduler[cpu_id]`.
  The step unlocks `cpu`, `P`, `T`, and the endpoint and clears `prog`.

Stutters: CpuIdle (cpu not Running or killed), ProcessKilled, ThreadKilled, NoQuota, a missing endpoint descriptor.

## 5a. new_endpoint — enter, finish

Status: conforms (workspace run #28754, monolith run #28755, noninterference run
#28756).

- Arguments: `endpoint_index`.
- U locks retained from enter to finish: `cpu`, `C`, `P`, and `T`. Non-U: the
  new page. The new endpoint is created write-locked and unlocked inside finish.
- Progress: `NewEndpoint { slot }` between enter and finish.
- Derivation: enter and finish read `C` as `cpu.owning_container`, `P` as
  `cpu.current_process->Some_0`, and `T` as `cpu.current_thread->Some_0`;
  `W(cpu)` keeps them stable until finish.

**Enter**

- Pre: `Caller`, `prog is None`, `cpu.current_process == Some(P)`,
  `thr.owning_proc == P`, `thr.owning_container == C`,
  `thr.state == RUNNING { cpu_id }`, `!C.killed`, `!C.zombie`, `!P.killed`, `!thr.killed`,
  `edp_idx_valid(endpoint_index)`, `thr.endpoint_descriptors[endpoint_index] is None`,
  `thr.quota_4k >= 1`; `Unlocked` for `cpu`, `C`, `P`, and `T`.
- Effect: write-locks those objects and records `NewEndpoint { slot: endpoint_index }`.

**Finish**

- Pre: `prog is NewEndpoint` with a valid `slot`; `W` for `cpu`, `C`, `P`, and `T`.
- Effect: `kernel_u_new_endpoint_changed`: one 4K quota of `T` funds a fresh,
  unlocked endpoint `E` of `C` with an empty queue in state `RECEIVE`, held
  only at `(T, slot)`; `T.endpoint_descriptors[slot] = Some(E)` and `E` joins
  `C.owned_endpoints`. The step unlocks `cpu`, `C`, `P`, and `T` and clears `prog`.

Stutters: CpuIdle (cpu not Running or killed), ContainerKilled, ContainerZombie, ProcessKilled, ThreadKilled, an
occupied descriptor (IpcEndpointTargetInUse), NoQuota.

## 6. mmap_4k — enter, directory/leaf steps, exit

Status: conforms (workspace run #27748; leaf-step IOMMU clause workspace run
#34522, monolith run #34523).

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
  executable entry owned by `C` whose page is in no process's
  `mapping_4k` of either its pagetable or its IOMMU table; `mapped` increases
  and `directory` resets to `None`.

**Exit** (`mmap_4k_exit_step_pre`, `mmap_4k_exit_step`)

- Pre: `mmap_4k_locked`, `prog is Mmap4k`, `mapped == R.len`, `directory is None`.
- Effect: unlocks `cpu`, `T`, and `PT(P)`; clears `prog`.

Trace: `range + 2 <= len <= 4 * range + 2`; enter, then directory or leaf
steps, then exit.

Stutters: argument errors, CpuIdle (cpu not Running or killed), ThreadKilled, NoQuota, a kernel-range VA (Error),
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

- Pre: `Caller`, `prog is None`; `!killed` for `T`, `P`, and `C`; `!C.zombie`;
  `Unlocked` for `cpu`, `C`, `P`, `PT(P)`, and `T`; `R.wf()`, `R.len > 0`, `UserVa(u, R)`;
  every VA of `R` is in `PT(P).mapping_4k`.
- Effect: write-locks the five objects; `prog = Unmap4k { R, 0, false }`.

**Leaf** (parameter `va`, the kernel's choice; R1)

- Pre: `unmap_4k_locked`, `prog is Unmap4k`, `unmapped < R.len`, `!flushed`,
  `va ∈ R`, `va` mapped in `PT(P)`.
- Effect: removes `va` from `PT(P).mapping_4k`; `unmapped + 1`.
- In the trace (`unmap_4k_leaf_trace_step`, without `va`): the new
  `mapping_4k` is the old one restricted to a subset of its domain whose
  complement is a finite set of exactly one key of `R`; `unmapped + 1`.


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

Stutters: argument errors, CpuIdle (cpu not Running or killed), ContainerKilled, ContainerZombie, ProcessKilled,
ThreadKilled, and an unmapped or kernel-range VA.

## 7a. iommu_map_4k — enter, directory/leaf steps, exit

Status: implemented (crate `veriflat_syscall_iommu_map_4k`;
`syscall_iommu_map_4k.rs`, `iommu_map_4k_range.rs`,
`iommu_map_4k_directory_step.rs`, spec `syscall_iommu_map_4k_spec.rs`);
verified, package run #34486, workspace run #34522, monolith run #34523. Boot
`NR_IOMMU_MAP_4K = 45`. Noninterference labels `IommuMap4kEnter`,
`IommuMap4kDirectory`, `IommuMap4kLeaf`, `IommuMap4kExit`
(`ni_iommu_map_4k.rs`, run #34521). `domain_4k_only`
(`noninterference/src/isolation.rs`) rules out 2M/1G entries in both tables
but allows 4K IOMMU entries, and `memory_iso` separates the two domains'
pages across every pair of page-table and IOMMU-table 4K entries.

Maps the pages mapped at `va_range` in `PT(P)` into `IT(P)` at `iova_range`,
as share_4k (§8) maps a page a second time.

- Arguments: `va`, `iova`, `range`; `VR = iommu_map_4k_syscall_range(va, range)`,
  `IR = iommu_map_4k_syscall_range(iova, range)`. Both are `VaRange4K`; `iova`
  needs `spec_va_4k_valid` (4K-aligned, L4 index at least
  `KERNEL_MEM_END_L4INDEX`), and only `VR` is checked against `UserVa`.
- U locks retained from enter to exit: `cpu`, `P`, `T` (write), `PT(P)`
  (read), `IT(P)` (write). `C` is not locked. Non-U: the existing 2M windows
  of `VR` (10007) for the whole call, the allocator of `C` and the new pages,
  and each mapped page's lock.
- Lock order: `cpu`, `P`, `T`, `PT(P)` (read), `IT(P)`, the windows of `VR`.
- Progress: `IommuMap4k { va_range: VR, iova_range: IR, mapped, directory }`.
- `iommu_map_4k_locked(u, cpu_id)`: `W` for `cpu`, `T`, `P`, and `IT(P)`;
  `PT(P)` read-locked.

**Enter** (`iommu_map_4k_enter_step_pre`, `iommu_map_4k_enter_step`)

- Pre: `Caller`, `prog is None`, `!thr.killed`, `!P.killed`, `C` present;
  `Unlocked` for `cpu`, `T`, `P`, and `IT(P)`; `PT(P)` not write-locked;
  `VR.wf()`, `IR.wf()`, `VR.len > 0`, `IR.len == VR.len`, `UserVa(u, VR)`;
  every VA of `VR` is in `PT(P).mapping_4k`, and no IOVA of `IR` is in
  `IT(P).mapping_4k`.
- Effect: write-locks `cpu`, `T`, `P`, and `IT(P)`, read-locks `PT(P)`;
  `prog = IommuMap4k { VR, IR, 0, None }`.

**Directory** (`iommu_map_4k_directory_step_pre`, `iommu_map_4k_directory_step`)

- Pre: `iommu_map_4k_locked`, `prog is IommuMap4k`, `mapped < IR.len`,
  `thr.quota_4k >= 1`.
- Effect: one 4K quota of `T` funds an IOMMU directory page; `directory`
  moves to a deeper level; `VR`, `IR`, and `mapped` are unchanged.

**Leaf** (`iommu_map_4k_leaf_step_pre`, `iommu_map_4k_leaf_step`)

- Pre: `iommu_map_4k_locked`, `prog is IommuMap4k`, `mapped < IR.len`,
  `VR[mapped]` mapped in `PT(P)`, `IR[mapped]` unmapped in `IT(P)`.
- Effect: `IT(P).mapping_4k[IR[mapped]] = PT(P).mapping_4k[VR[mapped]]`;
  `mapped + 1`, `directory = None`; no quota is consumed. In K the page
  gains `(IT(P), IR[mapped])` in `iommu_mappings` and `ref_count + 1`. The
  IOTLB is unchanged: `CAP.CM = 0` caches no non-present entry, so no
  invalidation is needed.

**Exit** (`iommu_map_4k_exit_step_pre`, `iommu_map_4k_exit_step`)

- Pre: `iommu_map_4k_locked`, `prog is IommuMap4k`, `mapped == IR.len`,
  `directory is None`.
- Effect: unlocks `cpu`, `T`, `P`, and `IT(P)`; drops `T`'s read lock on
  `PT(P)` (it ends Unlocked or ReadLocked); clears `prog`.

Trace (`iommu_map_4k_syscall_trace`): `range + 2 <= len <= 4 * range + 2`;
enter, then directory or leaf steps, then exit.

Stutters (in this order, `iommu_map_4k_syscall_result`): argument errors
(Error), CpuIdle (cpu not Running or killed), ProcessKilled, ThreadKilled,
PciNoIommuTable, NoQuota (`thr.quota_4k < 3 * range`: one 4K quota per IOMMU
directory level that may be missing), a kernel-range VA (Error),
IommuVaNotMapped, IommuIovaAlreadyMapped.

## 7b. iommu_unmap_4k — enter, leaf/flush/refund steps, exit

Status: implemented (crate `veriflat_syscall_iommu_unmap_4k`;
`syscall_iommu_unmap_4k.rs`, `_check.rs`, `_lock.rs`); verified, package run
#34434, workspace run #34522, monolith run #34523. Boot
`NR_IOMMU_UNMAP_4K = 46`. Noninterference labels `IommuUnmap4kEnter`,
`IommuUnmap4kLeaf`, `IommuUnmap4kFlush`, `IommuUnmap4kRefund`,
`IommuUnmap4kExit` (`ni_iommu_unmap_4k.rs`, run #34521).

- Arguments: `iova`, `range`; `IR = iommu_unmap_4k_iova_range(iova, range)`.
- U locks retained from enter to exit: `cpu`, `C`, `P`, `T`, `IT(P)`.
  Non-U: per removed page the page, cache, and pool locks as in §17 reclaim,
  and the allocator quota of `C` and its ancestors. The IOTLB flush takes no
  kernel lock.
- Lock order: `cpu`, `C`, `P`, `T`, `IT(P)`.
- Progress: `IommuUnmap4k { iova_range: IR, unmapped, flushed }`.
- `iommu_unmap_4k_locked(u, cpu_id)`: `W` for `cpu`, `T`, `P`, and `C`;
  `iommu_unmap_4k_table_locked` adds `W(IT(P))`.

**Enter** (`iommu_unmap_4k_enter_step_pre`, `iommu_unmap_4k_enter_step`)

- Pre: `Caller`, `prog is None`; `!killed` for `T`, `P`, and `C`; `!C.zombie`;
  `P.iommu_table is Some`; `Unlocked` for `cpu`, `C`, `P`, `T`, and `IT(P)`;
  `IR.wf()`, `IR.len > 0`, `UserVa(u, IR)`; every IOVA of `IR` is in
  `IT(P).mapping_4k`.
- Effect: write-locks the five objects; `prog = IommuUnmap4k { IR, 0, false }`.

**Leaf** (`iommu_unmap_4k_leaf_step_pre`, `iommu_unmap_4k_leaf_step`)

- Pre: `iommu_unmap_4k_table_locked`, `prog is IommuUnmap4k`,
  `unmapped < IR.len`, `!flushed`, `IR[unmapped]` mapped in `IT(P)`.
- Effect: removes `IR[unmapped]` from `IT(P).mapping_4k`; `unmapped + 1`. In
  K the leaf is only marked not present; `W(IT(P))` marks its attached
  domains dirty (§15).

**Flush** (`iommu_unmap_4k_flush_step_pre`, `iommu_unmap_4k_flush_step`)

- Pre: `iommu_unmap_4k_table_locked`, `prog is IommuUnmap4k`,
  `unmapped == IR.len`, `!flushed`.
- Effect: every `iommu_tlb` domain becomes empty and `flushed = true`;
  nothing else changes. K calls `flush_iommu_tlb_for_table`, then removes
  each hidden leaf and returns its page to its owner's 4K allocator cache in
  atomic sections that change no U state and stutter.

**Refund** (`iommu_unmap_4k_refund_step_pre`)

- Pre: `iommu_unmap_4k_locked`, `prog is IommuUnmap4k`, `unmapped == IR.len`,
  `flushed`.
- Effect: one container in `C` or `C.uppertree_seq` gains 4K quota
  (`kernel_u_container_quota_4k_increased`), as in §7.

**Exit** (`iommu_unmap_4k_exit_step_pre`, `iommu_unmap_4k_exit_step`)

- Pre: `iommu_unmap_4k_table_locked`, `prog is IommuUnmap4k`,
  `unmapped == IR.len`, `flushed`.
- Effect: unlocks the five objects; clears `prog`.

Trace (`iommu_unmap_4k_syscall_trace`):
`range + 3 <= len <= range + MAX_CONTAINER_TREE_DEPTH + 4`.

Stutters (in this order, `iommu_unmap_4k_syscall_result`): argument errors
(Error), CpuIdle (cpu not Running or killed), ContainerKilled,
ContainerZombie, ProcessKilled, ThreadKilled, PciNoIommuTable, and a
kernel-range or unmapped IOVA (IommuIovaNotMapped).

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

  In IpcPages, the caller sends when `peer.state` is `IPC_TRANSIT` with `wait`
  `Receive`; the sender and receiver are the caller and `peer` accordingly.
- Stability: publish records the child (or child container) in the origin, so
  no step relies on `children.last()`. The IPC peer stays locked by the caller.
  `share_4k_locked`, part of both pres, also requires `W(peer)` and `peer` in
  `IPC_TRANSIT` with partner `T` for origin IpcPages.

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

Noninterference: when the source process lies outside the observed domain
`x`, the `Share4kLeaf` hypothesis of the theorem (`noninterference/src/theorem.rs`)
requires that no process of the other domain maps the shared page in either
its pagetable or its IOMMU table 4K entries (run #34521).

## 9. new_process, new_process_with_endpoint, new_process_with_iommu_and_endpoint

Status: conforms (workspace run #27748). Steps: enter, publish, share steps,
finish.

- Arguments: `va`, `range`, `regs`, optional `endpoint_index`; the entry point
  fixes `with_iommu`. `base = 6` with IOMMU, otherwise `4`; the publish cost is
  `base - 1`.
- U locks: enter write-locks `cpu`, `P`, `PT(P)`, `T`, and the endpoint; the
  container `C` is never locked. Publish releases `P` and creates the child
  `D` and `PT(D)` (and its IOMMU table) write-locked. Finish releases the
  rest. Non-U: the PCID allocator (taken after `T`, held from enter to
  publish, guards `C.free_pcids`; the R5 exception), the scheduler, the
  allocator, and the staged pages. `C.owned_processes` is
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

Stutters: argument errors, CpuIdle (cpu not Running or killed), ProcessKilled, ThreadKilled, NoPcid, a missing
endpoint, NoQuota, and an unmapped or kernel-range source VA. new_process does
not check whether `C` is killed.

## 10. new_container, new_container_with_endpoint — enter, publish, share steps, finish

Status: conforms (new_container workspace run #27748; new_container_with_endpoint
workspace run #28754, monolith run #28755, noninterference run #28756).

- Arguments: `va`, `range`, `funding`, `process_quota`, `transfer_cpu`, `regs`;
  for the endpoint variant, `endpoint_index`.
- U locks: enter write-locks `cpu`, `C`, `CS(C)`, `P`, `PT(P)`, `T`, and
  `E(endpoint_index)` for the endpoint variant. Publish
  acquires and releases `transfer_cpu`, releases `CS(C)`, and creates the
  child container `CC` (with `CS(CC)` unlocked), its root process `D`, and
  `PT(D)` write-locked. Finish releases the rest. Non-U: the PCID allocator
  and 2M tails, the schedulers, and the staged pages.
- Progress: `NewContainer(NewContainerProgress { range, funding,
  process_quota, transfer_cpu, regs, endpoint_index, child_container: None })`,
  then `Share4k` whose origin is the same record with
  `child_container: Some(CC)`.

**Enter**

- Pre: `Caller`, `prog is None`; `!killed` for `C`, `P`, `T`; `!C.zombie`;
  `Unlocked` for `cpu`, `C`, `CS(C)`, `P`, `PT(P)`, `T`; `R.wf()`, `R.len > 0`,
  `R.len <= (usize::MAX - 9) / 3`, `UserVa(u, R)`; `transfer_cpu < NUM_CPUS`;
  `process_quota <= funding <= usize::MAX - 9 - 3 * R.len`;
  `C.depth < MAX_CONTAINER_TREE_DEPTH`;
  `thr.quota_4k >= 9 + funding + 3 * R.len` and `thr.quota_2m >= 2`; every VA
  of `R` is mapped in `PT(P)`; `cpu_array[transfer_cpu]` is Off and owned by `C`.
  For the endpoint variant, `edp_idx_valid(endpoint_index)`, the descriptor
  is present, and `Unlocked(E(endpoint_index))`.
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
  for `cpu`, `C`, `CC`, `P`, `PT(P)`, `D`, `PT(D)`, `T`, and the endpoint at
  the recorded `endpoint_index`.
- Effect: `kernel_u_new_thread_changed`: creates the root thread
  `D.owned_threads.last()` with `regs` and, for the endpoint variant, the
  endpoint in descriptor 0. It adds the thread to `CC.owned_threads` and the
  tail of `CC.scheduler[cpu_id]` (the caller's cpu id; `CC`'s own cpu
  `transfer_cpu` takes it with `rebalance_pull`, §4c), and charges `T` one 4K
  quota; unlocks `cpu`, `C`, `CC`, `P`, `PT(P)`, `D`, `PT(D)`, `T`, and the
  endpoint; clears `prog`.

Trace: `range + 3 <= len <= 4 * range + 3`.

Stutters: argument errors, CpuIdle (cpu not Running or killed), ContainerKilled, ContainerZombie, depth overflow,
ProcessKilled, ThreadKilled, a missing endpoint descriptor (Error), NoQuota,
a bad source range, IpcCpuOwnerMismatch, IpcCpuNotOff.

## 11. IPC ordinary: send/receive empty, no_block, cpu, pci — one step

Status: conforms (workspace run #27751; Pci payload workspace run #28638).

- Arguments: `endpoint_index`, the payload, the waiting direction fixed by the
  entry point, `regs`; K-internal label `flushed_default_pcid`.
- `IpcCaller(u, cpu_id, i)`: `Caller`, `prog is None`,
  `cpu.current_process == Some(P)`, `thr.state == RUNNING { cpu_id }`,
  `!thr.killed`, `edp_idx_valid(i)`, `E(i)` present,
  `T` not in `E(i).queue`, and `Unlocked` for `cpu`, `T`, `E(i)`. `P` is never
  locked: a killed caller process is caught by its killed thread.
- Stutters: CpuIdle (cpu not Running or killed), ThreadKilled, InvalidEndpoint, PeerKilled (a killed
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
  unequal lengths and SameProcess; for Pci, TypeMismatch unless both sides
  name the same B/D/F, SameProcess, IpcPciOwnerMismatch (the B/D/F is not in
  the sender process's `owned_pci_functions`), then Success for both sides.
  Success on an Endpoint or Pages payload
  takes no step here and enters §12 or §13; otherwise the syscall returns
  this result.
- Effect: `kernel_u_ipc_rendezvous_changed`: `peer` is dequeued and scheduled
  with `ipc_peer_result` on the wake shard `w`: `cpu_id` when `peer` is in
  `T`'s container, otherwise `peer.last_cpu`; it becomes `SCHEDULED { w }` at
  the tail of `scheduler[w]` of its container. The same wake shard rule
  applies to the §12 and §13 finish steps. For a CPU payload whose checks pass, the Off CPU
  moves to the receiver's container. For a Pci payload whose checks pass, the
  B/D/F moves from the sender process's `owned_pci_functions` to the
  receiver process's, its root-table owner becomes the receiver process, its
  `attached` bit is cleared, and its IOTLB domain `pci_bdf_did(bdf)` is
  emptied, whether or not it was attached. The root table lock (non-U) is
  taken after the peer thread once SameProcess has passed and is released in
  the step.

## 11a. IPC call: call, call_usize, receive_call, reply_and_receive, reply_and_receive_usize — one step

Status: conforms (focused runs #28796–#28804; handoff: workspace #28805, monolith #28806, noninterference #28807, all 0 errors).

Synchronous call/reply over an endpoint between threads of one container,
with the CPU handed directly between caller and callee. `call` enters `E(i)`
in the CALLING direction, `receive_call` and `reply_and_receive` in the
RECEIVING_CALL direction (`is_endpoint_send_waiting`: CALLING sends,
RECEIVING_CALL receives; the queue direction is SEND for queued senders and
callers, RECEIVE for queued receivers and receive-callers).

- Arguments: `endpoint_index`, the payload (`Empty` for `call`,
  `receive_call`, and `reply_and_receive`; `Usize { value }` for the
  `_usize` entries), `regs`; K-internal label `flushed_pcid`, as §4.
- Payloads are not type-checked between a call and its acceptance: a
  `call` and a `call_usize` are both accepted by `receive_call`. A delivered
  `Empty` returns Success and `Usize { value }` returns
  `SuccessUsize { value }` (`ipc_call_result`). A reply value is never
  queued: it is written into the caller's frame by the trap layer when the
  CPU is handed back.
- Entry (`ipc_entry_result` with the call directions, and
  `ipc_reply_entry_result` for `reply_and_receive`): ThreadKilled;
  ReplyOutOfPhase when a RECEIVING_CALL entry already records a caller, or a
  `reply_and_receive` records none; InvalidEndpoint; then block for `call`
  and `receive_call`, and SameDirection for `reply_and_receive` when
  `E(i).queue` holds senders or callers; PeerKilled (the killed head, or the
  killed recorded caller, stays where it is).
- Five user entries share three exec functions: `syscall_call` (`call`,
  `call_usize`), `syscall_receive_call`, and `syscall_reply_and_receive`
  (`reply_and_receive`, `reply_and_receive_usize`).

**Block** (`call`, `receive_call`)

- As §11 Block with waiting state CALLING or RECEIVING_CALL; a
  `receive_call` queues with the `Empty` payload.

**Rendezvous error** (`call`, `receive_call`)

- Pre: as §11 Rendezvous.
- Result (`ipc_rendezvous_result`): a `call` meeting a RECEIVING_CALL head,
  or a `receive_call` meeting a CALLING head, returns CallAcrossContainers
  (the handoff below applies when the head is of the caller's container);
  any other head returns TypeMismatch. Both sides get the result.
- Effect: `kernel_u_ipc_rendezvous_changed`, as §11.

**IpcCallHandoff** (`call`)

- Pre (`ipc_call_handoff_step_pre`): `IpcCaller`, `T.callee is None`, the
  head `S = E(i).queue[0]` waits in the RECEIVE direction, differs from `T`,
  is present and unlocked, `!S.killed`, `S.state is RECEIVING_CALL`,
  `S.caller is None`, `S.callee is None`, `S` blocks on `E(i)`, `S` is of
  `T`'s container, and `S.owning_proc` is present.
- Effect: `kernel_u_ipc_call_handoff_changed`: `S` is dequeued, becomes
  `RUNNING { cpu_id }` with `caller = Some(T)`, `last_cpu = cpu_id`, no
  blocking endpoint, and no saved frame; `T` saves `regs`, becomes
  WAITING_REPLY with `callee = Some(S)`; the CPU's current process and
  thread become `S`'s; the `(cpu_id, pcid)` TLB entry is flushed when
  `flushed_pcid` is `Some(pcid)`. The syscall returns `ipc_call_result` of
  the call payload, delivered to `S`.

**IpcAcceptCall** (`receive_call`)

- Pre (`ipc_accept_call_step_pre`): `IpcCaller`, `S.caller is None`,
  `S.callee is None`, the head `T = E(i).queue[0]` waits in the SEND
  direction, differs from `S`, is present and unlocked, `!T.killed`,
  `T.state is CALLING`, `T.callee is None`, `T` blocks on `E(i)`, and `T` is
  of `S`'s container.
- Effect: `kernel_u_ipc_accept_call_changed`: `T` is dequeued, becomes
  WAITING_REPLY with `callee = Some(S)` and no blocking endpoint, and is not
  scheduled; `S` records `caller = Some(T)` and keeps running. The syscall
  returns `ipc_accept_call_result`: `ipc_call_result` of `T`'s payload.

**IpcReplyHandoff** (`reply_and_receive`)

- Pre (`ipc_reply_handoff_step_pre`): `IpcCaller`, `S.caller == Some(T)`,
  `S.callee is None`, `E(i).queue` is empty or waits in the RECEIVE
  direction, `T` differs from `S`, is present and unlocked, `!T.killed`,
  `T.state is WAITING_REPLY`, `T.callee == Some(S)`, `T` is of `S`'s
  container, and `T.owning_proc` is present.
- Effect: `kernel_u_ipc_reply_handoff_changed`: `T` becomes
  `RUNNING { cpu_id }` with `callee = None`, `last_cpu = cpu_id`, and no
  saved frame; `S` saves `regs`, becomes RECEIVING_CALL with
  `caller = None` and the `Empty` payload, and is queued at the tail of
  `E(i)`, whose direction becomes RECEIVE when it was empty; the CPU's
  current process and thread become `T`'s; the `(cpu_id, pcid)` TLB entry
  is flushed when `flushed_pcid` is `Some(pcid)`. The syscall returns
  `ipc_call_result` of the reply payload, delivered to `T`.

Locks: `cpu`, then the current thread, then `E(i)`, then the peer (the head
or the recorded caller; a WAITING_REPLY caller is locked under its callee's
thread lock), then `pcid_needflush` for a handoff. No process lock.

## 12. IPC endpoint — transit, finish

Status: conforms (workspace run #27613, monolith run #27612).

- Arguments: `endpoint_index` (the channel), `payload_index`, the direction.
- U locks: transit acquires `cpu`, `T`, `peer` (retained) and the channel
  (released inside the step). Finish acquires and releases the payload
  endpoint. Non-U: the wake shard (§11) of the peer's scheduler.
- Progress: `IpcEndpoint { peer, caller_sends, payload_index }`. The sender is
  `T` when `caller_sends`, otherwise `peer`; the receiver is the other one. The
  source index is `payload_index` on the caller's side and the peer's
  `ipc_payload.endpoint_index` on the peer's side; the target index is the
  other one. The payload endpoint is the sender's descriptor at the source
  index.
- Transit state: from transit to finish `peer` is `IPC_TRANSIT { partner: T,
  wait }`, where `wait` is `Send` when `peer` was SENDING and `Receive`
  otherwise. `thread_ipc_transit_wf` (in `thread_perms_wf`) states for every
  thread `d` in `IPC_TRANSIT { partner: t, .. }`: `d` is write-held and not
  marked for kill, `t` is present and RUNNING, and `progress_peer_of(t.prog) ==
  Some(d)`. The pages rendezvous (§13) uses the same state; the single-step
  rendezvous paths (§11, §11a) never enter it.

**Transit**

- Pre: the §11 rendezvous pre for the channel; `edp_idx_valid(payload_index)`;
  the peer waits in the opposite direction with an Endpoint payload; the
  source descriptor is present and the target descriptor is empty.
- Effect: write-locks `cpu`, `T`, `peer`; dequeues `peer` into
  `IPC_TRANSIT { partner: T, wait }` with no blocking endpoint; records
  `IpcEndpoint`.

**Finish**

- Pre: `prog is IpcEndpoint`; `W` for `cpu`, `T`, `peer`; `peer` is
  `IPC_TRANSIT` with partner `T`; the payload endpoint is present and
  `Unlocked`.
- Result (`ipc_endpoint_finish_result`): Success when the payload endpoint's
  container is the receiver's container or in its `uppertree_seq`, otherwise
  EndpointOwnerMismatch. The syscall returns this result.
- Effect: on Success the receiver's descriptor at the target index becomes the
  payload endpoint and the endpoint gains that owner. `peer` leaves transit: it
  is scheduled with the result and an Empty payload and joins the wake shard
  (§11) of its container's scheduler. The
  step unlocks `cpu`, `T`, `peer`, and the payload endpoint and clears
  `prog`.

Single rendezvous error steps (§11): EndpointSourceInvalid,
EndpointTargetInUse, TypeMismatch.

## 13. IPC pages — enter, lock tables, check, share steps, unlock tables, finish

Status: conforms (workspace run #27816).

- Arguments: `endpoint_index` (the channel), `va`, `range`, `regs`; the entry
  point fixes the direction. `R = VaRange4K { start: va, len: range }` is the
  caller's payload. `regs` and the K-internal `flushed_default_pcid` serve only
  the §11 block step. Lock tables, check, and finish also take
  `endpoint_index`; the other later steps take only `cpu_id`.
- U locks: enter write-locks `cpu`, `T`, `peer`, and the channel
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
- Derivation: `peer` is recorded in `prog` and is `IPC_TRANSIT { partner: T,
  wait }` (§12) from enter to finish; the channel is `T`'s descriptor at
  `endpoint_index`; the caller sends exactly when `wait` is `Receive`
  (`ipc_pages_sender`, `ipc_pages_receiver`, `share_4k_objects`); the source and
  target processes are the sender's and receiver's `owning_proc`. These hold
  until finish because `peer` stays write-locked in transit and `T` stays
  write-locked.
- `ipc_pages_held(u, cpu_id, endpoint_index)`: `prog is IpcPages`; `cpu`,
  `cpu.current_process`, `T`, `peer`, and the channel are present and `W`;
  `peer` is `IPC_TRANSIT` with partner `T`; `edp_idx_valid(endpoint_index)`.
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
- Effect: write-locks `cpu`, `T`, `peer`, and the channel; dequeues `peer` from
  the channel into `IPC_TRANSIT { partner: T, wait }` with no blocking
  endpoint;
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
  requires `peer` present, `W`, and `IPC_TRANSIT` with partner `T`), origin
  IpcPages, `shared == len`;
  the source and target processes named by `share_4k_objects` differ, are
  present with page tables, and both tables are `W`.
- Effect: both tables become Unlocked;
  `prog = IpcPages { source_range, target_range, peer, locked: false, released: Some(Success) }`.

**Finish** (`ipc_pages_finish_step_pre`, `ipc_pages_finish_step`)

- Pre: `ipc_pages_held`, `!locked`, `released is Some`, and `peer`'s container
  is present.
- Effect: `peer` leaves transit and becomes SCHEDULED with no blocking
  endpoint, an Empty payload, and the recorded result as `error_code`; it joins
  the wake shard (§11) of its container's scheduler. The step unlocks `cpu`,
  `T`, `peer`, and the channel and clears `prog`. The syscall returns the same
  result.

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

Stutters: argument errors (Error before any step), CpuIdle (cpu not Running or killed), ThreadKilled,
InvalidEndpoint, and PeerKilled.

Noninterference (§12, §13): `inflight_iso` (`noninterference/src/isolation.rs`)
is keyed on the peer's state: a thread in `IPC_TRANSIT` whose live partner
belongs to one domain lies outside the other domain. The user fact
`kernel_u_ipc_transit_wf` (`noninterference/u_facts/src/ownership.rs`), proved
from `thread_ipc_transit_wf` by `kernel_wf_implies_u_ownership_wf`, gives every
transit thread a live RUNNING partner whose progress names it, so the reclaim
and exit steps need no assumption. The endpoint finish pre and
`share_4k_locked` (share, downgrade, and unlock-tables steps) state that the
recorded peer is `IPC_TRANSIT` with partner `T`, and `ipc_pages_held` states
`edp_idx_valid(endpoint_index)`; the proof assumes nothing beyond the step
specifications.

## 14. Syscall entry list

| Entry point | Section |
|---|---|
| `syscall_alloc_quota_4k`, `syscall_alloc_quota_2m` | §3 |
| `syscall_alloc_thread_quota_4k`, `syscall_alloc_thread_quota_2m` | §3a |
| `syscall_schedule` | §4 |
| `syscall_cpu_offline_request`, `syscall_cpu_online`, `syscall_cpu_offline_request_child`, `syscall_cpu_online_child` | §4a |
| `cpu_offline_check` (trap-layer entry, before every `syscall_schedule`) | §4b |
| `cpu_online_resume` (trap-layer IPI entry of a halted cpu) | §4b |
| `rebalance_pull` (trap-layer entry of an Idle cpu after `syscall_schedule` returns Idle) | §4c |
| `syscall_new_thread`, `syscall_new_thread_with_endpoint` | §5 |
| `syscall_new_endpoint` | §5a |
| `syscall_mmap_4k` | §6 |
| `syscall_unmap_4k` | §7 |
| `syscall_iommu_map_4k` | §7a |
| `syscall_iommu_unmap_4k` | §7b |
| `syscall_new_process`, `syscall_new_process_with_endpoint`, `syscall_new_process_with_iommu_and_endpoint` | §9 |
| `syscall_new_container`, `syscall_new_container_with_endpoint` | §10 |
| `syscall_send_empty`, `syscall_receive_empty`, `syscall_send_empty_no_block`, `syscall_receive_empty_no_block`, `syscall_send_cpu`, `syscall_receive_cpu` | §11 |
| `syscall_send_endpoint`, `syscall_receive_endpoint` | §11, §12 |
| `syscall_send_pages`, `syscall_receive_pages` | §11, §13 |
| `syscall_send_pci`, `syscall_receive_pci` | §11 |
| `syscall_call` (`call`, `call_usize`), `syscall_receive_call`, `syscall_reply_and_receive` (`reply_and_receive`, `reply_and_receive_usize`) | §11a |
| `syscall_pci_attach_dma` | §4d |
| `syscall_thread_exit` | §17 |
| `syscall_kill_process` | §18 |
| `syscall_kill_container` | §19 |

## 15. Approved representation changes

These changes were approved on 2026-09-29 and are all applied.

| Variant | Current | Approved | Needed by |
|---|---|---|---|
| `NewThread` | applied | `{ regs, endpoint_index: Option<EndpointIdx> }` | new_thread finish (R1, R4) |
| `NewEndpoint` | applied | `{ slot: EndpointIdx }` (added 2026-10-10 with new_endpoint) | new_endpoint finish |
| `NewProcess` | applied | `NewProcess(NewProcessProgress { range, regs, endpoint_index, with_iommu, child: Option })` | publish, finish |
| `NewContainer` | applied | `NewContainer(NewContainerProgress { range, funding, process_quota, transfer_cpu, regs, endpoint_index: Option<EndpointIdx>, child_container: Option })` (`endpoint_index` added with new_container_with_endpoint) | publish, finish |
| `Share4k` | applied | adds `origin: NewProcess(NewProcessProgress) \| NewContainer(NewContainerProgress) \| IpcPages { peer }` | share steps, finish, IPC pages unlock tables |
| `IpcEndpoint` | applied | `{ peer, caller_sends, payload_index }` | finish |
| `IpcPages` | applied | `{ source_range, target_range, peer, locked: bool, released: Option<RetValueType> }` (`locked` approved 2026-09-30) | lock tables, check, unlock tables, finish |
| `ThreadExit` | applied | `{ next: EndpointIdx }` (added 2026-10-12 with thread_exit) | thread_exit drop steps, finish (§17) |
| `IommuMap4k` | applied | `{ va_range, iova_range, mapped, directory: Mmap4kDirectory }` (added with iommu_map_4k) | iommu_map_4k directory, leaf, exit steps (§7a) |
| `IommuUnmap4k` | applied | `{ iova_range, unmapped, flushed: bool }` (added with iommu_unmap_4k) | iommu_unmap_4k leaf, flush, refund, exit steps (§7b) |

`ContainerU.cpu_set_lock` (approved 2026-09-30) projects the container's
CPU-set lock mode; new_container (§10) and IPC Cpu (§11) state it.

`ContainerU.cpu_offline_requests: Seq<bool>` (approved 2026-10-03 with the cpu
hotplug plan) projects the container's per-cpu offline request table
(`cpu_offline_requests_of(cpu_offline_mp[cpu_offline_flags_ptr(c)])`); the
table lives in the second 4K of the container's 2M page, its cells are locked
per cpu (major 104) and are not U-visible. new_container publishes it all-false
(§10); cpu_offline_request and cpu_offline_request_child set one bit (§4a);
cpu_offline_check clears it when the cpu goes Off (§4b).

Kernel representation changes for cpu hotplug (approved 2026-10-03, applied):
`KernelK.cpu_offline_mp: UnLockedMap<RwLockCpuOfflineFlagsPtr, CpuOfflineFlags>`
holds every container's table at `cpu_offline_flags_ptr(c) = c + 4096`, with
`cpu_offline_flags_wf` (cells aligned, `Off ⇒ !requested`) and
`container_cpu_offline_flags_wf` (container ↔ table); the cell locks form the
new family `CPU_OFFLINE_FLAG_LOCK_MAJOR = 104` (`KernelObjId::CpuOfflineFlag`,
`LocalContext.cpu_offline_flag_lock_map`). The major lies above the container
lock (101) and below the process lock (105), so a parent's container lock
precedes a child's request cell (§4a), and the container and PCID allocator
(107) locks require that no request cell is held.

`Cpu.hw_halted: Ghost<bool>`
(`CpuView.hw_halted`) records whether the hardware is halted: set when the cpu
publishes Off (§4b), cleared by `cpu_online_resume`; it is not U-visible and
no invariant depends on it. Trusted primitives: `CpuTLB::flush_all_local_pcids`
(external_body; empties every TLB entry of the calling cpu except
`KERNEL_DEFAULT_PCID`), `send_ipi`, `halt_until_ipi` (empty stubs).

Per-cpu scheduler shards (approved 2026-10-07, applied):
`ContainerU.scheduler: Seq<Seq<RwLockThreadPtr>>` has one run queue per cpu id
(`scheduler_shards_of(sched_mp[c.scheduler])`); `ThreadState::SCHEDULED { cpu_id }`
names the shard holding the thread; `Thread.last_cpu` / `ThreadU.last_cpu`
records the cpu that last ran it (new_thread sets the creating cpu, boot root
0). In K, `Scheduler { shards: LockedArray<SchedulerShard, NUM_CPUS>, owning_container }`
lives in `KernelK.sched_mp: SchedulerUnLockedMap`; shard `c` is locked with
major `SCHEDULER_LOCK_MAJOR` and minor `c` (`KernelObjId::SchedulerShard(s, c)`,
`LocalContext.scheduler_lock_map`), so one container's shards are taken in
cpu-id order. `container_thread_scheduler_wf` aligns
`t.state == SCHEDULED { c }` with membership in shard `c` of `t`'s container;
it says nothing about Off or unowned cpus.

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

PCI device ownership (approved 2026-10-08, applied):
`KernelK.irt: IommuRootTableLock = RwLock<IommuRootTable, (), (), NO_KILL_STATE>`
locks the whole root table with the new family
`IOMMU_ROOT_TABLE_LOCK_MAJOR = PAGE_TABLE_LOCK_MAJOR + 1`, directly below
`IOMMU_TABLE_LOCK_MAJOR` (swapped on 2026-10-12 so that exit can write-lock
its IOMMU table while it holds the root table, §17)
(`KernelObjId::IommuRootTable(table_base)`,
`LocalContext.iommu_root_table_lock_map`); the lock is taken and released
inside one step and is not U-visible. It also serializes each process's
reverse set: `ProcessGhost.owned_pci_functions` (lock-free ghost;
the exec `pci_function_ref_counter` is gone) is aligned with the root table's
owners by `process_pci_function_ownership_wf` (its zombie clause was dropped
on 2026-10-12: a zombie keeps its PCI functions until kill or reap, §16 item
10). `ProcessRO.iommu_cr3` mirrors the root of the process's IOMMU table
(`process_iommu_table_match`), so attach never locks that table. New exec
root-table operations: `set_owner`, `attach`, `detach`, `is_attached`.
Trusted primitive: `IommuTLB::invalidate_domain` (external_body; empties one
VT-d domain under the root table lock). New results: `ErrorIpcPciOwnerMismatch`,
`ErrorPciOwnerMismatch`, `ErrorPciNoIommuTable`, `ErrorPciAlreadyAttached`.

IOTLB dirty marker (applied; `iommu_table_lock_wf` is deleted): the IOMMU
table's write lock is the dirty marker. `iommu_tlb_wf_spec` keeps every
attached BDF's domain a subset of its owner's IOMMU table, and of its present
leaves when that table is not write-locked
(`single_tlb_subset_of_present_pagetable`). A write holder may hide leaves of
an attached table; `iommu_table_tlb_entries_present(iommu_tlb, root_table,
it_mp, it)` is the per-table flushed fact, and `kernel_step_boundary_raw` and
the step-boundary wrappers keep it for write-held IOMMU tables (TCB: a write
holder's hidden leaves are never re-cached, `CAP.CM = 0`). Approved trusted
primitive: `IommuTLB::flush_all_iotlb` (external_body; empties every domain,
keeps the context cache, takes no kernel lock; the boot hook
`veriflat_iommu_flush_all_iotlb` shares a platform spinlock with
`veriflat_iommu_invalidate_domain`), wrapped by the K helper
`flush_iommu_tlb_for_table`. `wlock_iommu_table` no longer needs the process
lock or detached functions, `wunlock_process` no longer needs the IOMMU table
released, and `syscall_pci_attach_dma` does not reason about the table lock.
New results: `ErrorIommuVaNotMapped`, `ErrorIommuIovaAlreadyMapped`,
`ErrorIommuIovaNotMapped`.

## 16. Decisions

1. Later steps read syscall arguments from `prog` (R1), using the §15 fields.
2. The unmap flush PCID comes from `ProcessU.pcid`.
3. The user-VA bound is `KernelU.kernel_l4_end`, compared through `UserVa`.
4. CPU hotplug (2026-10-03): offline requests are per-container cells locked
   per cpu (major 104, held through the whole offline); no permission check
   beyond container ownership of the target; the target cpu offlines itself in
   `cpu_offline_check` right before each schedule, requeueing its running
   thread and deferring to `syscall_schedule` when that thread or its process
   is killed; `syscall_cpu_online` publishes Idle and sends the IPI, and the
   woken cpu only clears `hw_halted` (re-halting while still Off); there is no
   `Offlining` state.
5. Scheduler shards (2026-10-07): every enqueue goes to the acting cpu's shard
   (schedule requeue, new_thread, cpu_offline_check, same-container IPC wake,
   new_container's root thread); a cross-container IPC wake goes to the peer's
   `last_cpu` shard; an Idle cpu pulls only the head of the lowest other
   non-empty shard of its container and stutters on a killed head. Shards of
   Off or unowned cpus may hold threads; they drain only through
   `rebalance_pull`.
6. PCI devices (2026-10-08): the root table is one lock that also guards the
   per-process PCI sets; it never crosses a step boundary, so it is not
   U-visible. The IOTLB is guarded by no kernel lock: a write-locked IOMMU
   table marks its attached domains dirty, and its holder flushes the IOTLB
   before unlocking (§15). An IPC Pci transfer needs both sides to name the same
   B/D/F, is not restricted to one container (the endpoint is the
   authority), and always detaches the function and empties its IOTLB domain.
   `syscall_pci_attach_dma` attaches a function to its owner's IOMMU table;
   there is no detach syscall.
7. Parent cpu hotplug (2026-10-10): a container may offline or online a cpu of
   a direct child, named by its index in `children`, through
   `syscall_cpu_offline_request_child` and `syscall_cpu_online_child`; deeper
   descendants are not supported. Each call is one two-phase-locked section
   that locks `cpu`, then the caller's container (rejecting a killed one),
   then the child's request cell and CPU-set lock, as the own variants do.
   The own variants are unchanged.
8. Endpoint creation (2026-10-10): `syscall_new_endpoint` creates an empty
   receive endpoint of the caller's container at an empty descriptor of the
   caller, funded by one 4K quota of the calling thread; an occupied
   descriptor returns the existing `ErrorIpcEndpointTargetInUse`. It holds the
   container lock while the page is allocated, as new_container does.
9. Synchronous call (2026-10-11): `call`, `receive_call`, and
   `reply_and_receive` hand the CPU directly between a caller and a callee of
   one container (§11a); a cross-container call meets a rendezvous error
   (CallAcrossContainers) rather than a handoff. Payloads are `Empty` or one
   usize, not type-checked between call and acceptance; the reply value goes
   straight into the caller's frame. `reply_and_receive` with no recorded
   caller stutters with ReplyOutOfPhase, with queued senders or callers with
   SameDirection (keeping its caller), and with a killed caller with
   PeerKilled. There is no plain reply: a server leaves its receive-call wait
   only by being called or by a rendezvous error. The call entries hold no
   process lock; a WAITING_REPLY caller is locked under its callee's lock.
10. Thread exit and zombie semantics (2026-10-12): `syscall_thread_exit`
    removes the running thread (§17). When a process's last thread exits,
    the same call first reclaims the process's user memory: it unmaps every
    user 4K mapping of the process's page table (the table structure stays),
    flushes the process's PCID from every cpu once, returns the thread's and
    the process's quota of every size to their container, and releases the
    process's PCID to its container's PCID allocator. It also detaches every
    attached function the process owns, emptying each one's IOTLB domain, and
    unmaps every 4K mapping of the process's IOMMU table: it hides every leaf,
    flushes the whole IOTLB once, then removes the leaves. The zombie keeps its page
    table and IOMMU table structures and owns its PCI functions for kill or
    reap; it holds no quota and no PCID, so its PCID and CR3 never enter a
    cpu's dirty map again. A zombie root process makes its container a zombie.

    Only the seven container-locking syscalls (alloc_quota_4k,
    alloc_quota_2m, unmap_4k, new_endpoint, new_container with its endpoint
    variant, cpu_offline_request_child, cpu_online_child) stutter with
    ContainerZombie; exit locks its container but does not stutter on a
    zombie. A callee that exits while serving a call wakes its caller with
    the new `ErrorIpcCalleeExited` on shard `cpu_id` of the container's
    scheduler, and a killed caller makes the exit stutter with PeerKilled.
    The caller is locked after the callee because a blocked caller's lock
    major (THREAD_BLOCKED, 10003) is above a running callee's (106). Each
    descriptor that holds an endpoint is released in its own step, and the
    exiting thread's page returns to the 4K allocator of the container that
    owns the page.

## 17. thread_exit — enter, drop steps, reclaim, finish

Status: implemented, including zombie reclaim of 4K mappings, quota, and the
PCID (stage A) and of PCI attachments and IOMMU 4K mappings (stage B).
Verified: thread_exit focused run #29094, workspace run #29101, monolith run
#29105, noninterference run #29108.


- Arguments: none; the running thread `T` of `cpu_id` exits. The trap layer
  checks nothing.
- Result: CpuIdle unless the call stutters (`thread_exit_syscall_result`).
  The idle cpu then runs the trap layer's `run_idle` (offline check,
  schedule, rebalance_pull), as after an IPC block.
- U locks retained from enter to finish: `cpu` (major 1), `C` (101), `P`
  (105), and `T` (106). When `T` is `P`'s last thread, reclaim also holds
  `PT(P)` (10004) and, when `P` has one, its IOMMU table `IT(P)` (10006) from
  its lock-table step to its unlock-table step. Finish
  releases `cpu`, `C`, and `P`; `T`'s lock goes with `T`. Enter acquires and
  releases the caller `R` (blocked-thread major 10003), and each drop step
  acquires and releases `E(index)` (10001).
- Non-U: in enter, when `R` exists, shard `cpu_id` of `C`'s scheduler
  (10011). In the lock-table step, the root table (10005), released inside
  the step once `IT(P)` is locked. In reclaim, per unmapped CPU or IOMMU
  page: the page (mapped-page major
  10009, moved to the free-page major once it is `Free4k`), shard `cpu_id`
  of its owner's 4K allocator cache (10012), and that allocator's pool
  (10015, only to drain a full cache); per flushed cpu, its `(cpu', pcid)`
  needflush cell (30001); and the 4K, 2M, and 1G allocator quota of `C`
  and of its ancestors (20002, 20003, 20004), one at a time. In finish: for
  `P`'s last thread, `C`'s PCID allocator (107) before anything else; `T`'s page
  (allocated-page major 1000), shard `cpu_id` of the 4K allocator cache of
  the page's owner (10012), that allocator's global pool (10015, only to
  drain a full cache), its quota (20002), and the
  `(cpu_id, KERNEL_DEFAULT_PCID)` needflush cell (30001). `update_lock_id`
  moves the woken `R` to the scheduled-thread major (20001), the page to the
  free-page major (30000) once it is `Free4k`, and the idle cpu to major 2;
  each is then released under its new id and not re-acquired.
- Lock order: `cpu`, `C`, `P`, `T`; then `R` and the shard in enter,
  `E(index)` in a drop step, `PT(P)`, the root table, `IT(P)`, and the
  per-page, needflush, and quota locks in reclaim, and the PCID allocator,
  page, cache, pool, quota, and
  needflush cell in finish.
- Progress: `ThreadExit { next }` from enter through the drop steps; every
  descriptor below `next` is empty. Enter records `next = 0`. For `P`'s last
  thread, reclaim records `ThreadExitReclaim { flushed }`, then
  `ThreadExitQuota { returned }` after each size of quota, then
  `ThreadExitZombie` once `PT(P)` and `IT(P)` are unlocked.
- Derivation: every step reads `C` as `cpu.owning_container`, `P` as
  `cpu.current_process->Some_0`, and `T` as `cpu.current_thread->Some_0`;
  `W(cpu)` keeps them stable until finish. `R = thr.caller->Some_0` and
  `E(index)` are read under `W(T)`.

**Enter** (`thread_exit_enter_step_pre`, `thread_exit_enter_step`)

- Pre: `Caller`, `prog is None`, `cpu.current_process == Some(P)`,
  `thr.owning_proc == P`, `thr.owning_container == C`,
  `thr.state == RUNNING { cpu_id }`, `!C.killed`, `!P.killed`, `!thr.killed`;
  `Unlocked` for `cpu`, `C`, `P`, and `T`; when `thr.caller == Some(R)`: `R`
  present, `Unlocked(R)`, `!R.killed`, and `R.state is WAITING_REPLY`. The
  invariant `thread_caller_callee_wf` gives `thr.callee is None`,
  `R.callee == Some(T)`, and `R.owning_container == C`; the pre does not
  state them. `C.zombie` is not checked.
- Effect: write-locks `cpu`, `C`, `P`, and `T`. When `R` exists, `R` becomes
  `SCHEDULED { cpu_id }` with `callee = None` and
  `error_code = Some(ErrorIpcCalleeExited)` (its call returns it when `R`
  next runs) and joins the tail of `scheduler[cpu_id]` of its container `C`,
  and `thr.caller = None`. `prog = ThreadExit { next: 0 }`.

**Drop** (`thread_exit_drop_step_pre`, `thread_exit_drop_step`)

- Pre: `prog is ThreadExit { next }`; `W` for `cpu`, `C`, `P`, and `T`. The
  step relation fixes `index` as the first descriptor at or after `next` that
  holds an endpoint, and requires `E(index)` present and `Unlocked`. Empty
  descriptors take no step.
- Effect: `thr.endpoint_descriptors[index] = None`; `E(index).owning_threads`
  loses `(T, index)` (in K its `rf_counter` drops by one);
  `prog = ThreadExit { next: index + 1 }`. The endpoint stays in the endpoint
  map, even with no holder left.

**Reclaim** (only when `P.owned_threads.len() == 1`; `unmap_4k_locked` means
`W` for `cpu`, `T`, `P`, `PT(P)`, and `C`, as in §7)

- Lock table (`thread_exit_lock_table_step_pre`, `thread_exit_lock_table_step`):
  pre `prog is ThreadExit`, `thr.caller is None`, every descriptor `None`,
  `W` for `cpu`, `C`, `P`, and `T`, `P.owned_threads.len() == 1`, and
  `PT(P)` and, when present, `IT(P)` `Unlocked`; effect: write-locks `PT(P)`
  and `IT(P)`, clears `iommu_root_table.attached` of every function that `P`
  owns (owners are unchanged), empties the IOTLB domain `pci_bdf_did` of each
  function it detached, and sets `prog = ThreadExitReclaim { flushed: false }`.
  K scans all 65,536 B/D/Fs under the root table lock. The root table lock is
  taken after `PT(P)` and released after `IT(P)` is locked, inside the step.
- Leaf (`thread_exit_leaf_step`): pre `unmap_4k_locked` and
  `prog == ThreadExitReclaim { flushed: false }`; effect: exactly one valid
  user 4K mapping (the kernel chooses the VA, R1) leaves `PT(P)`. In K the
  leaf's entry is only marked not present; the page is freed after the
  flush.
- Flush: pre `thread_exit_flush_step_pre` (a leaf pre with no valid user 4K
  mapping left in `PT(P)`); effect: exactly one `(cpu', P.pcid)` TLB entry
  becomes empty (`kernel_u_cpu_tlb_cleared`). The PCID is flushed once, from
  every cpu, after all leaves.
- Flushed (`thread_exit_flushed_step`): pre as for flush; effect:
  `prog = ThreadExitReclaim { flushed: true }`.
- Refund: pre `unmap_4k_locked` and `prog == ThreadExitReclaim { flushed: true }`;
  effect: one container in `C` or `C.uppertree_seq` gains 4K quota
  (`kernel_u_container_quota_4k_increased`). Before the refunds, K removes
  each cleared entry and returns its page to its owner's 4K allocator cache
  in atomic sections that change no U state and stutter, accumulating the
  refund in the thread's pending quota. The IOMMU leaf steps follow the CPU
  refunds, then one IOMMU flush step, then their own refunds.
- IOMMU leaf (`thread_exit_iommu_leaf_step`): pre `unmap_4k_locked`,
  `prog == ThreadExitReclaim { flushed: true }`, and `IT(P)` write-locked;
  effect: exactly one 4K mapping (the kernel chooses the IOVA) leaves `IT(P)`.
  In K the leaf is only marked not present; `IT(P)`'s write lock marks its
  attached domains dirty (§15).
- IOMMU flush (`thread_exit_iommu_flush_step`, NI label
  `ThreadExitIommuFlush`): pre as for an IOMMU leaf;
  effect: every `iommu_tlb` domain becomes empty and nothing else changes. K
  runs it once, after every IOMMU leaf is hidden
  (`flush_iommu_tlb_for_table`), then removes each hidden leaf and returns
  its page in atomic sections that change no U state and stutter, as for a
  CPU leaf.
- Quota (`thread_exit_quota_step_pre`, `thread_exit_quota_step`): pre
  `unmap_4k_locked` and `prog` is `ThreadExitReclaim { flushed: true }`,
  `ThreadExitQuota { returned: 4K }`, or `ThreadExitQuota { returned: 2M }`;
  effect: the next size `S` (4K, then 2M, then 1G) moves the whole `quota_S`
  of `T` and of `P` to `C`, zeroes both, and sets
  `prog = ThreadExitQuota { returned: S }`.
- Unlock table (`thread_exit_unlock_table_step_pre`,
  `thread_exit_unlock_table_step`): pre `unmap_4k_locked`,
  `prog == ThreadExitQuota { returned: 1G }`, no valid user 4K mapping left in
  `PT(P)`, and no 4K mapping left in `IT(P)` when present; effect: unlocks
  `PT(P)` and `IT(P)` and sets `prog = ThreadExitZombie`.

**Finish** (`thread_exit_finish_step_pre`, `thread_exit_finish_step`)

- Pre: `W` for `cpu`, `C`, `P`, and `T`; `thr.caller is None`; every
  descriptor is `None`. A thread with siblings finishes with
  `prog is ThreadExit`; `P`'s last thread finishes with
  `prog == ThreadExitZombie` and no quota of any size left in `T` or `P`.
- Effect: `kernel_u_thread_exit_changed` on the state with `cpu`, `C`, and
  `P` unlocked: `cpu` becomes Idle with no current process or thread; `T`
  leaves the thread map, `P.owned_threads`, and `C.owned_threads`; `P`
  absorbs `T`'s `quota_4k`, `quota_2m`, and `quota_1g`; the container whose
  `owned_pages` holds `T`'s page gains one `quota_4k`. If `T` was `P`'s last
  thread, `P` becomes a zombie whose `pagetable` and `iommu_table` project
  as `None`, and `P.pcid` joins `C.free_pcids` (in K, `C`'s PCID allocator
  releases it); if `P` is also `C.root_process`, `C` becomes a zombie. The
  `(cpu_id, KERNEL_DEFAULT_PCID)` TLB entry is emptied or kept: the step is
  the disjunction over `flushed_default_pcid`, and in K it is emptied exactly
  when that needflush bit was set. Nothing else changes.
- In K, `T`'s page becomes `Free4k` in shard `cpu_id` of its owner's 4K
  allocator cache, `cpu_id` switches to the default page table, and the
  containers of `C.uppertree_seq` drop `T` from `owned_indirect_threads`,
  which U does not show. A full cache is first drained under the pool in an
  atomic section that changes no U state and stutters; the page and cache
  stay locked across it.

Trace (`thread_exit_syscall_trace`): enter, the middle steps (one drop step
per descriptor that holds an endpoint, then, for `P`'s last thread, the
reclaim steps in the order above), then finish; `2 <= len`, with no
numeric upper bound. A stutter leaves an empty trace, `post == pre`, and no
lock held.

Stutters (in this order): CpuIdle (cpu not Running or killed), ContainerKilled, ProcessKilled, ThreadKilled,
PeerKilled (a killed `R`, met when its lock is tried after `T`'s).

Trusted primitive: `retype_thread_rwlock_to_4k_page_perm` (external_body;
authorized TCB), the inverse of the `retype_page_perm_to_rwlock` mint that
creates a thread: it retires the removed, write-locked thread object, returns
its page as a raw 4K page permission, and drops `T`'s lock from `lctx`.

## 18. kill_process — enter, walk, thread, reclaim, retire steps, finish

Status: implemented, including the thread kill (dangling, mark, dequeue, evict,
unlink, killed-thread reclaim), PCI reassignment, live reclaim, zombie reap,
and table-structure retirement.
Verified: kill focused run #TBD, workspace run #TBD, monolith run #TBD,
noninterference run #TBD.

- Arguments: `child_index`. The running thread `T` of `cpu_id` kills
  `D = P.children[child_index]` and every process below it, one subtree at a
  time, depth first and bottom up. The trap layer checks nothing.
- Result: Success unless the call stutters (`kill_process_syscall_result`);
  the killer keeps running. After Success no process of the subtree is left,
  and each of its threads is reclaimed or, if it waited for a reply, left as
  an unlocked dangling thread that its callee reclaims.
- U locks retained from enter to finish: `cpu` (major 1), `P` (105), and `T`
  (106). Each marked process stays write-locked from the step that marks it
  to its retire step; these processes form the chain from `D` down to the
  target `L`. A marked thread `V` stays write-locked from its mark step until
  it is reclaimed, and `PT(L)` (10004) and, when `L` has one, `IT(L)` (10006)
  from the lock-table step to the unlock-table step. A marked process or
  thread reports the minimal lock id (major 0), so every later lock is above
  it. `C` is never locked: its thread and process sets are lock-free ghost
  state, and its quota and PCIDs change only under allocator locks inside one
  step (R5).
- Non-U, each taken and released inside one atomic section: the locks of the
  killed-thread reclaim and of the leaf reclaim as in §17; the root table
  (10005) in the reassign step; `C`'s PCID allocator (107) in the zombify
  step; and the structure-page, root-page, cache, pool, and quota locks of
  the retire stage. Across the retire stage's sections the killer holds `L`'s
  process page, the object pages of `PT(L)` and `IT(L)`, and both tables
  (hold below). The per-step lists below name them.
- Lock order: `cpu`, `P`, `T`, then the marked chain and `V` at the sunk id;
  inside a step, `V` at the major of its state, then its shard, endpoint,
  or remote cpu `R`; in the killed-thread reclaim, the endpoint, the caller,
  the shard, the page, cache, pool, and quota; in reclaim, the root table,
  `PT(L)`, `IT(L)`, the per-page, needflush, and quota locks, and the PCID
  allocator; in retire, the process and table object pages (1000), `PT(L)`,
  `IT(L)`, then in each section a structure page or the root pages (10008),
  the cache, pool, and quota. `R` (major 1) is above `T` because it runs a process deeper than
  `P`.
- Progress: `KillProcess { process: L, stage }`. Enter records `{ D, Walk }`;
  a mark-child step moves to `{ child, Walk }`; mark thread records
  `Thread { V }` and unlink returns to `Walk`; reclaim records
  `Reclaim { flushed }`, `Quota { returned }`, `Zombie`, and `Retire`; the
  retire step moves to `{ L.parent, Walk }`. Finish needs `{ P, Walk }`.
- Derivation: every step reads `P` as `cpu.current_process->Some_0` and `T`
  as `cpu.current_thread->Some_0`; `W(cpu)` keeps them stable until finish.
  `L` and `V` are recorded in `prog` (R2). `W(L)` keeps `L.children[0]`,
  `L.owned_threads[0]`, `L.parent`, `PT(L)`, and `IT(L)` stable, and
  `L.parent` is the previous chain process or `P`, both write-held. Every
  process of the subtree belongs to `C = cpu.owning_container`.
- Middle steps (`kill_process_middle_step`) all require
  `kill_process_step_pre`: `W` for `cpu`, `P`, and `T`, `prog is
  KillProcess`, `L` present, `W(L)`, and `L.killed`.

**Enter** (`kill_process_enter_step_pre`, `kill_process_enter_step`)

- Pre: `index_valid(cpu_id)`, `cpu.state is Running`, `prog is None`,
  `cpu.current_process == Some(P)`, `thr.owning_proc == P`,
  `thr.state == RUNNING { cpu_id }`, `!P.killed`, `!thr.killed`; `Unlocked`
  for `cpu`, `P`, and `T`; `child_index < P.children.len()`, `D` present, and
  `!D.killed`. `C.killed` and `C.zombie` are not checked.
- Effect: write-locks `cpu`, `P`, and `T`; marks `D` (`killed`) and
  write-locks it; `prog = KillProcess { D, Walk }`. In K, `D` is locked at
  the process major below `P` and its id sinks once it is marked
  (`try_wlock_process_and_mark_kill`).

**Walk** (stage `Walk`)

- Mark child (`kill_process_mark_child_step`): pre `L.children` non-empty
  and `L.children[0]` present; effect: marks and write-locks `L.children[0]`
  and records `{ L.children[0], Walk }`. A child of the write-held `L`
  cannot carry another killer's mark (`process_kill_mark_wf`), so the step
  always applies.
- Dangling (`kill_process_dangling_step`; `kill_process_thread_step_pre`:
  `L.children` empty, `V = L.owned_threads[0]` present): pre
  `V.state is WAITING_REPLY` and `Unlocked(V)`; effect: `V` leaves
  `L.owned_threads`, `L` absorbs its `quota_4k`, `quota_2m`, and `quota_1g`,
  and `V` becomes `DANGLING` with no quota, keeping its descriptors, `caller`,
  and `callee`. `V` is not marked and stays unlocked (in K it is locked at the
  blocked major 10003 and released inside the step). It stays in `C`'s
  thread set until its callee reclaims it: a reply (§11a,
  ErrorIpcCallerKilled), the callee's exit (§17), or the reclaim of a killed
  callee below.
- Mark thread (`kill_process_mark_thread_step`): pre as for dangling with
  `!V.state.is_reply_waiting()`; effect: `V.killed`, `W(V)`, and
  `prog = { L, Thread { V } }`. In K, `V` is locked at the major of its state
  (running 106, scheduled 20001, blocked 10003; a TRANSIT or KILLED thread is
  write-held elsewhere and is waited for), and `mark_thread_kill` marks it
  and sinks its id.

**Thread** (stage `Thread { V }`; `kill_process_victim_step_pre`: `V`
present, `W(V)`, `V.killed`)

- Dequeue scheduled (`kill_process_dequeue_scheduled_step`):
  `V.state == SCHEDULED { s }`; `V` leaves `scheduler[s]` of its container
  and becomes `KILLED` with `error_code = None`. Non-U: shard `s` (10011).
- Dequeue endpoint (`kill_process_dequeue_endpoint_step`):
  `V.state.is_endpoint_waiting()` on `E = V.blocking_endpoint_ptr->Some_0`;
  `V` leaves `E.queue` and becomes `KILLED` with no blocking endpoint. `E`
  (10001) is locked and released inside the step.
- Evict (`kill_process_evict_step`): `V.state == RUNNING { R }`,
  `R != cpu_id`; `R` becomes Idle with no current process or thread, and `V`
  becomes `KILLED`. In K the killer write-locks `R`, marks it with its own
  `killer_info` (`V` carries the same mark, `thread_cpu_wf`), sends the
  maskable eviction IPI and waits for its acknowledgement, unmarks `R`
  (`unkill`), and sets it Idle with no current process or thread
  (`evict_remote`). `R` takes the IPI only in user mode or at its idle `hlt`:
  it loads the default page table with the default PCID, acknowledges, and,
  from user mode, abandons `V` for `run_idle`. Every own-cpu lock of `R`
  returns at once on the mark, so `R` cannot spin while the killer waits.
  `update_lock_id` moves `R` to the idle major (2), and `R` is released inside
  the step. The mark is U-visible as `cpu.killed` but cleared within the
  step.
- Unlink (`kill_process_unlink_step`): `V.state is KILLED`; `V` leaves
  `L.owned_threads`, `L` absorbs its quota of every size, `V` keeps none, and
  `prog = { L, Walk }`. `V` stays write-held.
- Killed-thread reclaim (`kernel_u_killed_thread_reclaim_step`, shared with
  the reply and exit dangling-caller paths), one step per change, the kernel choosing
  the thread (R1):
  - each descriptor of `V` that holds an endpoint is cleared, and its
    unlocked endpoint drops `(V, index)` (`kernel_u_killed_descriptor_dropped`;
    the endpoint, 10001, is locked inside the step);
  - when `V` serves a call from `X`: a waiting `X` becomes
    `SCHEDULED { cpu_id }` with `ErrorIpcCalleeExited` on shard `cpu_id` of
    its container (`kernel_u_killed_caller_woken`), or a `DANGLING` `X` is
    taken over as a write-locked `KILLED` thread without callee
    (`kernel_u_killed_caller_taken_over`); in K, `X` is locked at the blocked
    major (10003) and a taken-over `X` moves to the killed-thread major (108);
  - `V` leaves the thread map and `C.owned_threads`, and the container that
    owns its page gains one `quota_4k` (`kernel_u_dangling_thread_reclaimed`); in
    K its page (1000) becomes `Free4k` in shard `cpu_id` of its owner's 4K
    allocator cache (10012; the pool, 10015, only drains a full cache in a
    section that stutters) under that allocator's quota lock (20002);
  - a taken-over `X` is reclaimed the same way.

**Reclaim** (stage `Walk`; `kill_process_empty_target_pre`: `L` has no
children and no threads)

- Reassign (`kill_process_reassign_functions_step`): every PCI function `L`
  owns is detached, gets `P` as its root-table owner, and has its IOTLB
  domain `pci_bdf_did` emptied; `L.owned_pci_functions` moves to `P`. K
  scans all 65,536 B/D/Fs under the root table lock (10005), taken and
  released inside the step. A target owning no function takes no step.
- Zombie retire (`kill_process_zombie_retire_step`): an `L` that is already a
  zombie (§17) and owns no function moves to `Retire`.
- Lock table (`kill_process_lock_table_step`): a live `L` owning no function
  write-locks `PT(L)` and `IT(L)`; `prog = Reclaim { flushed: false }`.
- The remaining reclaim steps follow §17 with `L` for `P` and
  `kill_process_reclaim_step_pre` (the stage, `W(PT(L))`, and `W(IT(L))` when
  present) for `unmap_4k_locked`:
  - Leaf (`kill_process_leaf_step`): one valid user 4K mapping leaves
    `PT(L)`; the kernel chooses the VA. In K the entry is only marked not
    present.
  - Flush (pre `kill_process_flush_step_pre`: no valid user 4K mapping left in
    `PT(L)`): one `(cpu', L.pcid)` TLB entry becomes empty
    (`kernel_u_cpu_tlb_cleared`). Non-U: that needflush cell (30001).
  - Flushed (`kill_process_flushed_step`): `prog = Reclaim { flushed: true }`.
  - Refund: one container in `C` or `C.uppertree_seq` gains 4K quota
    (`kernel_u_container_quota_4k_increased`). Before the refunds, K removes
    each cleared entry and returns its page (mapped-page major 10009) to
    shard `cpu_id` of its owner's 4K allocator cache (10012; pool 10015 only
    to drain a full cache) in atomic sections that change no U state and
    stutter, accumulating the refund in `T`'s pending quota; each refund
    step takes one allocator quota lock (20002). The IOMMU leaf steps follow
    the CPU refunds, then one IOMMU flush step, then their own refunds.
  - IOMMU leaf (`kill_process_iommu_leaf_step`): `Reclaim { flushed: true }`;
    one 4K mapping (the kernel chooses the IOVA) leaves `IT(L)`. In K the
    leaf is only marked not present.
  - IOMMU flush (`kill_process_iommu_flush_step`, NI label
    `KillProcessIommuFlush`): `Reclaim { flushed: true }`;
    every `iommu_tlb` domain becomes empty and nothing else changes. K runs
    it once, after every IOMMU leaf is hidden, then removes the hidden leaves
    and refunds their pages as for a CPU leaf.
  - Quota (`kill_process_quota_step`): the next size `S` (4K, then 2M, then
    1G) moves the whole `L.quota_S` to `C`, zeroes it, and sets
    `prog = Quota { returned: S }`. Non-U: `C`'s allocator quota of size `S`
    (20002, 20003, or 20004).
  - Unlock table (`kill_process_unlock_table_step`): `Quota { returned: 1G }`,
    no valid user 4K mapping left in `PT(L)`, and none in `IT(L)`; unlocks
    both and sets `prog = Zombie`.
- Zombify (`kill_process_zombify_step`): `prog` at `Zombie`, `!L.zombie`;
  `L` becomes a zombie whose `pagetable` and `iommu_table` project as
  `None`, `L.pcid` joins `C.free_pcids`, and `prog = { L, Retire }`. Non-U:
  `C`'s PCID allocator (107).

**Retire** (stage `Retire`)

- Hold, no step: one section locks `L`'s process page and the object pages
  of `PT(L)` and `IT(L)` (1000) in index order, then `PT(L)` (10004) and
  `IT(L)` (10006). The killer keeps them until the retire step, so no other
  thread changes the tables between the sections below.
- Structure retirement, no step: for `PT(L)` and then `IT(L)`, the killer
  scans the held table for the next table page below the root that links
  nothing (an L1, L2, or L3 table). Each such page takes one section: it
  locks the page (structure-page major 10008, above both table locks) and
  shard `cpu_id` of `C`'s 4K allocator cache (10012; pool 10015 only to
  drain a full cache), unlinks the page from its parent table, returns it to
  the cache, and counts its quota on `T`'s pending counter. Every section
  removes one page, so the scans end. None of these sections changes U: a
  zombie's tables project as `None`, and the page array, caches, and pending
  counters are not in U.
- Refund: after the scans, one refund step
  (`kernel_u_container_quota_4k_increased`) returns any pending quota to the
  killer's container chain.
- Blocked: unreachable; a zombie's tables map nothing (`process_emptied_tables_wf`, `pagetable_no_huge_leaf_wf`).
- Retire (`kill_process_retire_step`): pre `Retire`, `L` has no children and
  no threads, `L.zombie`, `L` owns no function, `L.parent is Some`, and `C`
  present; effect: `L` leaves the process map, its parent's `children`, the
  `subtree_set` of every process in `L.uppertree_seq`, and
  `C.owned_processes`; `C.quota_4k` grows by the number of 4K pages the step
  frees: `L`'s process page, `PT(L)`'s object page and root table page, and,
  when `L` has an IOMMU table, `IT(L)`'s object page and root table page (3
  or 5); `prog = { L.parent, Walk }`. In K the step adds the root table
  pages (10008) to the held pages and tables, then locks shard `cpu_id` of
  `C`'s 4K allocator cache (10012; pool 10015 only to drain a full cache)
  and `C`'s 4K quota (20002), retypes the table objects, their root tables,
  and the process back into 4K pages, and returns them to the cache. `L`'s
  lock leaves with the object.

**Finish** (`kill_process_finish_step_pre`, `kill_process_finish_step`)

- Pre: `W` for `cpu`, `P`, and `T`; `prog == KillProcess { P, Walk }` (the
  walk retired `D`).
- Effect: clears `prog` and unlocks `T`, `P`, and `cpu`. Nothing else
  changes.

Trace (`kill_process_syscall_trace`): enter, the middle steps, then finish;
`2 <= len`, with no numeric upper bound. A stutter leaves an empty trace,
`post == pre`, and no lock held.

Stutters (in this order): CpuIdle (cpu not Running or killed), ProcessKilled (`P`),
ThreadKilled, InvalidChild (`child_index >= P.children.len()`),
ProcessKilled (`D` marked in the entry state; once `P` is write-held, its
child cannot be marked by another killer, `process_kill_mark_wf`).

Trusted primitives (external_body; authorized TCB): `RwLock::mark_kill`
(marks a write-held object for its killer), `CpuLockedArray::unkill` (clears
the mark of a cpu the killer still write-holds; no other object type is ever
unmarked), the kill-aware `CpuLockedArray` lock operations
(`wlock_unless_killed`, `wunlock`, `mark_kill`), `evict_remote_cpu` under
`CpuLockedArray::evict_remote` (a maskable IPI, taken only in user mode or at
the idle `hlt`, makes the remote cpu load the default page table and
acknowledge; the killer spins for the acknowledgement; TODO: model this wait
as a virtual lock in the lock order), `page_map_to_page_perm` (an
unlinked table page is a 4K page again),
`retype_pagetable_rwlock_to_4k_page_perms` (a page table whose only table
page is its root becomes its object page and root page), and
`retype_process_rwlock_to_4k_page_perm` (a killed, empty process becomes its
4K page).

Differences:

1. Steps that acquire a U-visible object do not state `Unlocked` for it
   (R3, R4): enter and mark child for the marked process, mark thread for
   `V`, dequeue endpoint for `E`, evict for `R`, and lock table for `PT(L)`
   and `IT(L)`. The dangling step and the killed-thread reclaim steps do.
2. Liveness: a blocked retire stage retries forever. No invariant states
   that a zombie's tables map nothing, although reclaim removes every 4K
   leaf and no syscall creates 2M or 1G leaves.

## 19. kill_container — enter, walk, process, cpus, pages, retire steps, finish

Status: implemented, including the container walk, the process kill of each
emptied container (the §18 middle steps in a container scope), the root
retire, and the Cpus, Pages, and Retire stages. No `TODO` remains in
`syscall_kill_container/`. Verified: kill focused run #TBD, workspace run
#TBD, monolith run #TBD; noninterference run #33949 covers its own steps but
not the reused §18 process kill steps (below).

- Arguments: `child_index` (boot `NR_KILL_CONTAINER`). The running thread `T`
  of `cpu_id`, in container `C = cpu.owning_container`, kills
  `D = C.children[child_index]` and every container below it, one subtree at
  a time, depth first and bottom up. Any thread of `C` may kill a direct
  child container. The trap layer checks nothing.
- Result: Success unless the call stutters (`kill_container_syscall_result`);
  the killer keeps running. After Success no container of the subtree is
  left: their processes and threads are gone as in §18, their cpus and free
  pages belong to `C`, and their kernel-object pages are free pages of `C`.
- U locks retained from enter to finish: `cpu` (major 1), `C` (101), `P`
  (105), and `T` (106). Each marked container stays write-held from the step
  that marks it to its retire step; these containers form the chain from `D`
  down to the target `L`, and the parent of each is the previous chain
  container or `C`, both write-held (`container_kill_mark_wf`). While `L` is
  in its Process stage, its marked processes, threads, and tables are held as
  in §18. From the cpus step to the retire step the killer also write-holds
  `L`'s marked cpu set (`CS(L)`, `cpu_set_killed`). A marked container,
  process, or cpu set reports the minimal lock id (major 0). `C` is
  write-held for the whole kill (unlike §18).
- Non-U: the locks of the process stage as in §18; in each move-cpu step,
  `L`'s request cell for the moved cpu (104) and `C`'s cpu set (10010); from
  the Pages stage's first section until after its retire-stage step, `L`'s 4K
  and 2M allocator caches on every cpu (10012, 10013) and the 4K and 2M global
  pools (10015, 10016) and quotas (20002, 20003) of both `L`'s and `C`'s
  allocators; inside the retire step, `L`'s request cells (104) and PCID
  allocator (107), its five 4K object pages and two 2M object heads (1000),
  its scheduler shards (10011), its 4K, 2M, and 1G caches (10012–10014), the
  4K and 2M pools and quotas of `L` and `C`, `L`'s 1G pool and quota (10017,
  20004), and the merged tails of both 2M heads (30000).
- Lock order: `cpu`, `C`, `P`, `T`, then the marked chain at the sunk id;
  the process stage follows §18. Containers, request cells, PCID allocators,
  and non-Off cpus carry their container's depth in the lock id, compared
  before the major, so they follow the killer's own locks; cpu sets,
  scheduler shards, and allocator locks carry none, and same-size allocator
  locks of `L` and `C` are taken in address order (`*_ordered`). A move-cpu
  step locks an Idle cpu (major 2), then the cell and `C`'s set; an Off cpu
  is locked last (`wlock_off_cpu`, 30002) after the cell and the set. The
  Pages stage locks `L`'s 4K and then 2M caches in cpu order, then the 4K and
  2M pools, then the 4K and 2M quotas. The retire step locks the cells in cpu
  order, the PCID allocator, the object pages in index order, the shards, the
  4K, 2M, and 1G caches in cpu order, the pools, the quotas, then the tails.
  It never locks `L`'s parent, which is already write-held.
- Progress: `KillContainer { container: L, stage }`. Enter records
  `{ D, Walk }`; mark child moves to `{ child, Walk }`; mark root records
  `{ L, Process { process: R, stage: Walk } }`, and the §18 steps then move
  only the inner `{ process, stage }` (`kill_progress_at`); the root retire
  step returns to `{ L, Walk }`; the cpus step records `Cpus`, the pages step
  `Pages`, the retire-stage step `Retire`, and the retire step moves to
  `{ L.parent, Walk }`. Finish needs `{ C, Walk }`.
- Derivation: every step reads `C`, `P`, and `T` from `cpu` under `W(cpu)`.
  `L` and the process target are recorded in `prog` (R2). `W(L)` keeps
  `L.children[0]`, `L.root_process`, `L.owned_processes`, and `L.parent`
  stable. The walk reads these lists live at each step; it keeps no snapshot
  of `owned_processes` (§9).
- Middle steps (`kill_container_middle_step`) are either a §18 middle step,
  whose `kill_process_step_pre` additionally requires the recorded container
  present and write-held, or one of the container steps below, which require
  `kill_container_step_pre`: `W` for `cpu`, `C`, `P`, and `T`,
  `prog is KillContainer`, `L` present, `W(L)`, and `L.killed`.

**Enter** (`kill_container_enter_step_pre`, `kill_container_enter_step`)

- Pre: `index_valid(cpu_id)`, `cpu.state is Running`, `prog is None`,
  `thr.owning_proc == P`, `thr.state == RUNNING { cpu_id }`, `!C.killed`,
  `!P.killed`, `!thr.killed`; `Unlocked` for `cpu`, `C`, `P`, and `T`;
  `child_index < C.children.len()`, `D` present, and `!D.killed`. `C.zombie`
  is not checked.
- Effect: write-locks `cpu`, `C`, `P`, and `T`; marks `D` (`killed`) and
  write-locks it; `prog = KillContainer { D, Walk }`. In K, `C` is taken with
  `wlock_container_unless_killed`, and `D` with
  `try_wlock_container_and_mark_kill`, whose id sinks once it is marked; a
  live container always owns a root process.

**Walk** (stage `Walk`)

- Mark child (`kill_container_mark_child_step`): pre `L.children`
  non-empty; effect: marks and write-locks `L.children[0]` and records
  `{ L.children[0], Walk }`. A child of the write-held `L` carries no other
  killer's mark (`container_kill_mark_wf`).
- Mark root (`kill_container_mark_root_step`): pre `L.children` empty and
  `L.owned_processes` non-empty; effect: marks and write-locks
  `R = L.root_process` and records `Process { R, Walk }`. A root has no
  parent; its container carries the same mark (`process_kill_mark_wf`).
- Cpus (`kill_container_cpus_step`): pre `L.children` empty and
  `L.owned_processes` empty; effect: `CS(L)` becomes write-locked and
  `cpu_set_killed`, and `prog = { L, Cpus }`. In K,
  `wlock_cpu_set_and_mark_kill` marks the set for the same killer
  (`cpu_set_kill_mark_wf`). By then `L` owns no thread
  (`container_without_children_and_processes_owns_no_threads`).

**Process** (stage `Process { process: Q, stage }`)

- The §18 walk, thread, and reclaim steps run on the processes of `L`, with
  `L` in place of `C` for the quota, PCID, and process-set changes:
  `kill_process_quota_step` and `kill_process_zombify_step` return quota and
  the PCID to `L`, and `kill_process_retire_step` retires a non-root process
  into `L.quota_4k`. The reassign step moves `L`'s PCI functions to the
  killer's process `P`. Dangling callers, marked threads, evictions, and the
  killed-thread reclaim (including the take-over of a `DANGLING` caller)
  are those of §18; a call never crosses containers (`thread_caller_callee_wf`
  states `caller.owning_container == callee.owning_container`), so every
  dangling caller in `L` is taken over and reclaimed by this walk.
  Endpoints have no stage of their own: every holder of an endpoint lives in
  its owner's subtree, so each one `L` owns is freed when its last
  descriptor is dropped.
- Refunds: in a container scope each freed 4K page, CPU or IOMMU leaf and
  unlinked structure page alike, is credited to the container that owns it
  (in `L` or `L.uppertree_seq`) in its own refund step
  (`kernel_u_container_quota_4k_increased`), not through `T`'s pending
  counter.
- TLB stale-window ledger: each page table carries `window_stale_cpus`, a
  map from a 2M window `(L2 page, L2 index)` to the cpus that may still hold
  translations of a leaf cleared in it. The leaf step clears the present bit
  and records every cpu for that window (`WindowStaleUpdate::Set`). The
  flush stage then visits each cpu `c` in order, one flush step each: it
  handles `(c, Q.pcid)` under `c`'s needflush cell (30001) as in §18 and
  drops `c` from every record (`RemoveCpu { cpu_id: c }`); after the last
  cpu, `ClearEmpty` deletes the empty records. The ledger is therefore empty
  before any cleared entry is removed and its page refunded; it is ghost and
  not in U. `pagetable_window_stale_cpus_only_when_locked`
  allows a record on a table that is not write-held only for a locked
  window.
- Root retire (`kill_container_retire_root_step`): pre stage
  `Process { R, Retire }`, `R` with no children, threads, or PCI functions,
  `R.zombie`, `R.parent is None`, and `R.owning_container == L`; effect: `R`
  leaves the process map and `L.owned_processes`, `L.zombie` becomes false,
  `L.quota_4k` grows by an amount the spec leaves open, and
  `prog = { L, Walk }`. In K the hold and structure-page sections of §18 run
  first (structure pages credited per page, as above); the step then returns
  `R`'s process page and its tables' object and root pages to shard `cpu_id`
  of `L`'s 4K allocator cache (drained first when full) under `L`'s 4K
  quota.

**Cpus** (stage `Cpus`)

- Move cpu (`kill_container_move_cpu_step`): exactly one cpu of `L`, Idle or
  Off and unlocked, gets `owning_container = C` and keeps its state;
  `L.cpu_offline_requests` drops that cpu. In K the killer scans `CS(L)` in
  cpu order; an Idle cpu moves to `C`'s set
  (`transfer_idle_cpu_to_container`) and an Off cpu to a closed slot of
  `C`'s set (`transfer_off_cpu_to_container`, `insert_closed`), with `C`'s
  depth; `L`'s request cell is cleared, and the cpu, the cell, and `C`'s set
  are released inside the step. No cpu of `L` is Running: `L` has no thread
  left. No IPI is sent and no cpu changes state: an Off cpu stays Off in
  `C` and an Idle cpu stays Idle in `C`; the `cpu_online` path is not used.
- Pages (`kill_container_pages_step`): pre no cpu of the array is owned by
  `L`; effect: `prog = { L, Pages }`.

**Pages** (stage `Pages`)

- Drain, no step: after locking (Non-U above), the killer moves every page of
  `L`'s 4K and then 2M caches on every cpu into `L`'s global pools, one page
  per section; none changes U.
- Move page (`kill_container_move_page_step`, size 4K or 2M): one free page
  of `L`'s global pool moves to `C`'s global pool of the same size; its 4K
  pages (1 or 512) leave `L.owned_pages` and join `C.owned_pages`, and one
  page of quota of that size moves from `L` to `C`. The step relation also
  admits size 1G, which the code never takes: `L`'s 1G allocator holds no
  page (the Pages stage proves it empty).
- Retire stage (`kill_container_retire_stage_step`): pre `L.quota_4k`,
  `L.quota_2m`, and `L.quota_1g` all zero; effect: `prog = { L, Retire }`.
  In K the killer first sets `L`'s ghost flag `retire_ready`
  (`container_kill_retire_wf`: a retire-ready container is marked, has no
  child, subtree, process, thread, or indirect thread, and its three
  allocators hold no quota and no cached page), then releases the allocator
  locks in a section that stutters. The flag is K-only and carries these
  facts across the step boundary.

**Retire** (stage `Retire`)

- Retire (`kill_container_retire_step`): pre `L` has no children and no
  processes, `L.parent is Some` and present, and `C != L`; effect: `L` leaves
  the container map, its parent's `children`, and the `subtree_set` of every
  container in `L.uppertree_seq`; `C.owned_pages` gains `L.owned_pages`;
  `C.quota_4k` and `C.quota_2m` grow by amounts the spec leaves open;
  `prog = { L.parent, Walk }`. In K the step takes the locks above, unlinks
  `L` from its parent (which returns `L`'s list node), retires `L` with its
  request table, its PCID allocator, scheduler, `CS(L)`, and its 4K, 2M, and
  1G allocators (all empty), returns their five 4K object pages to `C`'s 4K
  global pool and the two 2M heads (container and PCID allocator) with their
  merged tails to `C`'s 2M global pool, raises `C`'s 4K and 2M allocator
  quotas by the pages returned, and releases every lock taken for `L`. `L`'s
  lock and `CS(L)`'s leave with the objects. `page_object_owner_wf` shows that
  the pages `L` owns at this point are exactly these object pages and tails,
  and no page `L` owns is mapped, so no page-array scan is needed.

**Finish** (`kill_container_finish_step_pre`, `kill_container_finish_step`)

- Pre: `W` for `cpu`, `C`, `P`, and `T`; `prog == KillContainer { C, Walk }`
  (the walk retired `D`).
- Effect: clears `prog` and unlocks `T`, `P`, `C`, and `cpu`. Nothing else
  changes.

Trace (`kill_container_syscall_trace`): enter, the middle steps, then finish;
`2 <= len`, with no numeric upper bound. A stutter leaves an empty trace,
`post == pre`, and no lock held. The partial trace is
`kill_partial_trace` with `KillTraceCtx::Container { child_index }`.

Stutters (in this order): CpuIdle (cpu not Running or killed),
ContainerKilled (`C`), ProcessKilled (`P`), ThreadKilled, InvalidChild
(`child_index >= C.children.len()`), ContainerKilled (`D` marked in the entry
state).

Invariants the kill relies on: `container_kill_mark_wf`,
`process_kill_mark_wf` (root branch), and `cpu_set_kill_mark_wf` for the
marks; `container_kill_retire_wf` for the Pages→Retire facts;
`thread_caller_callee_wf` and `thread_dangling_chain_end_wf` (through the
lemma `container_without_children_and_processes_owns_no_threads`) for "no
thread left"; `page_object_owner_wf` for the retired pages;
`pagetable_window_stale_cpus_only_when_locked`, `process_emptied_tables_wf`,
and `pagetable_no_huge_leaf_wf` for the table reclaim and retire as in §18.

Trusted primitives (external_body; authorized TCB): those of §18, with
`RwLock::try_wlock_and_mark_kill` also marking containers and cpu sets, and
the inverse retypes of the Retire step in `src/proc/process_util_t.rs`:
`retype_container_rwlock_to_2m_page_perm` (the container and its request
table become their 2M page), `retype_pcid_allocator_rwlock_to_2m_page_perm`,
`retype_cpu_set_rwlock_to_4k_page_perm`, `retype_scheduler_to_4k_page_perm`,
and `retype_allocator_to_4k_page_perm` (4K, 2M, and 1G). Each requires the
object already out of its map and every lock of it held by the killer.

Noninterference: the eleven kill_container steps (Enter, MarkChild,
MarkRoot, RetireRoot, Cpus, MoveCpu, Pages, MovePage, RetireStage, Retire,
Finish) have `StepLabel`s in `noninterference/src/theorem.rs` and are proved
in `noninterference/src/ni_kill_container.rs` (run #33949, 145 verified, 0
errors). Not covered: the §18 process kill steps (`kill_process_middle_step`)
that the Process stage reuses. kill_process and thread_exit have their own
`StepLabel`s, including `KillProcessIommuFlush` and `ThreadExitIommuFlush`,
proved in `ni_kill_process.rs` and `ni_thread_exit.rs` (run #34469).

Differences:

1. Steps that acquire a U-visible object do not state `Unlocked` for it (R3,
   R4): enter and mark child for the marked container, mark root for `R`,
   and the cpus step for `CS(L)`, besides the §18 cases. The move-cpu step
   does.
2. The root retire and retire steps leave the quota increase open
   (`quota_4k`, `quota_2m` only grow); §18's retire step states the exact
   page count.
3. `kill_container_middle_step` admits a 1G move-page step that the code
   never takes.
4. The killer's wait for an evicted cpu's acknowledgement is not modeled as
   a lock (the §18 TODO).
