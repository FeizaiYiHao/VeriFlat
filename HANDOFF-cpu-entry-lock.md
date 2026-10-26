# 实施计划 — 具体锁序 + 动态容器 + 锚点 DID + Cpu 内含 SyscallPerm

状态：**已批准**；Batch 1 已完成并随本提交发布，Batch 2–4 未实现。权威细节是用户在对话中批准的实施计划；本文件只记录交接所需的结构与规则，做完删除。

- 取代：原"独立 CpuEntry 入口锁（IPI 模型）"方案已放弃——不新增 `CpuEntry` 对象、第 25 个锁族、`IpiPerm`、`mint/collect_syscall_perm` 或 ENTRY_* major。
- 被放弃方案的 step 0/1 实现保存在 `/local/home/xiangdc/veriflat-parked/cpu-entry-step01.patch`（原 `stash@{0}` "parked: cpu-entry step 0/1 (ws #34657 3181/0, NI #34658 257/0)"，Batch 1 推送后 drop）。只作参考，不要 apply。
- 基线：Batch 1 提交。

## 四个批次（顺序固定，每批工作区 + NI + 单体全绿后再进下一批）
1. **Batch 1（已完成）**：mmap 在 read miss → fill 之间保留 cpu/T 写锁（`Mmap4kHold` / `Mmap4kRelease` U/NI 标签与两条 trace spec），外加证明清理。见 `HANDOFF.md`。
2. **Batch 2 — 具体锁序 + 动态容器**：OwnerSource/LockControl 规则、`NotApp` 迁移为具体 owner、`ErrorContainerLockOrderConflict`。
3. **Batch 3 — 锚点 DID**：按用户批准的方案实施；仓库内尚无细节记录，开工前与用户核对语义。
4. **Batch 4 — SyscallPerm 放进 Cpu + IPI / kill 状态收尾**：`Cpu.syscall_perm`、入口包裹、删 offline kick、保留 online wake、删 CPU kill 状态、boot IF/evicted 规则。

## Batch 2：具体锁序 + 动态容器
- **OwnerSource**：每个锁族的 lock id owner 分量（container / process 深度）来自一个确定的来源——对象自身的不可变字段，
  或其当前动态归属（例如 CPU 当前所属容器 / 当前进程）。来源是锁族定义的一部分，不在调用点选择。
- **LockControl（动态规则）**：动态 owner 分量只能由持有该对象写锁的 section 改变，且改变就是一次 rekey
  （typed 锁表条目覆写 + pair 替换，按 lock-model 的既有 dynamic-id 规则）。未持写锁时 id 稳定，可作为锁序依据。
- **`NotApp` 迁移为具体值**：现在用 `NotApp` 通配的 owner 字段（CPU-set 锁、Off / 无上下文 CPU 等）改为由 OwnerSource 给出的
  具体 owner，使 `lock_id_acyclic` / `held_lock_majors_lt` 在全序下成立。`NotApp` 只剩确实无归属的对象；不改变 IPC 拓扑。
- **`ErrorContainerLockOrderConflict`**：新返回码。当 syscall 在当前已持锁下，按具体锁序无法合法获取下一把锁
  （动态容器归属与已持锁冲突）时，放锁并以该错误 stutter 返回，而不是加锁序豁免。对应 U spec / NI 按 stutter 处理。

## Batch 3：锚点 DID
- 语义以用户批准的计划为准；本文件不补写未记录的细节。

## Batch 4：SyscallPerm 放进 Cpu + IPI / kill 状态
- `Cpu` 对象新增 `syscall_perm: Option<Tracked<SyscallPerm>>`（随 CPU 锁保护，不新增锁族、不新增锁）；
  `LocalContext` 新增 tracked 槽存放本 CPU 取出的 `SyscallPerm`。
- `u_sys_enter(cpu_id)` / `u_sys_exit(cpu_id)`：`external_body` TCB 原语，把 `SyscallPerm` 在 `Cpu.syscall_perm` 与 lctx 槽之间移动；
  加入 TCB 清单。U 层与 NI 新增 `SysEnter` / `SysExit` 标签。
- 所有入口包裹：每个 `syscall_*` 以及 `cpu_offline_check` / `syscall_schedule` / `rebalance_pull` / `cpu_online_resume`
  的边界契约改为 lctx 只持本 CPU 的 SyscallPerm 槽、其余锁表为空；`release_and_finish_syscall.rs`、`kernel_step_wrappers/boundary.rs`
  同步。Off CPU 没有 SyscallPerm，因此不能进入内核步骤。
- **删 offline kick**：`syscall_cpu_offline_request.rs` / `cpu_offline_request_child_locked.rs` 中的 `send_ipi` 删除，目标在下一次入口 / 定时器自行走 `cpu_offline_check`。
- **保留 online wake**：`syscall_cpu_online.rs` / `cpu_online_child_locked.rs` 的唤醒 IPI 保留（放干净所有锁之后发）。
- **删 CPU kill 状态**：`CPU_HAS_KILL_STATE`、`CpuU.killed` 及 NI 中的使用一并删除；kill 改由 SyscallPerm / evict 路径保证受害 CPU 不在内核步骤中。删前后量 rlimit。
- **boot IF / evicted 规则**：内核步骤只在 IF=0 下执行；`u_sys_enter` 之后到 `u_sys_exit` 之前不开中断，idle `hlt` 前已 `u_sys_exit`。
  被 evict 的 CPU 在下一次 enter 后看到 `current_thread is None` 返回 CpuIdle，不另设标记；`handle_evict_ipi` 对 ring 0 帧只装默认 cr3。NMI 刷 PCID 路径不动。
- boot：普通 Cargo 编译须保持通过；运行时（QEMU/KVM）已由用户豁免，不作门槛（见 `HANDOFF.md`）。

## 收尾
- 每批：聚焦 → 工作区 + NI（并行，最多两个重任务）→ 单体（单独）对比上一批；风格审查只针对本批改动文件。
- 全部完成后删除本文件。
