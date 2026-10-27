# 实施计划 — 具体锁序 + 动态容器 + 锚点 DID + Cpu 内含 SyscallPerm

状态：**已批准**；Batch 1 已完成；Batch 2 已实施并完整验证（workspace #34945 3189 / 0、NI #34944 266 / 0、单体 #34946 3189 / 0，详见 `HANDOFF.md`）；Batch 3–4 待实施。权威细节是用户在对话中批准的实施计划；本文件只记录交接所需的结构与规则，做完删除。

- 取代：原"独立 CpuEntry 入口锁（IPI 模型）"方案已放弃——不新增 `CpuEntry` 对象、第 25 个锁族、`IpiPerm`、`mint/collect_syscall_perm` 或 ENTRY_* major。
- 被放弃方案的 step 0/1 实现保存在 `/local/home/xiangdc/veriflat-parked/cpu-entry-step01.patch`（原 `stash@{0}` "parked: cpu-entry step 0/1 (ws #34657 3181/0, NI #34658 257/0)"，Batch 1 推送后 drop）。只作参考，不要 apply。
- 基线：Batch 1 提交。

## 四个批次（顺序固定，每批工作区 + NI + 单体全绿后再进下一批）
1. **Batch 1（已完成）**：mmap 在 read miss → fill 之间保留 cpu/T 写锁（`Mmap4kHold` / `Mmap4kRelease` U/NI 标签与两条 trace spec），外加证明清理。见 `HANDOFF.md`。
2. **Batch 2（已实施，完整验证通过）— 具体锁序 + 动态容器**：OwnerSource/LockControl 规则、删除 owner 通配、`ErrorContainerLockOrderConflict`。
3. **Batch 3 — 锚点 DID**：按用户批准的方案实施；仓库内尚无细节记录，开工前与用户核对语义。
4. **Batch 4 — SyscallPerm 放进 Cpu + IPI / kill 状态收尾**：`Cpu.syscall_perm`、入口包裹、删 offline kick、保留 online wake、删 CPU kill 状态、boot IF/evicted 规则。

## Batch 2：具体锁序 + 动态容器（已实施，完整验证通过）
- `LockOwnerId` 只有 `High | Some(usize) | None`，无通配；`LockId` 结构相等，按 (container, process, major, minor)
  具体字典序比较，owner 序 `High < Some(小) < … < Some(大) < None`。`None` 是有意的"无 owner"分量，不是兜底。
- **OwnerSource**：`Payload`（payload 自身 owner，`ROT = ()` 默认）、`Fixed(owner)`（只读数据的固定 owner）、
  `Dynamic`（当前动态写获取记录的具体 owner，否则 `None`）。被 killer 标记的对象两个分量都报 `High`。
  各锁族的具体 owner 见 `LockId.md`。
- **Dynamic 只用于 Container 的 process 分量**，是获取 / 来源策略，不是最终 owner。请求 `r` 时在锁 guard 下：
  Killed 优先；活跃持有者 `h < r` 立即 `DepthConflict`；`h >= r` 等待并重查；空闲则获取并记录
  `LockControl::DynamicProcess(r)`；unlock 清除。
- 普通 Container 加锁请求当前进程深度，冲突时 stutter 返回 `ErrorContainerLockOrderConflict`（ABI 下标 49，
  result spec 中紧跟 ContainerKilled）；标记更深容器请求 `High`；新建子容器以 `Some(0)` 写持有发布；
  U 投影 `ContainerU.lock_process_owner`。
- **OfflineFlag** 固定 owner `(Some(container_depth), None)`。自 offline：持 cpu 探测请求位后放 flag →
  持 cpu 跨边界（Hold）→ 锁 process / thread → 重新获取 flag 并重查。完整 trace 为 Hold + Release 或
  Hold + went-off；决策结果与 flush 标签都取边界后的具体状态。

## Batch 3：锚点 DID
- 待实施。语义以用户批准的计划为准；本文件不补写未记录的细节。

## Batch 4：SyscallPerm 放进 Cpu + IPI / kill 状态
- 待实施。
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
