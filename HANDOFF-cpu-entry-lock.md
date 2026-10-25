# 实施计划 — CPU 入口锁（IPI 模型）

设计定稿见 `.ai-memory/project_numa_plan.md` "CPU 入口锁"一节。本文件是分步实施计划，做完删除。
基线：main 7fbc98d（lctx 锁序已撤回，锁序为 K 状态形式 0f82379）。

## 0. 先定的两个偏差
- **major 不能字面"低 1"**：`KILLED_LOCK_MAJOR = 0` 已占用（`src/define/lock_id.rs:12`），`PCID_NEEDFLUSH_LOCK_MAJOR = 30001`。
  改为重编号：KILLED 0 → ENTRY_RUNNING 1 → CPU_RUNNING 2 → ENTRY_IDLE 3 → CPU_IDLE 4；ENTRY_OFF 30002 → CPU_OFF 30003
  （pcid_needflush 30001 保持在两者之下）。所有用到 1/2/30002 字面量或常量名的地方跟着改。
- **入口锁不投影到 U**：它是机制不是语义，`kernel_k_to_kernel_u` 不包含它，NI 不受影响。
  CPU 的 kill 标记（`CpuU.killed`，NI 用到 9 处）第一阶段保留不用，最后一步再决定删。

## 1. kernel_core：新对象、新锁族、不变量（约 10 个文件，一个批次）
- `src/cpu/cpu_entry.rs`（新）：`CpuEntry { state: CpuState, container_depth, process_depth, syscall_perm: Option<Tracked<SyscallPerm>>, ipi_perm: Option<Tracked<IpiPerm>> }`，
  `SyscallPerm { cpu_id }` / `IpiPerm { cpu_id }` 为 tracked ghost 结构，只能由 TCB 铸造/销毁。`LockMajorTrait` 按 `state` 给
  ENTRY_* major，深度字段给 lock id 的 container/process。
- `src/kernel/kernel_k_define_spec.rs`：`KernelK` 加 `cpu_entry_arr: LockedArray<CpuEntry, (), (), NUM_CPUS, false>`；`KernelObjId::CpuEntry(CpuId)`；
  `typed_lock_maps_aligned`、`all_objects_unlocked`、`held_locks_order_below`（入口锁 major 低于 CPU 锁，所有"held cpus below X"子句同步）。
- `src/locks/local_context.rs`：第 25 个锁族 `cpu_entry_lock_map`，`no_locks_held`、`lock_id_acyclic`、`typed_lock_maps_unchanged/inserted`、`update_lock_id`。
- 新 `*_wf`（`src/kernel/cpu_management/` 或 `process_management/`）：`cpu_entry_wf`：对每个 cpu，entry 的 state/depths == cpu 的；
  `state != Off ∧ entry 未写锁 ⇒ 两个 perm 都 Some`；`state is Off ⇒ syscall_perm is None`。加进 `KernelK::inv` 和 `init.rs` 的初始状态
  （boot CPU：Running/Idle，两个 perm 在锁里；未启动 CPU：Off，只有 IpiPerm）。
- `src/kernel/implementation/locker_unlocker/locker_unlocker_cpu_entry.rs`（新）：`wlock_cpu_entry` / `wunlock_cpu_entry`，
  以及 kill 用的锁序豁免分支（复制 `locker_unlocker_cpu.rs:9` `wlock_cpu` 的 `killer_held_context` 分支）。
- 这一步先让"入口锁从不被持有"的平凡不变量成立，工作区全绿后再进 2。

## 2. 边界契约：syscall 全程持有自己的入口锁（机械批量，约 35 个入口 + 边界包装）
- 定义 `LocalContext::holds_only_cpu_entry(cpu_id)`（入口锁表 = {cpu_id ↦ Write}，其余表空）。
- 每个 `syscall_*` 入口和 `cpu_offline_check` / `syscall_schedule` / `rebalance_pull` / `cpu_online_resume` 的 `requires old(lctx).no_locks_held()`
  改成 `holds_only_cpu_entry(cpu_id)`，ensures 同样；`release_and_finish_syscall.rs`、`kernel_step_wrappers/boundary.rs`、
  `no_locks_held_imply_all_objects_unlocked` 改成对应形式（K→U 边界包装只要求除入口锁外为空）。
- 新原语 `cpu_entry_enter(krnl, cpu_id)`（写锁自己入口锁，取出两个 perm 交给 lctx 的 tracked 字段）和 `cpu_entry_exit`（放回）。
  `halt_until_ipi` 的 requires 保持 `no_locks_held`（入口锁已放）。
- 拿到入口锁后由 `syscall_schedule`/各入口在拿 CPU 锁后检查 `current_thread is None`（自旋期间被 evict）→ 返回 CpuIdle。

## 3. TCB 契约（`src/cpu/`）
- `cpu_ipi.rs`：`send_ipi(target, Tracked(&IpiPerm))` requires `perm.cpu_id == target`；
  `atomic_pcid_cr3.rs:63` `evict_remote_cpu` 同样要 IpiPerm，删掉注释里的 virtual lock TODO。
- 新 TCB：`mint_syscall_perm(target) -> Tracked<SyscallPerm>` requires 调用者写持 target 入口锁且 target Off、同一临界区内发布 Idle；
  `collect_syscall_perm(Tracked<SyscallPerm>)` 销毁。两者 `external_body`，加进 TCB 清单。
- `cpu_def.rs:403` `evict_remote` 增加 IpiPerm 参数。

## 4. 内核路径（约 10 个文件）
- kill：`syscall_kill_process_victim.rs:253` `kill_evict_running_victim`：`wlock_cpu_entry(remote)`（豁免分支）→ `wlock_cpu(remote)` → 取 IpiPerm →
  `evict_remote` → 放回 → 解锁两把；evict 后同一临界区 rekey 入口锁（state Idle）。CPU 标记调用保留但可不再依赖。
- 上线 `syscall_cpu_online.rs` / `cpu_online_child_locked.rs`：`wlock_cpu_entry(target)`（Off major）→ `wlock_off_cpu` → `publish_idle_from_off` →
  `mint_syscall_perm` 存入 → rekey 入口锁（Idle）→ 取 IpiPerm → 解锁 CPU → `send_ipi` → 放回 IpiPerm → 解锁入口锁。
- 下线 `cpu_offline_check.rs`：走到 Off 时（已持自己入口锁）`collect_syscall_perm`，rekey（Off），放锁，boot 层 `hlt`。
  `syscall_cpu_offline_request.rs:142` / `cpu_offline_request_child_locked.rs:185`：改成 `wlock_cpu_entry(target)` → 取 IpiPerm → `send_ipi` → 放回 → 解锁（lctx 为空，无锁序问题）。
- `cpu_online_resume.rs`：requires 持自己入口锁；锁里没有 SyscallPerm → 放锁返回 StillOff（杂散唤醒）；有 → 取出，清 hw_halted。
- rekey 点清单（和 CPU 锁同步）：schedule 切进程、evict、上线、下线、kill 标记（若保留）。

## 5. boot（`boot/kernel/src/syscalls/mod.rs`、`platform.rs`、`cpu.rs`）
- `sys_entry`（:129）/ 中断 trampoline 存帧后：`sti` → `cpu_entry_enter` → `cli` → 分发；`restore_frame`（:186）前 `cpu_entry_exit`。
- `run_idle`（约 :705）：每轮 enter → offline_check/schedule/rebalance → exit → `sti; hlt; cli`。
- `wait_until_online`：Off CPU 每次醒来 enter（开中断自旋）→ `cpu_online_resume` → 无 perm 则 exit + `hlt`。
- `timer_interrupt` / `wake_interrupt` 从 ring 3 进来的路径同样 enter/exit 包裹；ring 0 帧只 EOI。
- `handle_evict_ipi`：对入口自旋中的 ring 0 帧也装默认 cr3（已如此），`evicted` 判定改由第 2 步的 `current_thread is None` 检查承担。
- NMI 刷 PCID 路径不动。

## 6. 收尾
- 删 CPU kill 标记（`CPU_HAS_KILL_STATE`、`CpuU.killed`、NI 9 处）——单独一轮，先量 rlimit。
- 验证顺序：1 → 工作区；2 → 工作区；3+4 → 相关包聚焦后工作区；5 → boot check + KVM 三阶段；最后单体对比 7fbc98d 基线、NI、风格审查。
- 预计成本：每次 syscall 多一对本地无争用锁操作 + `sti`/`cli`；证明侧新增一个锁族会让所有 `lock_id_acyclic`/`typed_lock_maps_*` 多一个合取项，预期 rlimit +1–2%，做完量。
