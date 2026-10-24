# Handoff — IOMMU 写锁即 IOTLB 脏标记 + iommu_map_4k / iommu_unmap_4k（2026-10-24）

## 现状
- `main` = 0f82379；本轮改动全部未提交（工作区约 110 个文件 + 新 crate、新目录）。

## 内容
- 删除 `iommu_table_lock_wf`（`src/kernel/memory_management/iommu_table_lock_spec.rs`、`page_iommu_table_wf_eq.rs` 中相关引理）。
- IOTLB 模型：IOMMU 表的写锁标记其挂接域为脏。
  - `iommu_tlb_wf_spec` 增 present 子句；`iommu_table_tlb_entries_present`（`src/kernel/iommu_tlb_management/iotlb_wf_spec.rs`、`src/iommu/iotlb.rs`）。
  - step boundary 转发（`src/kernel/kernel_step_wrappers/boundary.rs`、`kernel_step_wrappers.rs`）。
  - `flush_all_iotlb` / `flush_iommu_tlb_for_table`（`map_4k/flush_iommu_tlb.rs`、`_eof.rs`）。
- thread_exit / kill_process 回收三阶段：CPU 叶 → IOMMU 叶（只清 present）→ 一次 IOMMU flush → 移除并退页。
  - `thread_exit_reclaim_iommu_leaves`、`kill_reclaim_iommu_leaves`（`*_reclaim_release.rs`）；step spec `thread_exit_iommu_flush_step`、`kill_process_iommu_flush_step`。
- 新系统调用：
  - `syscall_iommu_map_4k`（crate `veriflat_syscall_iommu_map_4k`；`syscall_iommu_map_4k/`；`map_4k/map_iommu_4k*.rs`）。
  - `syscall_iommu_unmap_4k`（crate `veriflat_syscall_iommu_unmap_4k`；`syscall_iommu_unmap_4k/`）。
- NI：`ThreadExitIommuFlush`、`KillProcessIommuFlush`、`IommuUnmap4k*`、`IommuMap4k{Enter,Directory,Leaf,Exit}` 标签（`theorem.rs`、`ni_thread_exit.rs`、`ni_kill_process.rs`、`ni_iommu_unmap_4k.rs`、`ni_iommu_map_4k.rs`）。
  - `isolation.rs`：`domain_4k_only` 只禁 2M/1G，允许 IOMMU 4K 映射；`memory_iso` 四个子句覆盖页表与 IOMMU 表 4K 项的两两组合。
  - `Share4kLeaf` 诚实对端假设扩展为：另一域既不在页表也不在 IOMMU 表中映射被共享页。
  - `mmap_4k_leaf_step` 新增子句：新页不在任何 IOMMU 表中（`mmap_4k_leaf_step_from_u` 现取 `krnl: &KernelK`）；`ni_mmap_4k.rs`、`ni_thread_exit.rs`、`ni_kill_process.rs`、`ni_ipc.rs`、`ni_share_4k.rs` 相应修复。
- boot：dispatcher 增 `NR_IOMMU_MAP_4K`(45) / `NR_IOMMU_UNMAP_4K`(46) 分支与三个错误码；`vsys` 增 `sys_iommu_map_4k` / `sys_iommu_unmap_4k`。
- `SystemCalls.md` §7a/§7b/§17/§18/§19 同步。

## 验证
- #34486 包 `veriflat_syscall_iommu_map_4k`：22 / 0。#34434 包 `veriflat_syscall_iommu_unmap_4k`：17 / 0。
- 删除测试：`syscall_iommu_map_4k` 中 `iova_range` 的 forall 断言删除后仍绿（#34519），已删；`mmap_4k_leaf_step_from_u` 的三个 reveal 同时删除即红（#34520），保留。
- #34522 workspace（8 个 crate 失效重检，17 个结果）：3155 verified / 0 errors，无 warning，cargo 1m51s。
- #34523 单体（`--num-threads 32 --time --time-expanded --output-json`，前约 1 分钟与 workspace 并行）：3155 verified / 0 errors，作为正确性运行；计时以 #34525 为准。
- #34525 单体计时（同参数，无并行任务）：3155 verified / 0 errors，total 68.8 s，SMT 561.0 s，rlimit-run 1,161,493,270。
- #34521 NI：257 verified / 0 errors，total 30.7 s。

单体 #34525 `--time-expanded`（无并行任务）：

| 函数 | 文件 | SMT | rlimit |
|---|---|---|---|
| `syscall_iommu_map_4k` | `syscall_iommu_map_4k.rs` | 1.12 s | 1.89M |
| `iommu_map_4k_lock_and_check` | `syscall_iommu_map_4k_check.rs` | 3.0 s | 6.8M |
| `iommu_map_4k_ensure_l1` | `iommu_map_4k_directory_step.rs` | 2.7 s | 5.2M |
| `iommu_map_4k_map_one_page` | `iommu_map_4k_leaf_step.rs` | 0.71 s | 1.42M |
| `iommu_map_4k_map_range_and_exit` | `iommu_map_4k_range.rs` | 0.35 s | 0.67M |
| `iommu_map_4k_exit` | `iommu_map_4k_exit.rs` | 0.55 s | 0.91M |
| `kill_reclaim_iommu_leaves` | `syscall_kill_process_reclaim_release.rs` | 4.9 s | 8.0M |
| `thread_exit_reclaim_iommu_leaves` | `syscall_thread_exit_reclaim_release.rs` | 2.4 s | 4.0M |
| `syscall_iommu_unmap_4k` | `syscall_iommu_unmap_4k.rs` | 4.5 s | 8.1M |
| `share_mapping_4k_build_and_share`（既有） | `map_4k/share_mapping_4k.rs` | 4.8 s | 7.9M |

| 树 | 结果 | rlimit-run | total |
|---|---|---|---|
| 本轮 #34525 | 3155 / 0 | 1,161,493,270 | 68.8 s（无并行任务） |
| 本轮 #34523 | 3155 / 0 | 1,161,493,270 | 74.9 s（与 workspace 部分并行） |
| 本轮 #34485 | 3155 / 0 | ≈1,162M | 68.8 s |
| 基线 #34350 | 3096 / 0 | 1,109,718,875 | ~64 s |

## map crate 文件布局（`src/kernel/implementation/syscall_iommu_map_4k/`，调用顺序）
- `syscall_iommu_map_4k_lock.rs`：`iommu_map_4k_lock_running_thread`（锁 cpu / P / T）。
- `syscall_iommu_map_4k_check.rs`：`iommu_map_4k_lock_and_check`（参数与 stutter 检查，锁 PT(P) / IT(P) / 2M 窗口）。
- `syscall_iommu_map_4k.rs`：入口 `syscall_iommu_map_4k`（enter step）。
- `iommu_map_4k_range.rs`：`iommu_map_4k_map_range_and_exit`（逐页循环）。
- `iommu_map_4k_leaf_step.rs`：`iommu_map_4k_map_one_page`（调 `iommu_map_4k_ensure_l1` 后发布一个 IOMMU 叶）。
- `iommu_map_4k_directory_step.rs`：`iommu_map_4k_ensure_l1` → `iommu_map_4k_install_directory`（每级一个目录页 step）。
- `iommu_map_4k_exit.rs`：`iommu_map_4k_exit`（exit step，解锁）。
- 另：`syscall_iommu_map_4k_spec.rs`（U spec）、`syscall_iommu_map_4k_trace.rs`（K→U 与 trace 引理）；页表层在 `map_4k/map_iommu_4k*.rs`。

## 环境
- 用 `ulimit -v 31457280` 代替 `systemd-run`。
- boot 未编译（缺 nasm），dispatcher / vsys 为手写对照 mmap/unmap 分支。

## 剩余项
- `iommu_tlb_wf_spec` 依赖 `CAP.CM = 0`（不缓存 not-present 项）。
- boot 代码未编译（缺 nasm）。
- 本轮新增 `assert forall`（`create_process_with_iommu_from_staged_pages/eof.rs`、`syscall_iommu_map_4k_check.rs`、`syscall_iommu_map_4k_trace.rs`）及其中/附近的裸 `assert`，未改写。
- 无并行的 #34525 中已无 >5 s 的函数（最高 `kill_reclaim_iommu_leaves` 4.9 s、`share_mapping_4k_build_and_share` 4.8 s）；#34523 的 6.9 s / 6.6 s 系并行 workspace 干扰。总 wall 68.8 s 仍高于基线 #34350 的 ~64 s（+59 个验证项，rlimit +4.7%），单样本，未做交替 A/B。
