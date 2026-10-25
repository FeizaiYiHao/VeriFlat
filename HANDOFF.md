# Handoff — IOMMU 写锁即 IOTLB 脏标记 + iommu_map_4k / iommu_unmap_4k（2026-10-24）

## 现状
- `main`：8bfefdc（IOMMU map/unmap 与 NI）→ 2958a65（第 6 轮证明清理）→ 已批准后续项 a/b/c/e/f/g 的提交（见 `ProofSimplificationNotes.md` Round 6 “后续”）。

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
- 已批准后续项 a/b/c/e/f/g 后：
  - #34648 NI：257 verified / 0 errors。
  - #34649 workspace（17 个结果）：3168 verified / 0 errors，无 warning，cargo 1m49s（与 NI 并行）。
  - #34650 单体（`--num-threads 32 --time --time-expanded --output-json`，无并行任务）：3168 verified / 0 errors，total 66.3 s，SMT 544.9 s，rlimit-run 1,135,582,304。
- 第 6 轮（IOMMU 调用链与绕弯证明清理，见 `ProofSimplificationNotes.md` Round 6）后：
  - #34617 NI：257 verified / 0 errors。
  - #34618 workspace（17 个结果）：3169 verified / 0 errors，无 warning，cargo 1m42s（与 NI 并行）。
  - #34619 单体（`--num-threads 32 --time --time-expanded --output-json`，无并行任务）：3169 verified / 0 errors，total 66.8 s，SMT 547.7 s，rlimit-run 1,148,387,464。
  - 上次集成（`kill_reclaim_iommu_leaves` 拆分前）：#34597 NI 257 / 0；#34598 workspace 3166 / 0；#34599 单体 3166 / 0，66.7 s，SMT 551.9 s，rlimit-run 1,152,392,740。
- 本轮前基线：#34525 单体 3155 / 0，68.8 s，SMT 561.0 s，rlimit-run 1,161,493,270；#34521 NI 257 / 0；#34522 workspace 3155 / 0。

单体 `--time-expanded`（均无并行任务；“—”为该次运行未保留）：

| 函数 | 文件 | #34525 | #34619 | #34650 |
|---|---|---|---|---|
| `syscall_iommu_map_4k` | `syscall_iommu_map_4k.rs` | 1.12 s / 1.89M | 1.19 s / 1.89M | 1.13 s / 1.77M |
| `iommu_map_4k_lock_and_check` | `syscall_iommu_map_4k_check.rs` | 3.0 s / 6.8M | 3.19 s / 11.44M | 1.19 s / 2.23M |
| `iommu_map_4k_result_from_k` | `syscall_iommu_map_4k_trace.rs` | — | — | 0.07 s / 0.18M |
| `mapping_4k_va_range_absent`（新） | `pagetable_seq/pagetable_range.rs` | — | — | 0.05 s / 0.19M |
| `iommu_map_4k_ensure_l1` | `iommu_map_4k_directory_step.rs` | 2.7 s / 5.2M | 1.29 s / 2.94M | 1.47 s / 3.26M |
| `iommu_map_4k_map_one_page` | `iommu_map_4k_leaf_step.rs` | 0.71 s / 1.42M | 0.51 s / 1.25M（#34620 单体模块聚焦） | 0.77 s / 1.58M |
| `syscall_iommu_unmap_4k` | `syscall_iommu_unmap_4k.rs` | 4.5 s / 8.1M | 1.08 s / 1.76M | 1.16 s / 1.89M |
| `iommu_unmap_4k_lock_and_check` | `syscall_iommu_unmap_4k_check.rs` | — | 1.38 s / 2.25M | 1.20 s / 2.14M |
| `kill_reclaim_iommu_leaves`（包装） | `syscall_kill_process_reclaim_release.rs` | 4.9 s / 8.0M | 0.29 s / 0.45M | 0.25 s / 0.43M |
| `kill_reclaim_iommu_hide_leaves` | `syscall_kill_process_reclaim_release.rs` | — | 0.70 s / 1.48M | 0.61 s / 1.35M |
| `kill_reclaim_iommu_flush` | `syscall_kill_process_reclaim_release.rs` | — | 0.81 s / 1.19M | 0.83 s / 1.19M |
| `kill_reclaim_iommu_remove_leaves` | `syscall_kill_process_reclaim_release.rs` | — | 0.98 s / 1.64M | 0.90 s / 1.59M |
| `thread_exit_reclaim_iommu_leaves` | `syscall_thread_exit_reclaim_release.rs` | 2.4 s / 4.0M | 2.38 s / 4.14M | 2.74 s / 4.27M |
| `drain_4k_cache_batch` | `free_4k_page/drain_4k_cache_batch.rs` | — | — | 0.56 s / 1.20M |
| `share_mapping_4k_build_and_share` | `map_4k/share_mapping_4k.rs` | 4.8 s / 7.9M | 4.88 s / 7.65M | 4.87 s / 7.65M |
| `publish_staged_container_root_mutation` | `create_container_from_staged_pages/publish.rs` | — | 3.62 s / 8.90M | 3.40 s / 8.38M |
| `install_one_mmap_4k_directory_page` | `map_4k/mmap_4k_install_one.rs` | — | 3.76 s / 4.89M | 3.52 s / 4.83M |
| `create_process_with_iommu_from_staged_pages` | `create_process_with_iommu_from_staged_pages/create_process.rs` | — | 3.30 s / 5.32M | 3.27 s / 5.32M |
| `ipc_pages_prepare_target` | `syscall_ipc_pages_share.rs` | — | 3.29 s / 4.79M | 3.43 s / 4.86M |
| `ipc_rendezvous_cpu_cross_container` | `syscall_ipc_cpu.rs` | — | 2.49 s / 3.88M | 2.45 s / 3.63M |
| `ipc_pages_check_tables` | `syscall_ipc_pages_check.rs` | — | 1.86 s / 2.66M | 1.72 s / 2.66M |
| `eof_page_object_owner_at` | `create_container_from_staged_pages/eof_process.rs` | — | 1.00 s / 3.38M | 1.04 s / 3.38M |

| 树 | 结果 | rlimit-run | total |
|---|---|---|---|
| 后续项 #34650 | 3168 / 0 | 1,135,582,304 | 66.3 s（无并行任务） |
| 第 6 轮 #34619 | 3169 / 0 | 1,148,387,464 | 66.8 s（无并行任务） |
| kill 拆分前 #34599 | 3166 / 0 | 1,152,392,740 | 66.7 s（无并行任务） |
| 上轮 #34525 | 3155 / 0 | 1,161,493,270 | 68.8 s（无并行任务） |
| 基线 #34350 | 3096 / 0 | 1,109,718,875 | ~64 s |

## map crate 文件布局（`src/kernel/implementation/syscall_iommu_map_4k/`，调用顺序）
- `syscall_iommu_map_4k_lock.rs`：`iommu_map_4k_lock_running_thread`（锁 cpu / P / T）。
- `syscall_iommu_map_4k_check.rs`：`iommu_map_4k_lock_and_check`（参数与 stutter 检查，锁 PT(P) / IT(P) / 2M 窗口；拒绝路径经 `iommu_map_4k_unlock_rejected` / `iommu_map_4k_unlock_thread_rejected` 解锁）。
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
- `assert forall`：map crate 中的两个（`syscall_iommu_map_4k_check.rs`、`syscall_iommu_map_4k_trace.rs`）已随 `mapping_4k_va_range_absent` 删除；`create_process_with_iommu_from_staged_pages/eof.rs` 中一个及其附近裸 `assert` 仍在，未改写。
- #34650 中无 >5 s 的函数（最大 `share_mapping_4k_build_and_share` 4.87 s / 7.65M）。总 wall 66.3 s 仍高于基线 #34350 的 ~64 s（rlimit +2.3%），单样本，未做交替 A/B。
- `iommu_map_4k_lock_and_check` 上下文敏感已基本消失：单体 #34619 11.44M → #34650 2.23M（分 crate 4.15M → 2.33M）；H+F′ 变体不再需要。
- 残余回退：`ipc_rendezvous_cpu_cross_container` +4%（分 crate 3.71M → 3.86M；单体 #34650 3.63M）。单样本中 `iommu_map_4k_ensure_l1`（本文件未改，2.94M → 3.26M）与 `thread_exit_reclaim_iommu_leaves`（已删 remove 循环 `pagetable_c` 块，仍 4.14M → 4.27M）单体 rlimit 上升，未隔离。
- 待批准：kill / thread_exit 共用 exec helper `reclaim_hidden_iommu_4k_leaves`（项 d）。
- `refund_unmap_4k_quota` 缺写持 `pagetable_c` 边界 ensures；补上后可删 `kill_reclaim_iommu_remove_leaves` 与 `thread_exit_reclaim_iommu_leaves` 中 refund 之后的两个 `pagetable_c` 块。
- `allocate_free_2m_page_pop_impl.rs:~119` 仍有既有 exec `reveal(LinkedList::wf_value_list)`。
- `pagetable_seq` 的 `PageTable::mapping_4k_va_range_empty` 已无树内调用方（公开原语，未删）。
