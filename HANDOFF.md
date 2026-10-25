# Handoff — IOMMU 写锁即 IOTLB 脏标记 + iommu_map_4k / iommu_unmap_4k（2026-10-24）

## 现状
- `main` = 8bfefdc（已含 IOMMU map/unmap 与 NI）；第 6 轮证明清理全部未提交（约 45 个源码文件，新文件 `syscall_iommu_unmap_4k_range.rs`、`kernel_step_wrappers/iommu_table_steps.rs`）。

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
- 第 6 轮（IOMMU 调用链与绕弯证明清理，见 `ProofSimplificationNotes.md` Round 6）后：
  - #34617 NI：257 verified / 0 errors。
  - #34618 workspace（17 个结果）：3169 verified / 0 errors，无 warning，cargo 1m42s（与 NI 并行）。
  - #34619 单体（`--num-threads 32 --time --time-expanded --output-json`，无并行任务）：3169 verified / 0 errors，total 66.8 s，SMT 547.7 s，rlimit-run 1,148,387,464。
  - 上次集成（`kill_reclaim_iommu_leaves` 拆分前）：#34597 NI 257 / 0；#34598 workspace 3166 / 0；#34599 单体 3166 / 0，66.7 s，SMT 551.9 s，rlimit-run 1,152,392,740。
- 本轮前基线：#34525 单体 3155 / 0，68.8 s，SMT 561.0 s，rlimit-run 1,161,493,270；#34521 NI 257 / 0；#34522 workspace 3155 / 0。

单体 `--time-expanded`（均无并行任务；“—”为 #34525 未保留）：

| 函数 | 文件 | #34525 | #34619 |
|---|---|---|---|
| `syscall_iommu_map_4k` | `syscall_iommu_map_4k.rs` | 1.12 s / 1.89M | 1.19 s / 1.89M |
| `iommu_map_4k_lock_and_check` | `syscall_iommu_map_4k_check.rs` | 3.0 s / 6.8M | 3.19 s / 11.44M |
| `iommu_map_4k_ensure_l1` | `iommu_map_4k_directory_step.rs` | 2.7 s / 5.2M | 1.29 s / 2.94M |
| `iommu_map_4k_map_one_page` | `iommu_map_4k_leaf_step.rs` | 0.71 s / 1.42M | 0.51 s / 1.25M（#34620 单体模块聚焦） |
| `syscall_iommu_unmap_4k` | `syscall_iommu_unmap_4k.rs` | 4.5 s / 8.1M | 1.08 s / 1.76M |
| `iommu_unmap_4k_lock_and_check` | `syscall_iommu_unmap_4k_check.rs` | — | 1.38 s / 2.25M |
| `kill_reclaim_iommu_leaves`（包装） | `syscall_kill_process_reclaim_release.rs` | 4.9 s / 8.0M | 0.29 s / 0.45M |
| `kill_reclaim_iommu_hide_leaves` | `syscall_kill_process_reclaim_release.rs` | — | 0.70 s / 1.48M |
| `kill_reclaim_iommu_flush` | `syscall_kill_process_reclaim_release.rs` | — | 0.81 s / 1.19M |
| `kill_reclaim_iommu_remove_leaves` | `syscall_kill_process_reclaim_release.rs` | — | 0.98 s / 1.64M |
| `thread_exit_reclaim_iommu_leaves` | `syscall_thread_exit_reclaim_release.rs` | 2.4 s / 4.0M | 2.38 s / 4.14M |
| `share_mapping_4k_build_and_share` | `map_4k/share_mapping_4k.rs` | 4.8 s / 7.9M | 4.88 s / 7.65M |
| `publish_staged_container_root_mutation` | `create_container_from_staged_pages/publish.rs` | — | 3.62 s / 8.90M |
| `install_one_mmap_4k_directory_page` | `map_4k/mmap_4k_install_one.rs` | — | 3.76 s / 4.89M |
| `create_process_with_iommu_from_staged_pages` | `create_process_with_iommu_from_staged_pages/create_process.rs` | — | 3.30 s / 5.32M |
| `ipc_pages_prepare_target` | `syscall_ipc_pages_share.rs` | — | 3.29 s / 4.79M |
| `ipc_rendezvous_cpu_cross_container` | `syscall_ipc_cpu.rs` | — | 2.49 s / 3.88M |
| `ipc_pages_check_tables` | `syscall_ipc_pages_check.rs` | — | 1.86 s / 2.66M |
| `eof_page_object_owner_at` | `create_container_from_staged_pages/eof_process.rs` | — | 1.00 s / 3.38M |

| 树 | 结果 | rlimit-run | total |
|---|---|---|---|
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
- 本轮新增 `assert forall`（`create_process_with_iommu_from_staged_pages/eof.rs`、`syscall_iommu_map_4k_check.rs`、`syscall_iommu_map_4k_trace.rs`）及其中/附近的裸 `assert`，未改写。
- #34619 中已无 >5 s 的函数（最大 `share_mapping_4k_build_and_share` 4.88 s / 7.65M）；`kill_reclaim_iommu_leaves` 拆成包装 + 三个私有 exec 函数后合计 4.77M、最大 0.98 s（拆分前 #34599 为 5.94 s / 8.61M）。总 wall 66.8 s 仍高于基线 #34350 的 ~64 s（+73 个验证项，rlimit +3.5%），单样本，未做交替 A/B。
- 残余回退：`publish_staged_container_root_mutation` rlimit +10%（分 crate 7.32M → 8.09M，原因未隔离）；`ipc_rendezvous_cpu_cross_container` +4%；`iommu_map_4k_lock_and_check` 单体 11.44M / 分 crate 4.15M；实测 H+F′ 变体（helper 移到 `_lock.rs`，删 `rlock_pagetable` 后的 `pagetable_perms_wf_map`）为单体 3.89M / 分 crate 15.55M（#34613/#34614），两种上下文方向相反，未改，待用户选择。
- 需用户批准后才能做：
  - `pagetable_seq` 上新原语 `mapping_4k_va_range_absent`。
  - 删除 `map_shared_page_into_iommu_4k` 的死 ensures。
  - `iommu_table_tlb_entries_present` 加 `#[verifier::opaque]`。
  - kill / thread_exit 共用 exec helper `reclaim_hidden_iommu_4k_leaves`。
  - `publish_objects.rs` 中 `pg_arr` frame ensures 改为只用 post 触发。
  - `link_new_container_into_tree` 与 `LinkedList::wf_map` 的 exec reveal 需新引理才能去掉。
  - `drain_4k_cache_batch` / `reclaim_last_lock_4k_cache_with_room` / `kill_retire_lock_cache` 增边界形 `pagetable_c` ensures，以删余下 remove 循环块。
