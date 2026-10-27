# Handoff — Batch 3 锚点 DID（检查点，未完成）

状态：**部分完成的检查点，按用户要求暂停收尾**。split workspace 与 NI 均为红，未跑 Batch 3 单体；不得声称 Batch 3 完成或单体通过。
基线：Batch 2 提交 `2011fb98c04becad78fc2ee4db8705c6b1f6e136`（已推送）。Batch 4 未开始。完成后用最终结果替换 / 删除本文件。

## 已完成代码
- `PageTable` / `PageTableU` 携带 `did`；`ProcessRO` 镜像 `iommu_table_ptr`。
- 根表：任意 DID 的 context；attach 先写上层、最后写 P，detach 先清 P（trusted store）。
- 硬件检查：`CAP.CM` / `RWBF` fail-closed，CAIG / IAIG 检查，DID 范围检查，只按 domain 的 hook。
- 按 BDF 键的 context cache；组合失效按 `did` 过滤所有缓存 BDF；按 domain 的 IOTLB-only 失效。
- anchor / cache 不变式；重锚定确定性地取字典序最小的剩余 BDF。
- 路径：首次 attach、单次 IPC 转移重锚、thread-exit detach-all、kill reassign-detach-all；普通 unmap 选择性 flush；
  detach 后直接回收 present leaf。
- 终态迁移：PCI、IPC PCI、IOMMU-unmap、kill、thread-exit；kill / thread-exit 删 IOMMU-flush 标签、保留 leaf 标签；NI 部分迁移。

## 新增 / 变更 TCB 边界（需写入 TCB 清单）
- 根表 publish / clear 的有序 volatile 写原语（publish：upper-first / P-last；clear：P-clear-first）。
- 新增 IOTLB-only 按 domain 失效原语及其 FFI。
- 变更契约 `IommuTLB::invalidate_domain`：过滤掉所有标记为该 DID 的 BDF context cache 项。
- `IommuTLB::inv` 现校验 BDF cache 的键与 DID。
- boot（`boot/kernel/src/iommu.rs`）：CAIG / IAIG 的 `granularity_covers` 检查、RTADDR 检查、越界即 panic 的 `domain_id`、
  CAP.CM / RWBF fail-closed。

## 聚焦绿（只代表各自范围）
core anchor #34975 / #34977；map direct reclaim #34989；map package #35078；PCI #35021；IOMMU-unmap #35052；
IPC PCI #35071；thread-exit #35043；kill #35046；core wrappers #35001 / #35064 / #35066；init #35055。

## 最新集成状态（当前事实）
- 全 workspace #35088：3203 verified / 6 errors，所有包都跑到。
  - `veriflat_syscall_iommu_map_4k` 2 个：`syscall_iommu_map_4k_trace.rs` 的 leaf 与 directory K→U 调用缺 DID 保持事实。
  - `veriflat_syscall_kill_process` 4 个：三个 EOF 闭合缺新 DID / 根表 framing —
    `kill_retire_table_page_eof`（`syscall_kill_process_retire_pages_eof.rs`）、
    `kill_reclaim_unmapped_iommu_4k_page_scoped_eof`、`kill_retire_table_page_scoped_eof`（`syscall_kill_process_reclaim_scoped_eof.rs`）；
    一个 `kill_container_retire_unlock` 页权限前置条件（`syscall_kill_container/syscall_kill_container_retire_commit.rs`）。
- 冷启动完整 NI #35087：259 verified / 3 errors，`ni_ipc.rs` 中 `ipc_pages_lock_tables_step_iso`、`ipc_pages_check_step_iso`、
  `ipc_pages_unlock_tables_step_iso` rlimit。
- 无 Batch 3 单体（split + NI 红）。上述聚焦绿不改变 #35088 / #35087 的结果。
- boot 编译（检查点之后）：`cd boot && cargo +1.98.1 check -p kernel` exit 0，9.38 s，改动的 `boot/kernel/src/iommu.rs` 无 warning。
  boot 运行时（QEMU / KVM）已豁免，未运行。

## 已知证明纪律债（审查发现，本未完成检查点不阻塞，收尾时须修）
- `reclaim_detached_iommu_4k_page` 的 exec 中 `reveal(process_iommu_table_match)`。
- kill container 路径 exec 中 `reveal(iommu_table_tlb_entries_present)`。
- `iommu_table_map_set_did` 中重的 `*_wf` reveal。

## 剩余工作与文件归属（互不重叠）
1. map_4k trace（`src/kernel/implementation/syscall_iommu_map_4k/syscall_iommu_map_4k_trace.rs`，必要时其 `*_spec.rs`）：补 DID 保持事实给 leaf / directory K→U。
2. kill（`src/kernel/implementation/syscall_kill_process/*_eof.rs`、`*_spec.rs`）：三个 EOF 的 DID / 根表 framing 进 S；
   kill_container（`src/kernel/implementation/syscall_kill_container/syscall_kill_container_retire_commit.rs`）：页权限前置。
3. NI（`noninterference/src/ni_ipc.rs`）：三个 `ipc_pages_*_step_iso` rlimit；完成 NI 迁移剩余部分（`noninterference/src/` 其余文件归此项）。
4. 清理（`src/iommu/`、`boot/kernel/src/iommu.rs`、`src/kernel/iommu_tlb_management/`）：确认无调用方后删全局 flush 原语
   `flush_all_iotlb` / `veriflat_iommu_flush_all_iotlb` 及 hook；单 BDF `RootTable::detach` 当前仍被
   `detach_owned_contexts` 与 `iommu_subsystem_mutation.rs` 调用，核对后再决定是否删。
5. 全量风格 / 语义审查（只针对本批改动文件），含上节三处证明纪律债。
6. 文档（只由一个 agent 改）：`SystemCalls.md`、`Methodology.md`、`LockId.md`、`.ai-memory/project_iommu_identity_and_static_root_table.md`。
不得新增未经批准的 framing spec / 引理（EOF S 及其闭合函数除外，见 `AGENTS.md`）。

## 下一步命令
```sh
ulimit -v 31457280
./verify-workspace.sh --package veriflat_syscall_iommu_map_4k -- --verify-only-module <mod>   # 项 1
./verify-workspace.sh --package veriflat_syscall_kill_process -- --verify-function <fn>       # 项 2
noninterference/verify-ni.sh                                                                 # 项 3
# 全绿后：并行（最多两个重任务）
./verify-workspace.sh
noninterference/verify-ni.sh
# 然后单独、无并发：
./verify.sh --num-threads 32 --time --time-expanded --output-json
git diff --check
```

## 注意
- `.verus-log/verify-count` 不属于检查点，永远不要 stage / 提交；`noninterference/.verus-solver-log/` 也不提交。
