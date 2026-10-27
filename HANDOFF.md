# Handoff — Batch 1：mmap hold/release + 四组证明清理（2026-10-25）；Batch 2 已实施并完整验证；Batch 3 为部分完成检查点，见 `HANDOFF-anchor-did.md`

## Batch 1 现状
- Batch 1 作为 02ad734（CPU 入口锁实施计划；该计划已被替换，见 `HANDOFF-cpu-entry-lock.md`）之上的一个提交发布。
- 被放弃方案的 step 0/1 补丁保存在 `/local/home/xiangdc/veriflat-parked/cpu-entry-step01.patch`；对应
  `stash@{0}`（"parked: cpu-entry step 0/1 (ws #34657 3181/0, NI #34658 257/0)"）在 Batch 1 推送后 drop。

## Batch 1 内容
- **mmap_4k hold/release**（`syscall_mmap_4k/`、`kernel_step_wrappers/boundary.rs`、`noninterference/src/{ni_mmap_4k,theorem}.rs`）：
  - read section 发现 R 的某 2M 窗口缺 L2 页时只放 `PT(P)`（无 rlock→wlock 升级），cpu / T 写锁一直保留到 fill section，
    记为 lock-only 的 `Mmap4kHold` step；fill section 拒绝 R 时放 `PT(P)` / T / cpu，记为 `Mmap4kRelease`。
  - 新 U spec：`mmap_4k_hold_step{_pre}`、`mmap_4k_release_step{_pre}`、trace spec `mmap_4k_trace_after_hold`、`mmap_4k_syscall_failure_trace`；
    `*_from_u` / trace 组合引理在 `syscall_mmap_4k_trace.rs`；通用 K→U 引理 `kernel_cpu_thread_lock_states_changed_implies_u_step` 在 `boundary.rs`。
  - 结果锚点：`ret.1` 是决定结果的 section 的起点（hold 后为 fill section 起点）。NI 新增 `Mmap4kHold` / `Mmap4kRelease` 标签及其 `*_lr` / `*_iso` 引理。详见 `SystemCalls.md` §6。
- **证明清理**（见 `ProofSimplificationNotes.md` “Batch 1 后续”）：
  - `refund_unmap_4k_quota`：三层 helper 与循环不变式加写持 `pagetable_c` 边界形 ensures；删 kill / thread_exit 中 refund 之后的四个 `pagetable_c` 块。
  - `create_process_with_iommu_from_staged_pages/eof.rs`：删 `assert forall` 与 36 行种子断言，`pagetable_window_holders_hold_pagetable` 直接两个 reveal 闭合。
  - `allocate_free_2m_page_pop_impl.rs`：删冗余断言及 exec `reveal(LinkedList::wf_value_list)`；无需新增 `wf_value_list_at`。
  - `pagetable_seq`：删无调用方的顺序版 `PageTable::mapping_4k_va_range_empty`、其私有 spec 与 broadcast 引理；`PageTableC` 并发版保留。
- **普通 Rust 编译修复（boot 用）**：`map_iommu_4k_spec.rs` 中只被 ghost 代码用的 `mmap_4k_installed_directory` import 加
  `#[cfg(verus_keep_ghost)]`；`iommu_map_4k_range.rs` 的 `#[verifier::loop_isolation(false)]` 改为
  `#[cfg_attr(verus_keep_ghost, ...)]`。无语义变化；聚焦 #34692（spec-only，0 / 0）、#34693（循环函数，1 / 0）。

## Batch 1 验证（最终集成）
- #34689 workspace（17 个结果，与 NI 并行）：3172 verified / 0 errors，无 warning，cargo 1m43s。
- #34690 NI：262 verified / 0 errors（u_facts 1 + noninterference 261），1m24s。
- #34691 单体（`--num-threads 32 --time --time-expanded --output-json`，无并行任务）：见下表。
- Batch 1 先前分段运行：mmap focused/workspace/NI/单体 #34662/#34668/#34669/#34670（单体 3174 / 0）；refund #34672/#34676/#34679；
  pagetable_seq #34674；allocate_free_2m #34687；create_process_with_iommu #34688。

| 树 | 结果 | total | SMT | rlimit-run |
|---|---|---|---|---|
| Batch 1 #34691 | 3172 / 0 | 66.1 s | 547.0 s | 1,138,176,482（+0.23%） |
| Batch 1 mmap-only #34670 | 3174 / 0 | — | — | — |
| Batch 1 基线 #34650 | 3168 / 0 | 66.3 s | 544.9 s | 1,135,582,304 |

Batch 1 计数：mmap +6，删除顺序版 `mapping_4k_va_range_empty` exec 与 broadcast 引理 −2。单样本，未做交替 A/B。
Batch 1 #34691 无 >5 s 函数；前五：`share_mapping_4k_build_and_share` 4.33 s / 7.65M、`map_one_mmap_4k_page` 3.87 s / 5.52M、
`install_one_mmap_4k_directory_page` 3.48 s / 4.83M、`ipc_pages_prepare_target` 3.33 s / 4.86M、`create_process_with_iommu_from_staged_pages` 3.25 s / 5.32M。
mmap 新路径：`mmap_4k_try_read_enter` 3.04 s / 4.78M、`mmap_4k_fill_enter` 2.32 s / 3.87M。

## 环境
- 用 `ulimit -v 31457280` 代替 `systemd-run`。
- **boot**：上述两处 cfg 修复后，普通 Cargo boot 编译成功。运行时未执行：主机 QEMU 3.1 加载 multiboot2 镜像时在进入 guest 前报
  `linux kernel too old to load a ram disk`，没有 guest 运行；用户已豁免 boot 运行时，不再作为门槛。未声称任何 KVM / QEMU 通过。

## Batch 2（已实施，完整验证通过）
- 最终验证（全绿）：冷启动 split workspace #34945 3189 verified / 0 errors；冷启动完整 NI #34944 266 verified / 0 errors
  （NI 265 + u_facts 1）；无并发单体 #34946 3189 / 0，total 67.294 s，SMT 571.483 s，rlimit 1,175,192,647。
  上文 Batch 1 运行编号不覆盖 Batch 2 语义；未执行 QEMU / KVM 运行时。
- 具体锁序 + 动态容器：`LockOwnerId` 为 `High | Some | None`、`OwnerSource`、动态 Container 获取、
  `ErrorContainerLockOrderConflict`（ABI 下标 49）、OfflineFlag 固定 owner 与自 offline 的 Hold 边界。
  设计摘要见 `HANDOFF-cpu-entry-lock.md`，锁 owner 映射见 `LockId.md`。

## Batch 3（部分完成检查点，未验证通过）
- 基线 Batch 2 提交 `2011fb98c04becad78fc2ee4db8705c6b1f6e136`。按用户要求在未完成状态收尾；详情、剩余项与下一步命令见 `HANDOFF-anchor-did.md`。
- 最新：workspace #35088 3203 / 6 errors（iommu_map_4k trace 2、kill_process 4）；冷启动 NI #35087 259 / 3 errors（`ni_ipc` rlimit）；
  无 Batch 3 单体。不得声称 Batch 3 完成。
- boot：检查点后 `cd boot && cargo +1.98.1 check -p kernel` exit 0（9.38 s，`boot/kernel/src/iommu.rs` 无 warning）；运行时豁免，未运行。
- 新增 / 变更 TCB 边界与已知证明纪律债（3 处 exec / 重 wf reveal，本检查点不阻塞）见 `HANDOFF-anchor-did.md`。
  Batch 4 未开始；`.verus-log/verify-count` 不提交。

## 剩余项
- Batch 3 收尾（`HANDOFF-anchor-did.md`）；Batch 4（`HANDOFF-cpu-entry-lock.md`，未开始）：Cpu 内含 SyscallPerm 与 IPI / CPU kill 状态收尾。
- 既有遗留：`iommu_tlb_wf_spec` 依赖 `CAP.CM = 0`；待批准 kill / thread_exit 共用 exec helper `reclaim_hidden_iommu_4k_leaves`（项 d）；
  `ipc_rendezvous_cpu_cross_container` 残余 +4%。
