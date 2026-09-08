# Proof 清理记录

本轮按已确认方案清理代码、契约与证明。核心语义、锁模型、公共 syscall 和九个 split crate 的边界保持不变。新增 framing spec 必须逐个先向用户展示完整定义并获得批准；该规则已写入 `AGENTS.md`，性能理由也不豁免。

## 契约与调用链

| 审计项 | 实施内容 |
| --- | --- |
| F01 页转移 transition framing | 删除 framing spec 与四个专用闭合 helper，在修改点直接证明。57 次逐个删除实验移除 15 个闭合断言，另 5 次实验删除 5 个冗余 reveal。 |
| F02 process quota framing | 保留已批准的类型关系。六类消费者按实际读取的 domain、rodata、pagetable、pcid、线程列表等字段收窄，不再一律要求整个 quota framing 包。 |
| F03 allocator quota framing | 保留类型关系。free-page-pointer 消费者只读 domain、global pool 和各 CPU cache 的内容，不再要求无关的 owner/depth。 |
| F04–F05 Kernel context wrapper | 删除 process/thread/container 的三个 Kernel context spec。七个保留引理直接写出条件，删除 61 条无关字段相等前置条件。 |
| F06–F09 类型级 invariant/quota 关系 | 保留已批准的现有类型关系和必要复用。此次授权不构成添加新 framing 的许可。 |
| F10 thread/endpoint memory bundle | 删除 Kernel bundle，使用现有三个 Thread quota 关系，直接写出 maps、domain 和 staging-cache 条件。 |
| F11 page memory context | 删除 wrapper，保留消费者引理及其直接依赖。 |
| F12 staged-page ensures | 删除 spec，将真实后置保证放到两个 producer。 |
| F13–F14 staged-page requires | 删除两个各只有一个用户的 requires wrapper。 |
| F15–F16 mmap/share held context | 删除两个 held-context spec。契约直接展示所有权、持锁和 permission 条件，删除重复条款，调用点按失败的具体义务保留窄断言。 |
| F17 old-or-low | 删除两个未使用的 spec 与两个 proof helper，共 268 行旧链路。 |
| F18 held process owning containers | 保留真实的跨边界持锁保证。 |
| F19–F20 endpoint-reference-added | 删除两个 spec 和两个 single-update 打包 helper；在 descriptor 更新和引用计数变更处直接证明。 |
| F21 page-map-write context | 删除 `page_map_write_lctx_ensures`，在 12 个写操作直接列出五项保证；保留 `typed_lock_maps_unchanged`。 |

全库静态扫描覆盖 233 个 Rust 文件、1,243 个 requires/ensures 区块，删除了 60 条完全重复的条款；另检查 41 个 loop-invariant 区块，删除 22 条重复条件。此数字描述语法级重复扫描；深入调用链审查与删除验证集中在上表和以下热点，并不表示每个函数的每一条契约都已证明最小化。

## 六组优化

1. `new_process`：两个 create producer 直接给出真实的 lock-id-set 删除／插入结果和新对象 lock major。普通与 IOMMU 发布路径用该结果关闭锁上界，删除 IOMMU 专用包装 helper。没有增加 caller 的前置条件。
2. `new_container`：固定八元素的索引证明删除八路分支与 nonlinear arithmetic；七个 remainder 中间量缩为四个，通过现有 Map 相等和 submap 传递证明。
3. PCID 初始化：constructor 直接给出完整空序列等式，调用点删除嵌套 `assert forall`；同时删除 constructor 中被序列等式覆盖的逐槽空集后置条件。页转移 proof 另有逐项删除记录。
4. allocator：4K/2M 原先相同的五个尺寸无关 spec 共享到 `allocator_cache_spec.rs`，保持 exec 路径独立。删除透明 spec 的冗余 reveal 和四个不必要的 ledger 相等断言；序列前缀增长在消费集合插入等式的局部 proof 内证明。
5. 死代码：删除无调用者的私有 `PageMap::init_unpublished`、`page_map_set_kernel_entry_range`；删除只可能是 Acquire 或 Release 的枚举恒真前置条件。未按“没有仓库内调用”删除公共 syscall。
6. 测量工具：两个 timing 前端共用唯一日志目录，保留 stderr、Verus JSON、外部 wall time 和真实退出码；解析正确的 `times-ms` 字段，拒绝缺失、损坏、失败和无实际验证数据。新增带编号的 pipeline 入口。

格式整理仅覆盖本轮修改的函数与删除遗留的空白，第一轮整理检查了前后非空白字符一致，随后去掉调用参数的可选尾逗号和多余括号。没有将格式压缩算作 solver 加速。

## 未采用的更短写法

- 直接删除 PCID 的所有调用点量化证明、却不补 producer 的整体空序列保证：#11774 失败。最终使用 producer 已实际构造的 `Seq::new` 等式，不新增假设或专用 lemma。
- 将 new-container 的所有 remove 链合并为一个 union/remove_keys 等式：直接证明与过度压缩版本失败。最终保留四个命名中间量；不把未通过的表达式当作等价实现交付。
- 删除 allocator 的序列前缀增长步骤：#11791 的四个集合插入义务失败。最终使用 vstd 的序列相等工具，在该集合义务内完成证明；没有保留对透明 spec 的无效 reveal。
- 一次删除所有 held-context 调用点断言：#11794 起暴露出页表锁与跨边界 process 归属的真实义务。最终只保留对应的直接断言，具体失败与回补记录见运行日志。

## Monolith 闭合

首次全量 monolith 的 #11865 暴露两个 split workspace 已通过的义务；#11866–11867 的单独选择验证复现了失败。最终修复只保留：

- 进程树插入：在消费上界与唯一性事实的局部 proof 中，直接证明 parent 不在自己的 ancestor sequence 中。没有修改 tree invariant 或增加 precondition。试加的 Seq 前缀相等和 subrange 组合步骤删除后，#11870 仍通过。
- 2M global-pool pop：在 `thread_staged_pages_2m_wf` 的局部 proof 中展开已有 `thread_perms_wf`。#11871–11873 的删除实验确认 page-array reveal 和地址往返断言可删，thread-permission reveal 必须保留。

## 验证与性能

最终 workspace（#11875）九个 crate 全部实际重验，847 verified / 0 errors，外部 wall 48.38 秒；monolith（#11874）32 线程全量 848 verified / 0 errors，外部 wall 35.70 秒。测量工具 6 项测试通过，真实失败的 #11865 也经新 timing 前端正确返回非零。

A/B 比较采用交替 A/B，各三次，外部 wall time 的中位数；Cargo 默认并发、Verus 32 线程、vstd 与普通依赖热、全部九个 VeriFlat package 冷。以 5% 为已确认的简洁度／性能取舍阈值。

基线是本轮修改前的源码快照 `/tmp/veriflat-cleanup-baseline-11772`，保留相同的本地 Verus 修改。A/B 使用相同 `CARGO_TARGET_DIR` 和测量入口；源码根路径不同，日志记录了该差异。每个样本必须包含全部九个 crate 的实际全量验证，缓存 no-op 不计入结果。


## 规模与风格审计

- 定义数：1,531 → 1,499，净少 32 个（删除 27 个不同名字，另合并 5 份重复定义）；没有新增 spec/proof 名字。
- 整个 `src/**/*.rs` 按换行符统计：61,024 → 57,556，减少 3,468 行，包含格式压缩。非空白字符 2,297,072 → 2,317,821，增加约 0.90%；显式契约会重复展示字段保证，所以不能声称所有尺度的代码体积都变小。简化主要体现在删除定义、降低契约间接层数及移除已验证不必要的 proof。
- 新增 bare/empty assert、`assume`、`external_body` 均为 0；受影响文件中 `assert forall` 从 23 降至 21。保留 pre/post 独立的正向 trigger，没有修改公共 invariant 的 trigger。
- canonical `syscall_alloc_quota/` 三个文件字节一致。Verus 子模块原有四个修改文件保留，本轮没有修改该子模块。
- `git diff --check` 通过；格式审计覆盖本轮改动的文件。Rust source 和共享 API 在最终测量期间冻结。

## 复验入口

```bash
./verify-workspace.sh -- --output-json
./smt_times.sh -n 32
./module_times.sh -n 32
./verify-pipeline.sh --cold-veriflat -- --output-json
python3 -B tests/test_verification_tools.py
```

`--cold-veriflat` 仅清理九个 VeriFlat package；依赖是否已经热，需要结合实际编译日志确认。初次使用有依赖重建的运行不能充当 hot-dependency 样本。每次 timing 前端运行在 `.verus-log/timings.*` 保留 JSON、stderr 和外部 wall time，verifier 的非零退出码优先于解析结果。

## 实验索引

- 修改前源码基线 commit：`58d06b6c4348a75303e51e1c82c99689c39cb67e`，外加已有 Verus 子模块修改。先前单次审计 #11769–11772 的不同配置不混入本次 A/B 中位数。
- #11773–11798：分模块 typecheck、契约展开、直接 proof 与调用点窄断言实验。失败的中间版本已修正。
- #11799–11855：页转移 57 个闭合断言逐项删除，[完整结果](/tmp/veriflat-transfer-ablation/results.json)。
- #11856–11860：同一 producer 的五个透明 Kernel reveal 逐项删除，[结果](/tmp/veriflat-transfer-ablation/reveals.json)。
- #11861–11864：格式与全库闭合；#11864 九个 crate 实际重验，847 / 0，46.96 秒。随后 monolith 发现的两处问题继续修复，没有把这次 workspace 通过当作全部完成。
- #11865–11873：monolith 差异定位及删除验证，[2M 删除实验](/tmp/veriflat-monolith-2m-ablation.json)。
- #11874：[最终 monolith 报告](/tmp/veriflat-final-monolith-second-report.txt)，[原始 JSON](/home/xiangdc/VeriFlat/.verus-log/timings.4WZ1FIDA/verus.json)。
- #11875：[最终 workspace JSON](/tmp/veriflat-final-workspace-second.jsonlog)，[stderr](/tmp/veriflat-final-workspace-second.stderr)。
- A/B 的复现实验驱动保存在 [/tmp/veriflat_benchmark.py](/tmp/veriflat_benchmark.py)，每次运行都检查九个 crate 全量验证、成功状态与普通依赖无重建。


## A/B 最终结果

外部 wall time 中位数 **33.95 → 31.88 秒（-6.09%）**。整组清理没有超过已确认的 5% 退化阈值，保留此次简化。

| 顺序 | Run | 版本 | 外部 wall / s | 实际全量验证 |
| --- | --- | --- | ---: | --- |
| A1 | #11876 | 基线 | 33.951 | 871 / 0 |
| B1 | #11877 | 清理后 | 32.282 | 847 / 0 |
| A2 | #11878 | 基线 | 33.333 | 871 / 0 |
| B2 | #11879 | 清理后 | 31.454 | 847 / 0 |
| A3 | #11880 | 基线 | 34.059 | 871 / 0 |
| B3 | #11881 | 清理后 | 31.883 | 847 / 0 |

全部样本均为 Cargo 默认并发、Verus 32 线程、vstd 与普通依赖热、九个 VeriFlat artifact 冷；日志确认无普通依赖重建。外部 wall 包括 package 清理和验证入口开销。A/B 交替执行，期间源码 hash 未改变。此比较衡量整组改动，没有把收益归因于单个 helper 或调度属性。

基线范围 33.33–34.06 秒；清理后范围 31.45–32.28 秒。三次中位数衡量本机此次样本，不承诺其他机器的固定提升比例。

| 时间／资源指标（三次中位数） | 基线 | 清理后 |
| --- | ---: | ---: |
| 外部 wall / s | 33.951 | 31.883 |
| 各 crate 累计 Rust / s | 12.075 | 11.663 |
| 各 crate 累计 VIR / s | 19.173 | 18.941 |
| 各 crate 累计 verification / s | 107.409 | 92.856 |
| 各 crate 累计 SMT run / s | 324.020 | 293.255 |
| 各 crate 累计 rlimit run | 380,778,780.000 | 380,301,643.000 |

各 crate 的并发时间不能相加当作外部 wall；VIR 是 verification 的子项，不能重复相加。rlimit 仅作为资源诊断，没有用它代替 wall time 决策。

| Crate | 基线 Verus wall 中位数 / s | 清理后 / s |
| --- | ---: | ---: |
| `veriflat_alloc_page` | 14.952 | 12.896 |
| `veriflat_kernel_core` | 20.467 | 18.582 |
| `veriflat_map_4k` | 11.942 | 12.668 |
| `veriflat_syscall_alloc_quota` | 5.347 | 5.191 |
| `veriflat_syscall_ipc` | 13.623 | 12.085 |
| `veriflat_syscall_mmap_4k` | 9.287 | 7.577 |
| `veriflat_syscall_new_container` | 19.428 | 15.651 |
| `veriflat_syscall_new_process` | 19.777 | 16.965 |
| `veriflat_syscall_new_thread` | 6.337 | 5.843 |

原始结果与每个 crate 的完整 Rust、VIR、verification、SMT、wall、rlimit 均保留在以下 JSON：

- [A1 / #11876](/tmp/veriflat-final-benchmark/A1.summary.json)：[完整 Verus 输出](/tmp/veriflat-final-benchmark/A1.jsonlog)，[stderr](/tmp/veriflat-final-benchmark/A1.stderr)。
- [B1 / #11877](/tmp/veriflat-final-benchmark/B1.summary.json)：[完整 Verus 输出](/tmp/veriflat-final-benchmark/B1.jsonlog)，[stderr](/tmp/veriflat-final-benchmark/B1.stderr)。
- [A2 / #11878](/tmp/veriflat-final-benchmark/A2.summary.json)：[完整 Verus 输出](/tmp/veriflat-final-benchmark/A2.jsonlog)，[stderr](/tmp/veriflat-final-benchmark/A2.stderr)。
- [B2 / #11879](/tmp/veriflat-final-benchmark/B2.summary.json)：[完整 Verus 输出](/tmp/veriflat-final-benchmark/B2.jsonlog)，[stderr](/tmp/veriflat-final-benchmark/B2.stderr)。
- [A3 / #11880](/tmp/veriflat-final-benchmark/A3.summary.json)：[完整 Verus 输出](/tmp/veriflat-final-benchmark/A3.jsonlog)，[stderr](/tmp/veriflat-final-benchmark/A3.stderr)。
- [B3 / #11881](/tmp/veriflat-final-benchmark/B3.summary.json)：[完整 Verus 输出](/tmp/veriflat-final-benchmark/B3.jsonlog)，[stderr](/tmp/veriflat-final-benchmark/B3.stderr)。


## 第二轮：五项跟进优化（基线 #11881）

本节记录用户要求实施的五项后续优化，比较基线是上一轮清理完成后的源码快照 `/tmp/veriflat-followup-baseline-11881`。不将第一轮的计时样本混入第二轮，也不把本轮的微小中位数下降称为稳定提速。

### 五项实际改动

1. 两个 `publish_staged_process*` 移除 `source_range` 参数及范围相关前提，quota 前提分别收窄为实际消耗的 3／5，后置条件直接给出 `quota_after == quota_before - 3/5`。原有 source-range-present 证明移到三个实际共享调用之前。发布层直接给出持有的 source 页表值不变，以及新页表与原 source 页表相同的 kernel L4 边界；这些是已有操作的具体保证，没有新增 framing spec、桥接 lemma 或 invariant。
2. `share_one_mapping_4k` 已直接保证目标线程 lock id 不变，循环也保留了相同的不变量；删除调用之后重新依赖前后全局 `inv()` 的 `thread_lock_id_preserved_for_typed_maps_unchanged` 断言。构建页表阶段仍需要的另一处调用保留。
3. 移除审计找到的 17 个函数中 74 条不可变输入的重复 postcondition，包括固定指针有效性／不等、CPU 索引有效性、只读 LockPerm 状态和只读 LocalContext 的 ledger alignment。其中 3 条属于随后整体删除的 staging wrapper；代码规模统计不重复计算。
4. 删除 `stage_mmap_4k_page` 和 monolith／split crate 的 re-export，两个使用点改为直接调用 `allocate_free_4k_page`，保持原有 crate 依赖。删除两处大段 EOF context 断言；directory 路径保留 7 个针对实际义务的局部断言，leaf 路径保留 3 个。没有增加调用方前置条件、运行时检查或改变锁协议。
5. 4K／2M 的私有 `scan_caches_and_alloc` 从 `(bool, Option<(CpuId, PagePtr, Tracked<LockPerm>)>)` 简化为 `Option<(PagePtr, Tracked<LockPerm>)>`。两个唯一调用点直接匹配 Option，删除重复的成功标志、未使用的 CPU 返回值和对应约束。扫描顺序、失败不修改状态的保证、成功后的页面和权限保证保持。

### 验证与删除实验

- #11882：初次类型检查发现 Verus 不接受 `if let` 中嵌套解构 `Tracked`；改为匹配整个返回 tuple 后，#11883 类型检查通过。#11884 allocator 整包 24 / 0。
- #11885：发布链类型检查通过。#11886–11887 发现并最小化复现新页表 kernel L4 边界的调用前提；发布层改为直接给出与 source 的边界等式，#11888 new-process 整包 14 / 0。
- #11889：删除 staging wrapper 后类型检查通过。#11890–11893 的局部失败定位到 process/container 归属、稳定 Thread 字段、allocator-ready 和 PageTable wf；#11894–11895 两条路径分别 1 / 0，#11896 map_4k 整包 21 / 0。
- #11897–11913：12 个新局部断言逐个删除，另对多-reveal 断言做 5 次独立 reveal 删除；17 次均失败，已恢复必须保留的证明。每次只验证受影响函数并清理对应 partial package，避免把缓存命中当作删除成功。[完整删除实验](/tmp/veriflat-followup-ablation.json)。
- #11914：九个 package 全部清理 `target/verus-partial` 下的 VeriFlat 产物后，workspace 默认 Cargo jobs=2／Verus threads=16 全量验证 **846 / 0**；外部 wall **45.086 秒**。[报告](/tmp/veriflat-followup-runs/final_workspace.json)。
- #11915：32 线程 monolith 全量验证 **847 / 0**；外部 wall **36.042 秒**，Verus wall 35.184 秒、Rust 5.943 秒、VIR 5.387 秒、verification 28.101 秒、SMT run 347.096 秒、rlimit 375,481,882。[报告](/tmp/veriflat-followup-runs/final_monolith.json)。
- 本轮未修改测量工具，沿用第一轮已通过测试的入口。没有新增 warning／recommendation；日志中的 Z3 `if cannot be used in patterns` 是原有警告。

### 第二轮 A/B

Cargo 默认并发、Verus 32 线程，vstd／普通依赖热，九个 VeriFlat package 冷；交替 A/B 各三次。使用相同 `CARGO_TARGET_DIR`，每个样本均确认九个 crate 实际全量验证成功、无普通依赖重建。源码根目录不同，基线快照通过 symlink 使用同一份本地 Verus。外部 wall 包含 VeriFlat package 清理和验证入口开销。

| 样本 | Run | 版本 | 外部 wall / s | Verified / errors |
| --- | --- | --- | ---: | --- |
| [A1](/tmp/veriflat-followup-benchmark/A1.summary.json) | #11916 | 上一轮完成版 | 30.315 | 847 / 0 |
| [B1](/tmp/veriflat-followup-benchmark/B1.summary.json) | #11917 | 五项优化后 | 34.292 | 846 / 0 |
| [A2](/tmp/veriflat-followup-benchmark/A2.summary.json) | #11918 | 上一轮完成版 | 35.674 | 847 / 0 |
| [B2](/tmp/veriflat-followup-benchmark/B2.summary.json) | #11919 | 五项优化后 | 35.635 | 846 / 0 |
| [A3](/tmp/veriflat-followup-benchmark/A3.summary.json) | #11920 | 上一轮完成版 | 36.027 | 847 / 0 |
| [B3](/tmp/veriflat-followup-benchmark/B3.summary.json) | #11921 | 五项优化后 | 35.038 | 846 / 0 |

外部 wall 中位数 **35.674 → 35.038 秒（-1.78%）**。基线范围 **30.315–36.027 秒**，优化后 **34.292–35.635 秒**；范围重叠且基线波动明显，**尚未证实稳定提速**。首对样本曾表现为变慢，后两对持平或略快，因此保留全部样本，不挑选最好的一次。当前收益主要是代码和契约简洁度。

| 三次中位数 | 基线 | 优化后 |
| --- | ---: | ---: |
| 各 crate 累计 Rust / s | 14.339 | 14.299 |
| 各 crate 累计 VIR / s | 25.033 | 24.190 |
| 各 crate 累计 verification / s | 112.788 | 109.134 |
| 各 crate 累计 SMT run / s | 351.431 | 348.712 |
| 各 crate 累计 rlimit | 380,301,643.000 | 379,475,726.000 |

各 crate 阶段时间有并发重叠，不能相加当作外部 wall；VIR 包含在 verification 内。rlimit 只记录资源使用，没有作为 wall 加速的证据。

| Crate Verus wall 中位数 / s | 基线 | 优化后 |
| --- | ---: | ---: |
| `veriflat_alloc_page` | 16.989 | 16.297 |
| `veriflat_kernel_core` | 21.846 | 21.306 |
| `veriflat_map_4k` | 15.696 | 16.847 |
| `veriflat_syscall_alloc_quota` | 6.313 | 6.453 |
| `veriflat_syscall_ipc` | 14.029 | 13.711 |
| `veriflat_syscall_mmap_4k` | 9.637 | 9.226 |
| `veriflat_syscall_new_container` | 17.787 | 17.896 |
| `veriflat_syscall_new_process` | 18.783 | 18.699 |
| `veriflat_syscall_new_thread` | 8.127 | 7.645 |

`map_4k` 的 crate wall 中位数仍从 15.696 升到 16.847 秒（约 +7.3%），这次没有解决该局部性能问题。总 pipeline 中位数没有超过第一轮已采用的 5% 退化阈值；保留已验证的五项简化，但不声称各 crate 都变快。完整阶段与函数数据保存在 [对比结果](/tmp/veriflat-followup-benchmark/comparison.json) 和同目录 A1/B1/A2/B2/A3/B3 的 `.summary.json`、`.jsonlog`、`.stderr` 中。

### 第二轮规模与风格

- Rust 文件 233 → 232，函数定义 1,499 → 1,498。
- 按换行符计 57,556 → 57,254 行，**净减 302 行**；非空白字符 2,317,821 → 2,301,142，**净减 16,679 字符（约 0.72%）**。未通过格式压缩制造行数收益。
- 没有新增 spec/proof 定义、bare/empty assert、`assert forall`、`assume`、`external_body` 或 ghost snapshot；保留既有 invariant／trigger／TCB。新增断言都只展开消费目标所需的不变量。
- canonical `syscall_alloc_quota/` 三文件字节一致，Verus 子模块原有四个修改文件保留。本轮 232 份 Rust source hash 在全量验证与六次 A/B 期间完全一致。
- `git diff --check` 及本轮改动风格审计通过。所有日志与脚本均在 `/tmp/veriflat-followup-*`，仓库原有脏改动保留。

## 第三轮：四项候选实验（基线 #11921）

用户授权四项都试验后汇报。基线为上一轮最终源码快照 `/tmp/veriflat-round3-baseline-11921`，保留之前所有清理和原有 Verus 修改。本轮只保留通过验证且有明确简洁度收益的改动；未找到更简洁实现的 lock-id 方案及变慢的调度方案均撤回。

### 保留的改动

- `mmap_4k_build_one_structure` 删除仅用于契约的 `quota_reserve` 参数。前提直接要求至少 3 页额度，后置条件保留实际消耗在 0–3 页之间；mmap 和共享映射的两个调用者不再计算并传入剩余额度。两条链均无需新增局部证明就能推导后续额度，公共 syscall 的 quota 预检不变。
- 两个页表构建／安装函数已经保证 `user_view()` 相等，删除其包含的三种 mapping 的重复相等保证，共 6 条。删除由原有 LocalContext 线程号等式和只读 LockPerm 前提覆盖的 14 条线程号后置条件；最后一个共享函数的四条权限线程号条件改为一条 LocalContext 线程号等式。另删除 `!being_killed()` 与 `being_killed() == false` 的三个重复条件，以及 `lctx`／`&*lctx` 形式重复的一条 alignment invariant。这组契约净减 27 行。
- 私有 `install_staged_4k_page_table_page` 只有 directory 安装函数一个调用者。删除调用者不需要的 15 条 Page／Thread／页表内部细节保证，以及两段其他 Thread／PageTable 对象不变的量化后置条件，共 27 行；保留现有 `unchanged_except`、持锁对象关系、kernel invariant、锁协议和用户视图保证。调用者原有完整契约仍通过验证。

### 未保留的实验

- **lock-id 直接后置条件**：#11926 仅在 builder 暴露目标线程 lock-id 等式并删除上层桥接断言，builder 无法闭合。#11927–11928 尝试从 Thread permission invariant 和现有 LockId 字段相等引理直接证明，仍失败。#11929–11930 尝试向 allocator／directory 层暴露该保证，并展开已有 `stable_allocation_root_equal`，allocator 仍失败；该关系不包含全部动态 lock-id 所需字段。现有权限 token 匹配本身不足以在这些实验中证明由对象元数据计算的完整 lock id 相等。没有据此修改模型、增加前提或新增 framing／专用引理；全部试验修改已撤回，原有调用点证明保留。这说明这些具体短写法不通过，不表示该事实不能用其他方法证明。
- **移除热点函数 `spinoff_prover`**：只对 `share_mapping_4k_build_and_share` 的既有属性做成对实验，其他代码相同。Cargo jobs=1／Verus threads=32，依赖热、map package 每次冷，整包均 21 / 0。A 保留属性，B 移除属性：#11934–11939 分别为 A1 5.278、B1 5.692、A2 5.366、B2 5.719、A3 5.634、B3 5.719 秒。外部 wall 中位数 **5.366 → 5.719（+6.57%）**，Verus wall 中位数 **4.726 → 5.119（+8.32%）**，因此恢复原属性。此结论限于该单包实验，不用 rlimit 代替 wall 做调度决策。[完整记录](/tmp/veriflat-round3-scheduling.json)。

### 验证记录

- #11922：修改前 map 整包 `--time-expanded`，21 / 0，外部 wall 6.093 秒；最慢函数合计 SMT 约 2.599 秒，没有据此认定存在超过 5 秒的单个 equation。
- #11923：quota 参数删除后的类型检查通过，实际 proof 数为 0。#11924–11925：map 21 / 0、mmap 9 / 0，确认两个调用者无需补证明。
- #11926–11930：五次 lock-id 失败实验，具体错误保存在同名 JSON／stdout／stderr，均已撤回。
- #11931–11932：第一组长契约清理后 map 21 / 0、mmap 9 / 0。#11933：私有安装函数契约进一步收窄后 map 21 / 0。
- #11934–11939：上述六次调度实验，全部实际整包验证成功。
- #11940：九个 VeriFlat partial package 全冷，workspace 默认 Cargo jobs=2／Verus threads=16 全量 **846 / 0**，外部 wall **48.880 秒**。[完整报告](/tmp/veriflat-round3-runs/final_workspace.json)。
- #11941：32 线程 monolith 全量 **847 / 0**，外部 wall **37.742 秒**；Verus wall 36.938 秒、Rust 6.546 秒、VIR 5.130 秒、verification 29.236 秒、SMT run 379.282 秒、rlimit 376,625,603。[完整报告](/tmp/veriflat-round3-runs/final_monolith.json)。

本轮修改 5 个 Rust 文件，57,254 → 57,198 行，**净减 56 行**；非空白字符 2,301,142 → 2,296,017，**净减 5,125**。没有新增 assert、reveal、ghost、spec/proof 定义、assume 或 external_body；无需保留或最小化新增 proof scaffolding。没有修改公共 invariant／trigger／TCB、canonical quota syscall、Verus 子模块或仓库原有其他脏改动。源码在最终验证和性能测量期间冻结。

### 第三轮 pipeline A/B

Cargo 默认并发／Verus 32 线程，vstd 和普通依赖热，九个 VeriFlat package 每次冷；同一 `CARGO_TARGET_DIR`，基线与当前源码根路径不同。次序 A1、B1、B2、A2、A3、B3，第二对反转顺序。六次均确认九个 crate 实际全量验证、846 / 0、无普通依赖重建。每次使用相同的约一秒一次资源采样，采样文件与原始报告同目录。外部 wall 包括 package 清理和验证入口。

| 顺序 | Run | 版本 | 外部 wall / s |
| --- | --- | --- | ---: |
| A1 | #11942 | 基线 | 32.710 |
| B1 | #11943 | 本轮清理后 | 35.162 |
| B2 | #11944 | 本轮清理后 | 34.464 |
| A2 | #11945 | 基线 | 34.430 |
| A3 | #11946 | 基线 | 34.554 |
| B3 | #11947 | 本轮清理后 | 34.354 |

外部 wall 中位数 **34.430 → 34.464 秒（+0.10%）**。基线范围 32.710–34.554 秒，清理后 34.354–35.162 秒；第二对几乎持平，第三对清理后略快，首对较慢。差异不足以证实稳定的提速或退化；保留确定的契约简洁度收益，不声称 wall 优化成功。

| 各 crate 累计阶段（三次中位数） | 基线 | 本轮清理后 |
| --- | ---: | ---: |
| Rust / s | 13.620 | 14.532 |
| VIR / s | 23.258 | 24.116 |
| verification / s | 109.070 | 112.263 |
| SMT run / s | 346.624 | 362.757 |
| rlimit | 379,475,726.000 | 379,069,452.000 |

并发阶段不能相加当作外部 wall；VIR 是 verification 的子项。rlimit 仅用于诊断，未作为速度结论。

| Crate Verus wall 中位数 / s | 基线 | 本轮清理后 |
| --- | ---: | ---: |
| `veriflat_alloc_page` | 15.860 | 17.265 |
| `veriflat_kernel_core` | 21.483 | 22.250 |
| `veriflat_map_4k` | 15.767 | 15.670 |
| `veriflat_syscall_alloc_quota` | 6.883 | 6.547 |
| `veriflat_syscall_ipc` | 13.990 | 14.081 |
| `veriflat_syscall_mmap_4k` | 9.160 | 9.588 |
| `veriflat_syscall_new_container` | 17.323 | 17.718 |
| `veriflat_syscall_new_process` | 18.341 | 18.262 |
| `veriflat_syscall_new_thread` | 7.894 | 8.343 |

`map_4k` 中位数 **15.767 → 15.670 秒（-0.62%）**，也没有稳定改善的证据。当前单包 profile、移除 spinoff 的反例和 pipeline A/B 都不足以唯一归因上一轮的 +7.3%；没有把这项局部性能问题写成已解决。

资源采样中，32 个逻辑 CPU 的平均忙碌比例约 48.1%–52.1%，Z3 进程峰值 31–37（包括可能等待的进程，不能等同于同时占用 CPU 的数量），可见的 cgroup throttling 计数均未增长。采样确认并发执行背景，但没有证明慢样本由 CPU 限流、频率或某个具体调度行为造成；也不能替代未采集的上一轮历史数据。

[完整对比与阶段／资源数据](/tmp/veriflat-round3-benchmark/comparison.json)。同目录 A1/B1/B2/A2/A3/B3 的 `.summary.json`、`.jsonlog`、`.stderr`、`.telemetry.json` 保留每个样本；驱动为 `/tmp/veriflat_round3_benchmark.py`。本轮所有 focused／全量验证结果在 `/tmp/veriflat-round3-runs/`，#11922–11947 均在本节说明。最终 `git diff --check`、改动范围风格审计、232 份 Rust 源码 hash 核对通过。

## 第四轮：跨 syscall 调用链清理（基线 #11947）

用户授权尝试六组只读审计候选。开始前把完整当前源码冻结到 `/tmp/veriflat-round4-baseline-11947`，保留前三轮清理和原有 dirty worktree。本轮变化相对该快照计算。

### 保留的改动

- **4K / 2M allocator**：两个批量加锁 helper 各删 `thread_ptr`；两个批量解锁 helper 各删 `thread_ptr` / `page_index`。共 6 个形参及 18 条 pre/post/loop membership 条件。已有完整 thread/page typed lock map 等式足以让调用者继续证明成员关系，没有新增证明。
- **attach endpoint**：共享原语删 CPU、scheduler、process、page 四个上下文参数及 8 条关联条件；new-thread-with-endpoint、new-process-with-endpoint、IOMMU+endpoint 三个调用点同步收窄。完整对象 map 不变保证继续支撑后续解锁。
- **IPC Pages**：`ipc_share_pages_locked` 删 `source_process` 及 5 份只用于契约的收尾权限引用，保留真正传给映射操作的 source/target 权限。删除枚举全部变体的恒真后置条件。进一步删除调用者不需要的 5 条完整 computed lock-id 等式及为它们服务的 8 次 bridge 引理调用；实际 held-object、typed map、token 匹配、用户视图和错误语义保证保留。整包 25 / 0，无新增证明。
- **IPC Endpoint**：`ipc_begin_endpoint_transfer` 删 CPU、process、current-thread 三份只用于契约的权限引用和对应 12 条条件。已有完整对象相等保证足以支撑调用者。实际用于状态迁移的 peer 权限保留。
- **new-container**：`publish_new_container_base` 删三份只用于契约的权限引用；把三条 token lock-id 匹配后置条件改为 CPU、父 process、源 pagetable 的 `locking_thread()` 前后相等，直接暴露原操作的窄保证。下游 `finish_staged_container_publish` 删除完整 domain 等式已包含的 10 条成员前提。历史动态锁状态快照保留。
- **mmap**：私有 `map_owned_4k_page` 固定唯一调用点已有的 `write: true` / `execute_disable: false`，删两个形参；底层页表原语继续支持通用权限。

本轮修改 **11 个 Rust 文件，净减 120 行、8,547 个非空白字符，9 个函数共减少 24 个形参**。源码公共 syscall 入口文件全部与本轮基线一致；没有新增 assert、reveal、ghost、proof/spec helper、framing spec、trigger、TCB 或运行时检查。三条直接后置条件替换的是既有操作保证。所有添加行的 proof/style 审计及 `git diff --check` 通过。

### 未保留的尝试与契约诊断

- **线程创建的 `endpoint_index`**：删参后 #11954 在 allocator 调用后的 endpoint/container 归属兼容性断言失败。此索引用于从仍持锁的 current thread 的 descriptor 关系重新建立跨 kernel-step boundary 后的兼容性，不能只凭函数体未读就认定冗余。已恢复参数、原前提和调用；#11970 整包 4 / 0。attach 的四参数删减保留。
- **container 直接删除权限引用**：#11958 和聚焦 #11959 暴露下一个 helper 缺 CPU token 匹配事实。随后将已有 token 匹配保证改成对应对象自身的锁状态相等；#11960 整包 29 / 0，没有新断言、桥接函数或放宽模型。
- **IPC 只删 bridge**：#11961 删除 CPU 引理调用通过；#11962–11968 的失败指向 helper 自己承诺的 computed lock-id 等式。#11966 / #11967 的脚本命中了前一个同名调用，实际重复 #11962 / #11965，不作为尾部调用的独立证据。最终一并收窄下游不消费的五条保证，八次 bridge 调用全部删除，#11969 整包 25 / 0。

### 开发及完整验证记录

开发命令从 `./verify-workspace.sh --package PACKAGE` 开始；受测 partial package 每次冷清理，普通依赖缓存保留。`--no-verify` 是类型检查，0 个 proof；选函数结果不冒充全包。所有原始 stdout/stderr、JSON 和完整参数存于 `/tmp/veriflat-round4-runs/`。

| Run | 实验 | 结果 verified / errors | 外部 wall / s | SMT run 合计 / s | rlimit 合计 |
| --- | --- | ---: | ---: | ---: | ---: |
| #11948 | `shared_typecheck` | 0 / 0 | 15.999 | 0.000 | 0 |
| #11949 | `attach_proof` | 1 / 0 | 10.591 | 0.543 | 1,606,960 |
| #11950 | `allocator_proof` | 24 / 0 | 7.024 | 24.753 | 55,407,974 |
| #11951 | `ipc_typecheck` | 0 / 0 | 4.807 | 0.000 | 0 |
| #11952 | `ipc_proof` | 25 / 0 | 6.065 | 13.554 | 31,002,619 |
| #11953 | `thread_typecheck` | 0 / 0 | 1.609 | 0.000 | 0 |
| #11954 | `thread_proof` | 3 / 1 | 2.953 | 3.130 | 8,824,525 |
| #11955 | `mmap_typecheck` | 0 / 0 | 1.723 | 0.000 | 0 |
| #11956 | `mmap_proof` | 9 / 0 | 3.414 | 3.080 | 9,903,265 |
| #11957 | `container_typecheck` | 0 / 0 | 2.765 | 0.000 | 0 |
| #11958 | `container_proof` | 28 / 1 | 8.425 | 17.855 | 65,028,831 |
| #11959 | `container_missing_contract` | 3 / 1 | 5.406 | 2.309 | 11,949,248 |
| #11960 | `container_direct_contract` | 29 / 0 | 8.295 | 15.516 | 59,290,139 |
| #11961 | `ipc_ablate_1` | 2 / 0 | 3.673 | 1.009 | 2,955,802 |
| #11962 | `ipc_ablate_2` | 1 / 1 | 4.155 | 1.809 | 2,910,775 |
| #11963 | `ipc_ablate_3` | 1 / 1 | 4.176 | 1.870 | 3,623,810 |
| #11964 | `ipc_ablate_4` | 1 / 1 | 4.633 | 1.896 | 2,959,311 |
| #11965 | `ipc_ablate_5` | 1 / 1 | 4.305 | 1.750 | 2,917,195 |
| #11966 | `ipc_ablate_6` | 1 / 1 | 4.207 | 1.843 | 2,910,775 |
| #11967 | `ipc_ablate_7` | 1 / 1 | 3.877 | 1.859 | 2,917,195 |
| #11968 | `ipc_ablate_8` | 1 / 1 | 4.711 | 2.081 | 3,098,776 |
| #11969 | `ipc_narrow_contract` | 25 / 0 | 5.183 | 12.293 | 30,450,753 |
| #11970 | `thread_restored_index` | 4 / 0 | 2.411 | 2.424 | 7,542,607 |
| #11971 | `process_callers` | 14 / 0 | 9.819 | 34.961 | 75,706,513 |
| #11972 | `final_workspace` | 846 / 0 | 45.417 | 166.783 | 377,883,750 |
| #11973 | `final_monolith` | 847 / 0 | 38.401 | 372.515 | 376,551,809 |

最终 workspace #11972 为九包实际全量验证（846 / 0，Cargo jobs=2 / Verus threads=16）；monolith #11973 为 32 线程全量（847 / 0）。二者测量范围不同，不用其 wall 互相比速度。源码在这两次验证及后续 pipeline 测量期间冻结，232 份 Rust 文件 hash 保存在 `/tmp/veriflat-round4-final-hashes.json`。

### Pipeline A/B

Cargo 默认并发，Verus 32 线程，`VERUS_PIPELINE_SMT=1`。vstd 和普通依赖热，9 个 VeriFlat package 每次冷；baseline/current 共用同一 `CARGO_TARGET_DIR`，源码根目录不同。每次使用相同的一秒资源采样。次序 A1、B1、B2、A2、A3、B3，第二对反转顺序。外部 wall 包含清理和验证入口。六次全部确认九个 crate 实际全量验证、846 / 0、无普通依赖重建。

| Run | 样本 | 外部 wall / s |
| --- | --- | ---: |
| #11974 | A1 | 33.078 |
| #11975 | B1 | 35.496 |
| #11976 | B2 | 35.641 |
| #11977 | A2 | 35.771 |
| #11978 | A3 | 35.559 |
| #11979 | B3 | 35.358 |

外部 wall 中位数 **35.559 → 35.496 秒（-0.18%）**；A 范围 33.078–35.771，B 范围 35.358–35.641。**整体基本持平，没有稳定提速证据。保留理由是代码和证明依赖更简洁。**

| 各 crate 阶段合计的中位数 | 基线 A | 清理后 B |
| --- | ---: | ---: |
| Rust / s | 13.949 | 14.720 |
| VIR / s | 22.278 | 24.878 |
| verification / s | 112.084 | 113.496 |
| SMT run / s | 353.069 | 358.428 |
| rlimit | 379,069,452 | 377,883,750 |

并发阶段合计不能相加当作 pipeline wall；VIR 已包含在 verification 内。SMT run 是累计 solver 时间，不是 syscall 执行时间；rlimit 不作为加速证据。

| Crate Verus wall 中位数 / s | 基线 A | 清理后 B | 变化 |
| --- | ---: | ---: | ---: |
| `veriflat_alloc_page` | 16.786 | 17.941 | +6.88% |
| `veriflat_kernel_core` | 21.922 | 23.021 | +5.01% |
| `veriflat_map_4k` | 16.013 | 15.646 | -2.29% |
| `veriflat_syscall_alloc_quota` | 7.057 | 6.434 | -8.83% |
| `veriflat_syscall_ipc` | 13.897 | 13.858 | -0.28% |
| `veriflat_syscall_mmap_4k` | 9.923 | 9.887 | -0.36% |
| `veriflat_syscall_new_container` | 17.533 | 17.686 | +0.87% |
| `veriflat_syscall_new_process` | 18.559 | 18.734 | +0.94% |
| `veriflat_syscall_new_thread` | 7.479 | 8.496 | +13.60% |

局部不能都写成改善：allocator 16.786 → 17.941 秒（+6.88%），new-thread 7.479 → 8.496 秒（+13.60%），kernel-core 21.922 → 23.021 秒（+5.01%）；这是并发 pipeline 内观测，未用孤立单包 A/B 建立因果。IPC 13.897 → 13.858 秒（−0.28%）也不足以单独证明加速。完整 pipeline 中位数基本不变。

资源采样：平均 CPU 忙碌比例 48.6%–51.3%，Z3 进程峰值 31–37；这描述并发背景，不作为波动原因的证明。

[完整阶段、每 crate 和资源数据](/tmp/veriflat-round4-benchmark/comparison.json)。同目录各 `.summary.json` / `.jsonlog` / `.stderr` / `.telemetry.json` 保留原始样本。本轮独立 diff 为 `/tmp/veriflat-round4-changes.patch`；统计与风格审计分别为 `/tmp/veriflat-round4-change-stats.json`、`/tmp/veriflat-round4-parameter-stats.json`、`/tmp/veriflat-round4-style-audit.json`。#11948–11979 的每次验证已记录。

## Round 5: 调用链职责与历史状态清理（2026-09-07）

基线是本轮开始时的完整脏树，保存在 `/tmp/veriflat-round5/baseline`，未以 Git HEAD 覆盖前几轮工作。最终源码冻结在 `/tmp/veriflat-round5/candidate-domain`。本轮修改 8 个 Rust 文件，净删 517 行、21,406 个非空白字符。

### 保留的结构变化

- `finish_staged_container_publish` 删除历史 `LocalContext` 和 funding 页序列两个 ghost 参数；requires 不再描述上层加尾页锁之前的状态。ensures 直接说明从自身入口到出口的锁集合变化，保留返回权限和实际对象的匹配、kernel invariant 与用户视图保证。删除发布层为旧契约准备的 submap/反向 map 等式，以及 `lctx_before_tail_locks` 快照。该文件净删 404 行。
- 共享映射的 ownership 条件直接以目标 container 为参数；出资线程在构建与安装目录页的调用链中明确命名为 `quota_thread` / `quota_thread_ptr`。原有 `container_thread_wf` 保证线程的 ancestor 序列等于所属 container 的 ancestor 序列，因此现有调用前提下 ownership 语义保持一致。目标对象稳定性的两种合法锁路径保留。跨 kernel-step 的 5 次新增 scoped reveal 已逐个删除验证，均失败后保留。
- 删除 `share_pages_and_lock_scheduler`，三个创建进程分支直接执行共享映射和 scheduler 加锁。步骤关系在调用点直接证明；没有新增 helper。逐个删除后去掉 9 处展开后冗余断言、3 次 `LockedMap::typed_lock_map_aligned` reveal。两个 process helper 文件合计净删 110 行。

公开 syscall 入口、运行时锁操作与状态修改顺序、公共 invariant/trigger、TCB 均未改；没有新增 framing spec、wrapper、assume、assert forall 或 proof-only snapshot。未做 syscall 运行时基准。

### 验证与删除实验

| Run | 作用和结果 |
| --- | --- |
| #12005–12008 | container 类型检查；局部契约 29/0；删除 remainder 补充断言 29/0；删除历史 submap 证明与快照 29/0 |
| #12009–12012 | mapping 改名的 struct shorthand 类型错误修正；ownership 改用 container 暴露 3 个函数中的证明失败；补齐 5 个必要 scoped reveal 后 21/0 |
| #12013–12015 | process 类型检查；展开后缺少三处步骤关系证明，10/3；直接证明现有步骤后 13/0 |
| #12016–12020 | 逐个删除 5 个 mapping reveal，均失败并恢复 |
| #12021–12040 | 普通/endpoint 两个 process caller 的 20 次逐条删除，保留 6 次成功删除；每次实际整包验证 |
| #12041–12050 | IOMMU caller 的 10 次逐条删除，保留 3 次成功删除；每次聚焦该函数且 verified > 0 |
| #12051 | 删除 container 发布层反向 map 衔接证明，29/0 |
| #12052–12057 | 三处步骤断言内逐个删除两个 reveal；保留 3 次成功删除，必要的 process_pagetable_match 保留 |
| #12058 | workspace 增量类型检查，3 个受影响 crate 实际检查，其余缓存；无证明测量 |
| #12059 | workspace，9 个 VeriFlat crate 全冷，普通依赖热，Cargo 2 / Verus 16：845/0，45.731 s |
| #12060–12091 | 四个 crate 各 2 次类型预热、6 次真实整包 A/B 测量；初版 container 有回退 |
| #12092–12093 | container 先将 page map 保证缩到 domain，再将其余非 allocator map 保证缩到 domain，均 29/0；最终不再传递不需要的 map 值等式 |
| #12094–12101 | 最终 container 的 2 次类型预热和 6 次真实整包 A/B 测量 |
| #12102–12103 | pipeline 类型预热，9 个 crate，verified 0，不计入性能样本 |
| #12104–12109 | pipeline 三对交替 A/B；A 全部 846/0，B 全部 845/0，普通依赖无重建 |
| #12110 | 最终 32 线程 monolith：846/0，35.638 s |

计数减少 1 来自删除一个已验证 helper。原始命令、stdout、stderr、JSON、删除试验清单均在 `/tmp/veriflat-round5/`；本轮所有 run 汇总见 `all-runs.json`。

### 相同条件下的性能

单包：Cargo 1 / Verus 32，pipeline 关闭，每次只清冷目标 package，依赖热；独立 A/B cache，每组顺序 A1、B1、B2、A2、A3、B3。类型预热不计入样本，所有测量均确认真实整包验证且依赖没有重建。下表为外部验证 wall，不是 syscall 执行时间。

| Crate | A 中位数 / s | B 中位数 / s | 变化 |
| --- | ---: | ---: | ---: |
| `veriflat_map_4k` | 5.519 | 5.420 | -1.79% |
| `veriflat_syscall_new_container` | 7.950 | 8.447 | +6.26% |
| `veriflat_syscall_new_process` | 10.469 | 10.832 | +3.46% |
| `veriflat_syscall_ipc` | 6.056 | 5.976 | -1.33% |

初版 container 传递完整 typed map 等式，单包中位数 8.638 → 10.177 s（+17.82%）。最终改成直接的 domain 保证后，另一组三对 A/B 为 7.950 → 8.447 s（+6.26%）。两组基线时段不同，不用两个 B 的绝对差值宣称提速。最终版本仍有局部回退。

| 单包阶段中位数（A → B） | Rust / s | VIR / s | verification / s | SMT / s | rlimit |
| --- | ---: | ---: | ---: | ---: | ---: |
| `veriflat_map_4k` | 0.417 → 0.423 | 0.846 → 0.840 | 4.536 → 4.364 | 10.996 → 9.701 | 28,231,935 → 28,579,375 |
| `veriflat_syscall_new_container` | 0.528 → 0.516 | 0.992 → 0.986 | 6.776 → 7.278 | 15.561 → 14.472 | 59,290,139 → 57,501,309 |
| `veriflat_syscall_new_process` | 0.530 → 0.525 | 1.011 → 1.031 | 9.181 → 9.640 | 40.109 → 49.628 | 75,706,513 → 94,498,528 |
| `veriflat_syscall_ipc` | 0.441 → 0.437 | 0.985 → 0.915 | 4.843 → 4.847 | 14.905 → 15.323 | 30,450,753 → 30,300,700 |

完整 pipeline：Cargo 默认并发 / Verus 32，9 个 VeriFlat crate 每次全冷，vstd/普通依赖热，使用同一 target cache。外部 wall 包含清理和验证入口，中位数 **36.854 → 37.274 s（+1.14%）**。三对样本不足以建立整体提速；这轮主要收益是职责和证明边界更直接、代码更少。

| Pipeline 阶段累计中位数 | A | B |
| --- | ---: | ---: |
| Rust / s | 15.263 | 16.233 |
| VIR / s | 25.731 | 26.722 |
| verification / s | 121.013 | 126.963 |
| SMT / s | 376.187 | 397.915 |
| rlimit | 377,883,750.000 | 395,084,322.000 |

阶段累计值不能相加当作 wall，VIR 包含在 verification 内。new-process 的整包 rlimit 约增加 24.8%，说明去掉共享 helper 会增加求解工作；wall 的变化较小，不代表证明成本下降。保留该改动的理由是减少中间契约和调用者历史依赖，而非速度优势。

[完整样本和阶段数据](/tmp/veriflat-round5/comparison.json) · [本轮独立 diff](/tmp/veriflat-round5/changes.patch) · [精确变更统计](/tmp/veriflat-round5/change-stats.json) · [风格审计](/tmp/veriflat-round5/style-audit.json)。最终源码与冻结样本一致，`git diff --check` 通过。
