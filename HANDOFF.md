# Handoff — 锁序 K-state 化（2026-10-24）

## 现状
- `main` = a061d7a 的 `src` + 两个提交：
  - `d5d041f`：回退 lctx 两提交（ff62781、c5449cc），`src` 回到 a061d7a 原样。
  - 本提交：K-state 锁序清理（下述内容）。

## 方向
- locker 公共 `requires` 只写 K 状态（对象状态、哪些锁图持有/为空）；锁序（`lock_id_acyclic`、存储 id 的 major）在 locker 内部推出，不向调用者索取。
- lctx 方向已放弃：实测 lctx 优化后 rlimit 1,084.6M vs K-state 1,098.7M（K-state +1.3%），wall 在噪声内；
  但 lctx 需要调用方 98 处点引理过桥、20 个 locker 契约带存储 id 界。

## 内容
- 页锁序：`Page::orders_below_table_locks` / `orders_below_allocator_locks` 用于全部 29 个页序 locker 及 `held_locks_order_below`。
- iommu_root_table / cpu_offline_flag / cpu / endpoint locker 只要 K 状态，去掉 ledger/acyclic requires。
- 线程 locker = 私有 core + 六个情形 wrapper，调用点：
  - current_running：系统调用入口锁自己线程；
  - scheduled：schedule next / rebalance pull；
  - endpoint_waiting_peer：ipc rendezvous peer；
  - reply_waiting_caller：ipc reply 与 thread_exit 的 caller；
  - kill_victim：kill walk；
  - killed_chain_caller：reclaim chain。
- 删 9 条死数值页 major ensures（create_process 8 条 + allocate_free_4k_pages 1 条）。
- 去掉 3 处 exec 内 `held_lock_majors_lt` 对齐 reveal；EOF 内 reveal 收进 assert 作用域。
- `install_one_mmap_4k_directory_page` 加 pre-side window trigger，修 `map_one_mmap_4k_page` 的单体不稳定。

## 验证
- 与本提交源树相同的树：
  - #34265 workspace：增量，8 个改动 crate 重检 862 verified / 0 errors，其余命中缓存。
  - #34266 单体（`--num-threads 32 --time-expanded`）：3096 verified / 0 errors；rlimit-run 1,098,681,137，
    smt-run 527,756 ms，total 64,397 ms；>3 s 6 个，>5 s 1 个（`share_mapping_4k_build_and_share` 5.4 s），>10 s 0。
  - #34267 NI：1 + 233 verified / 0 errors。
- 本提交源树 gate：
  - #34333 单体（`--num-threads 32 --time`）：3096 verified / 0 errors；rlimit-run 1,098,681,137（与 #34266 一致）；
    smt-run 584,938 ms，total 71,090 ms（期间机器上另有一个重验证任务并发）。
  - #34334 NI：1 + 233 verified / 0 errors。

| 树 | rlimit-run | smt-run ms | total ms |
|---|---|---|---|
| 本提交 #34266 | 1,098,681,137 | 527,756 | 64,397 |
| 上一轮 #34239 | 1,102,443,188 | 531,152 | 63,767 |
| 数值 K #34202 | 1,096,600,523 | 522,260 | 62,971 |
| a061d7a | 1,102,989,363 | – | – |
| lctx 优化后（已弃）#34312 | 1,084,608,136 | 519,505 | 63,751 |

## 环境
- `verus` 子模块：本克隆从旁边本地 clone 检出，`verus/source/target-verus` 软链到该 clone。
- 用 `ulimit -v 31457280` 代替 `systemd-run`。
- `--verify-function` 每次只给一个。
- boot check 缺 nasm。

## 剩余项
- 保留的数值事实及原因：wlock_page 页对页顺序；2M tail merged 顺序；FREE/MAPPED 类别事实；share_mapping `< MAPPED` ×3 喂 wlock_page。
- `wlock_scheduler_shard` 的 `|| being_killed()` 保留。
- 需批准的系统性成本：lock-map 空集子句引发的 `lemma_set_is_empty_len0` + `axiom_set_ext_equal`；
  `kill_chain_state` 的 `chain[i],chain[j]` trigger；publish_objects 的 get-frame ensures。
- 桶结构导致的 wall 未测。
