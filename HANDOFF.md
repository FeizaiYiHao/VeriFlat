# Handoff — 锁序 lctx 化（2026-10-22）

## 现状
- `main` = `ff62781`：第一批已集成、全绿、已推送。
  - `held_locks_order_below(lctx, page_bound)`（`src/kernel/kernel_k_define_spec.rs`）不再带 `KernelK`，
    三条锁序子句改成 `typed_lock_map_majors_lt(lctx.{cpu,page,thread}_lock_map(), 界)`，
    界分别是 `CPU_LOCK_MAJOR_OFF` / `page_bound` / `THREAD_SCHEDULED_LOCK_MAJOR`。
  - 已批准并加入的引理（只在这三处 reveal 对齐谓词）：
    `LockedArray::typed_lock_map_aligned_lock_id_at`（`src/locks/lock_array.rs`），
    `LockedMap::typed_lock_map_aligned_lock_id_at`、`LockedMap::typed_lock_map_aligned_majors_lt`（`src/locks/locked_map.rs`）。
  - 窗口锁 `lock_pagetable_window` requires 改为坐标级，id 级事实由
    `pagetable_window_typed_lock_map_ids_lt_from_order`（`pagetable_map_spec.rs`）在原语内证明（c5449cc）。
  - 单体 #34396：3094 verified / 0 errors，总 rlimit 1094.90M（前一版 1102.81M），wall 69 s，无函数 SMT > 10 s。
    NI #34397 通过，boot `cargo +1.98.1 check -p kernel / -p aloader`（在 `boot/` 下）通过。
- 分支 `lock-order-batch2-wip`：第二批的**未验证**起步（7 个 locker 文件的契约改写，+32/−33 行）。

## 还没做（第二批）
剩余 K 形式锁序子句约 52 条、12 个文件
（grep：`lock_map().dom().contains(x) ==> … lock_id_by_index( | state is Off | state is SCHEDULED`）：
1. 7 个不在 `held_locks_order_below` 链上的 locker（`locker_unlocker/`）：
   allocator_cache_1g、allocator_global_pool_1g、allocator_global_pool_ordered、cpu_set、iommu_table、quota_ordered、scheduler。
   WIP 分支里契约已机械改写，函数体和所有调用方还没修、没验证。
2. kill 的 3 个文件：`syscall_kill_container_lock_pairs.rs`、`syscall_kill_container_retire_lock.rs`
   （shards/cache_1g/pools_quotas 几条）、`syscall_kill_process_retire_pages_lock.rs`。
3. 保留 K 形式（语义上要"线程非 SCHEDULED"，不是锁序）：`kill_dequeue_scheduled_victim`、`wake_waiting_reply_caller`。
4. 用户已预先批准：`LockedArray::typed_lock_map_aligned_majors_lt(&self, held_locks, thread_id, major)`，
   requires 对齐谓词 + `forall|index| #![trigger held_locks.dom().contains(index)] … ==> self.spec_index(index).lock_id().major < major`，
   ensures `typed_lock_map_majors_lt(held_locks, major)`，函数体 `reveal(LockedArray::typed_lock_map_aligned)`。
   只在确有调用方需要（持有的页/CPU 集合是量化集合）时才加，放在 LockedArray 点引理之后。
5. 遗留小项：`thread_exit_reclaim_lock_table` 里 exec 内还有一处 reveal 对齐谓词
   （用于 `held_lock_majors_lt(IOMMU_ROOT_TABLE_LOCK_MAJOR)`），可用 cpu/ctn/prc/thr 四个点引理替换。

## 怎么继续
- 做法同第一批：先冻结 locker 契约（WIP 分支），再按 crate 分组并行修调用方；
  起点函数在已知 key 上调点引理（`krnl.cpu_arr/thr_mp/pg_arr.typed_lock_map_aligned_lock_id_at(lctx.<family>_lock_map(), lctx.thread_id(), key)`），
  量化集合用整表引理；不在 exec 里 reveal 对齐谓词，不用 assert forall / exists / choose / assume / spinoff，不提 rlimit，不加别的引理。
- 聚焦验证：`systemd-run --user --scope -p MemoryMax=30G ./verify-workspace.sh --package <pkg> -- --verify-only-module <mod>`；
  重活（全仓 `./verify-workspace.sh`、单体 `./verify.sh`、NI 在 `noninterference/`）机器上同时最多两个。
- 评估标准：单体总 rlimit 对比 1094.90M（#34396），无函数 > 10 s；留不留由用户决定后再推送。
- 第一批各包相对旧 K 形式：new_process −20%、new_container −10.8%、kill 组明显下降；thread_exit +7.8%、hotplug +4%、ipc +1.7%。
- 已知修过的运气点：`map_one_mmap_4k_page` 靠 `install_one_mmap_4k_directory_page` 那条 held-window ensures 的旧状态侧 trigger 才稳定。
