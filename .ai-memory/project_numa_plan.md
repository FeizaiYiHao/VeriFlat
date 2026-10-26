# NUMA 计划（设计方向，2026-10-22 与用户讨论定稿）

目标：证明单内核（一个 `KernelK`、锁不变量保证一致性）不用 multikernel 也能拿到
极佳的 NUMA 性能。原则：**内核保证每个对象的位置和"一个 cache line 只有一个写者"
的单向流纪律，局部性策略交给用户态**。跨节点流量只允许三类：缺页拉锚点页表
（一次远端读）、unmap 写 N 份备份（单写者）、用户自己选择的跨节点 IPC/唤醒。

## 要做的改动

1. **节点标注**：Thread、Endpoint、物理页（Page 元数据）各加一个 NUMA 节点字段。
   CPU 本地队列和线程/进程 allocator 缓存只装本节点的线程和页。
   暴露一个便宜的"当前节点"只读查询给用户态；endpoint 跨不跨节点由用户决定
   （服务每节点各开一个 endpoint，客户端挑本节点的），内核不做跨节点 IPC 优化。
2. **定长数组拆每节点**：`pg_arr`、`cpu_arr`、调度 shard、pool 表等每节点一份，
   放在本节点内存，条目按 cache line 对齐。`KernelK` 里按指针键的 ghost map 不动，
   对象在哪个节点分配就在哪。
3. **全局 pool 4k/2m/1g 每节点一份**（container/process/thread 三级配额已经分散，不动）。
   本节点 pool 空了不借远端页。
4. **多节点共读对象的读锁字**（唯一要改设计的热点）：读锁的原子加减让锁字在所有读者节点间
   乒乓。决定（2026-10-25）：
   - 页表 root/锚点的上层：目录页在进程存活期间只增不减，读上层不拿锁；缺页只拿窗口读锁，
     争用按 2M 分散。exit/kill 释放目录页的 grace 条件就是现有的"cpu_set 清空、所有 CPU 切走"。
   - 真要排除读者的对象：写者置标志 + 凭 IpiPerm 给 cpu_set 发 IPI 等 ack，读者只做普通 load
     （见"CPU 入口锁"）；备选 brlock（每 CPU 一个 bit、各占一个 line，读者 `lock bts` 自己的，
     写者按序拿全部）。
   - 不做 RCU：VeriFlat 里 RCU 只能是异步形态，表示层改动大，收益只是省读者一个屏障。
5. **页表惰性备份**（Mitosis lazy 模式）：
   - 每个开了备份的进程有一个锚点页表 + 每节点一个备份 root；CPU 的 CR3 指向本节点备份。
   - 不变量在**映射层**：备份里每个 va→(pa, perms) 在锚点里也有（有 2M 拆分，不能按表项比）。
   - mmap 只写锚点；备份靠缺页补：rlock 锚点窗口、读表项链、wlock 自己备份的窗口、
     从本节点 pool 分配备份的 L3/L2/L1 页（记进程配额）、写入。
   - unmap/权限降级/拆分后撤 4k：先清每个备份里的对应项（各拿写锁），再改锚点，再 flush。
   - 决定：缺页时本节点配额/pool 不够 → 把该 CPU 的 CR3 切到锚点继续跑（远端走表），
     不杀线程、不预留。
   - 决定：备份 root 的内核上半区每节点一份（内核映射也复制，boot/热插拔同步 N 份）。
   - 决定：进程级开关，默认关；关时全部 CPU 用锚点。
   - 依赖：#PF 路径和中断模型（未决设计之一）要先定。
6. **TLB shootdown**：靠放置减少跨节点；用已有的 CR3-skip/stale 标记对远端空闲 CPU 延迟刷，
   PCID 避免整刷。

## CPU 入口锁（已被取代）

本节原先的"独立 CpuEntry 入口锁 + SyscallPerm/IpiPerm"方案已放弃，以 `HANDOFF-cpu-entry-lock.md` 为准。要点：
- `SyscallPerm` 放在 `Cpu` 对象里（`Cpu.syscall_perm`，受既有 CPU 锁保护），由 TCB `u_sys_enter` / `u_sys_exit` 在 `Cpu` 与 lctx 槽之间移动；
  Off CPU 没有 SyscallPerm，不能进内核步骤。
- 不新增入口锁对象 / 锁族，不设 `IpiPerm`；删 offline kick、保留 online wake、删 CPU kill 状态。

## 接受的双写者低频 line（不改）
远端唤醒写别人的调度 shard、unmap 远端置 `pcid_needflush`、kill 的 cpu/thread 标记、
真实共享页的页锁字。

## 顺序
标注 + 本地队列/pool（便宜）→ 数组拆节点 + RwLock 读计数拆节点（测了再做）→ 页表惰性备份
（最贵，等 #PF 模型定了）。

## 对比时要测
缺页/mmap/unmap 吞吐随节点数的伸缩（论点命门）、同节点与跨节点 IPC 往返、锚点读锁争用
（1 节点 vs N 节点缺页压测），基线 Linux 和 Barrelfish 类 multikernel。
