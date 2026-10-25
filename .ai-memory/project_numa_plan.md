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

## CPU 入口锁（IPI 模型，2026-10-25 定稿，可先于 NUMA 单独做）

目的：把"远端 CPU 是否在内核里"和"本 CPU 是否关中断"两个缺失的模型合成一把锁，闭合
`src/cpu/atomic_pcid_cr3.rs` 里 "model the IPI wait as a virtual lock" 的 TODO，并去掉 CPU 的 kill 标记。
- 每 CPU 一把只有写模式的入口锁，内容是两个 tracked perm：`SyscallPerm(cpu)`（可在本 CPU 执行
  内核步骤）、`IpiPerm(cpu)`（可向本 CPU 发 IPI）。lock id 的 container/process 深度与该 CPU 的
  CPU 锁相同，major 低 1；随 CPU 锁一起 rekey（切进程、evict、上下线）。
- 不变量（KernelK 级，跨入口锁和 CPU 锁）：CPU 非 Off 且入口锁未被写持 ⇒ 两个 perm 都在锁里；
  Off ⇒ SyscallPerm 不存在。
- 本地：陷入（syscall/timer/缺页）后 swapgs、换栈、存帧，`sti`，自旋拿入口锁，`cli`，再按 step
  锁放 CPU 锁；`sysret` / idle `hlt` 前放回。TCB 规则只剩"IF=1 ⇔ 本地未持入口锁"。拿到锁后重查
  CPU 状态（自旋期间 evict handler 可能已跑过），已 Idle 则返回 CpuIdle。
- 远端：所有 IPI（evict、唤醒）都先写持目标入口锁、凭 IpiPerm 发。唤醒 IPI 现在四处都在放干净
  所有锁之后发，无锁序问题；evict 由 killer 在持受害者线程锁时取，需要和 `wlock_cpu` killer 分支
  同样的锁序豁免。持有入口锁 ⇒ 目标不在内核、中断开着、IPI 必到，ack 等待有界。
- kill：CPU 的 kill 标记去掉；线程标记和 `*_unless_killed` 保留（目标在 syscall 里要锁自己当前线程时
  看标记返回 None → CpuIdle → 放入口锁）。
- 上线/下线：上线方持目标（Off）入口锁，TCB `mint_syscall_perm` 存入锁，放锁，发唤醒 IPI；目标醒来
  拿自己的入口锁，有 SyscallPerm 才进 `cpu_online_resume`，没有（杂散唤醒）就放锁再 `hlt`。
  下线方 `cpu_offline_check` 走到 Off 时持入口锁调 TCB `collect_syscall_perm` 销毁，放锁，`hlt`。
- 不进模型：NMI 刷 PCID 路径（不拿锁、无模型效果）。
- 成本：每次 syscall 多一对本地无争用的锁操作（约 20 周期一次）和一对 `sti`/`cli`。

## 接受的双写者低频 line（不改）
远端唤醒写别人的调度 shard、unmap 远端置 `pcid_needflush`、kill 的 cpu/thread 标记、
真实共享页的页锁字。

## 顺序
标注 + 本地队列/pool（便宜）→ 数组拆节点 + RwLock 读计数拆节点（测了再做）→ 页表惰性备份
（最贵，等 #PF 模型定了）。

## 对比时要测
缺页/mmap/unmap 吞吐随节点数的伸缩（论点命门）、同节点与跨节点 IPC 往返、锚点读锁争用
（1 节点 vs N 节点缺页压测），基线 Linux 和 Barrelfish 类 multikernel。
