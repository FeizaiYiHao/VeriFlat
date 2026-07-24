---
name: project_syscall_new_thread_kernelsteps_inv
description: syscall_new_thread postcondition needs KernelSteps.inv() to bridge old_u and old_k
---

在 syscall_new_thread 的 postcondition 中，solver 无法自动关联 old(self) 的内核状态与 old_u 的用户状态。必须显式引入 `KernelSteps.inv()` 不变量，建立 `old_u == kernel_k_to_kernel_u(old_k)` 及 `old_k.inv()` 的推理链，使 solver 能推导出关键事实（如 `old_u.cpu_array.len() == NUM_CPUS`、`process_ptr ∈ old_u.process_map.dom()`）。

**Why:** 跨 boundary 的 syscall 中 kernel_u_* helper spec fn 需要 K-state ↔ U-state 桥接，solver 推理链不够长。
