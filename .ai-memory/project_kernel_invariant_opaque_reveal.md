---
name: project_kernel_invariant_opaque_reveal
description: All kernel invariants are #[verifier::opaque] — must explicitly reveal() in proof blocks
---

项目中所有 kernel invariant（如 process_cpu_wf, page_array_wf, subsystems_inv 等）均标记为 `#[verifier::opaque]`，在 proof block 中需显式调用 `reveal(invariant_name)` 才能展开使用，不可直接依赖其内部结构。

**How to apply:** 每次需要在 proof 中使用 invariant 的内部结构时，先 `reveal()`。如果 reveal 后仍无法实例化，检查 trigger 是否匹配（见 feedback_ask_before_invariant_triggers）。
