---
name: project_memory_model_core_concepts
description: VeriFlat memory model — Page metadata vs PagePtr physical address vs PagePerm ownership
---

VeriFlat 内存模型核心概念:
- `Page` struct 是页面元数据（state/owning_container/ref_count等），存储在 `page_array` 中
- `PagePtr` 是 4K/2M/1G 物理内存块的地址
- `PageIndex` 由 `PagePtr` 计算得出，用于索引 `page_array` 中的元数据
- `PagePerm4k` 是 `PointsTo<4K物理内存>`，代表物理内存的 tracked ownership
- `LockedArray<Page>` 仅管理元数据，与物理内存无 PointsTo 冲突
- `page.addr == page_ptr` 等价性通过 `page_index2page_ptr` 单向映射保证，而非 Page.addr 字段
- 项目倾向简化地址表示：删除 Page.addr 字段，仅保留 page_index→page_ptr 映射
- Page perm 字段类型为 `Tracked<Option<PagePerm>>`（非 `Option<Tracked<...>>`），支持 proof 上下文中安全 unwrap
