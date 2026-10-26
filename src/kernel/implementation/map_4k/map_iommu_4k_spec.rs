use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::mmap_4k_build_structure_spec::mmap_4k_installed_directory;

verus! {
/// Installing an IOMMU directory page records its level in IOMMU-map progress.
pub open spec fn iommu_map_4k_progress_after_directory(progress: Option<SyscallProgress>, level: MissingPageTableLevel) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::IommuMap4k { va_range, iova_range, mapped, directory: _ }) => Some(SyscallProgress::IommuMap4k { va_range, iova_range, mapped, directory: mmap_4k_installed_directory(level) }),
        _ => progress,
    }
}

/// Publishing an IOMMU leaf moves IOMMU-map progress to the next page with no directory installed.
pub open spec fn iommu_map_4k_progress_after_leaf(progress: Option<SyscallProgress>) -> Option<SyscallProgress> {
    match progress {
        Some(SyscallProgress::IommuMap4k { va_range, iova_range, mapped, directory: _ }) => Some(SyscallProgress::IommuMap4k { va_range, iova_range, mapped: (mapped + 1) as usize, directory: Mmap4kDirectory::None }),
        _ => progress,
    }
}
} // verus!
