#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_alloc_page::free_4k_page::{refund_unmap_4k_quota, refund_unmap_4k_quota_trace};
use veriflat_map_4k::map_4k::unmap_iommu_4k_present::clear_iommu_4k_mapping_present;
use veriflat_map_4k::map_4k::unmap_iommu_4k_reclaim_one::reclaim_unmapped_iommu_4k_page;
use veriflat_map_4k::map_4k::flush_iommu_tlb::flush_iommu_tlb_for_table;
use veriflat_map_4k::map_4k::refund_unmap_4k_quota_to_thread::refund_unmap_4k_quota_to_thread;
#[cfg(verus_keep_ghost)]
use veriflat_map_4k::map_4k::unmap_4k_spec::THREAD_QUOTA_4K_REFUND_CAP;
use veriflat_map_4k::map_4k::unmap_4k_lock_running_thread::{unmap_4k_lock_running_thread, Unmap4kLocked};

pub mod syscall_iommu_unmap_4k;

verus! {
global size_of usize == 8;
}
