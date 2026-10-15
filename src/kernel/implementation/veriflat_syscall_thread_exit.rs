#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_alloc_page::free_4k_page::{drain_4k_cache_batch, refund_unmap_4k_quota};
use veriflat_map_4k::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;
use veriflat_map_4k::map_4k::unmap_4k_present::clear_4k_mapping_present;
use veriflat_map_4k::map_4k::unmap_4k_reclaim_one::reclaim_unmapped_4k_page;
use veriflat_map_4k::map_4k::unmap_iommu_4k_present::clear_iommu_4k_mapping_present;
use veriflat_map_4k::map_4k::unmap_iommu_4k_reclaim_one::reclaim_unmapped_iommu_4k_page;
use veriflat_map_4k::map_4k::unmap_4k_spec::unmap_4k_locked;

pub mod syscall_thread_exit;

verus! {
global size_of usize == 8;
}
