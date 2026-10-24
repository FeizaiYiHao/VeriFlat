#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_alloc_page::free_4k_page::refund_unmap_4k_quota;
use veriflat_alloc_page::reclaim_dangling_thread::{reclaim_killed_thread_chain, release_killed_thread_caller};
use veriflat_map_4k::map_4k::unmap_4k_present::clear_4k_mapping_present;
use veriflat_map_4k::map_4k::unmap_4k_reclaim_one::reclaim_unmapped_4k_page;
use veriflat_map_4k::map_4k::unmap_4k_tlb::{mark_pcid_needflush_and_load, flush_remote_pcid_and_clear, flush_local_pcid_and_clear};
use veriflat_map_4k::map_4k::unmap_iommu_4k_present::clear_iommu_4k_mapping_present;
use veriflat_map_4k::map_4k::unmap_iommu_4k_reclaim_one::reclaim_unmapped_iommu_4k_page;
use veriflat_map_4k::map_4k::flush_iommu_tlb::flush_iommu_tlb_for_table;
use veriflat_map_4k::map_4k::unmap_4k_remove::remove_4k_mapping_without_free;
use veriflat_map_4k::map_4k::unmap_iommu_4k_remove::remove_iommu_4k_mapping_without_free;

pub mod syscall_kill_process;
pub mod syscall_kill_container;

verus! {
global size_of usize == 8;
}
