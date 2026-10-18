#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_alloc_page::free_4k_page::refund_unmap_4k_quota;
use veriflat_alloc_page::reclaim_dangling_thread::reclaim_killed_thread_chain;
use veriflat_map_4k::map_4k::unmap_4k_present::clear_4k_mapping_present;
use veriflat_map_4k::map_4k::unmap_4k_reclaim_one::reclaim_unmapped_4k_page;
use veriflat_map_4k::map_4k::unmap_4k_tlb::{mark_pcid_needflush_and_load, flush_remote_pcid_and_clear, flush_local_pcid_and_clear};
use veriflat_map_4k::map_4k::unmap_iommu_4k_present::clear_iommu_4k_mapping_present;
use veriflat_map_4k::map_4k::unmap_iommu_4k_reclaim_one::reclaim_unmapped_iommu_4k_page;

pub mod syscall_kill_process;

verus! {
global size_of usize == 8;
}
