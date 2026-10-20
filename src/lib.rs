#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;
pub mod define;
pub mod lemma;
pub mod util;
pub mod primitive;
pub mod locks;
pub mod linkedlist;
pub mod page;
pub mod cpu;
pub mod proc;
pub mod allocator;
pub mod pagetable_seq;
pub mod pagetable_concurrent;
pub mod iommu;
pub mod kernel;

pub use define::*;
pub use lemma::*;
pub use util::*;
pub use primitive::*;
pub use locks::*;
pub use linkedlist::*;
pub use page::*;
pub use cpu::*;
pub use proc::*;
pub use allocator::*;
pub use pagetable_seq::*;
pub use pagetable_concurrent::*;
pub use iommu::*;
pub use kernel::*;
pub use kernel::implementation::free_4k_page::*;
pub use kernel::implementation::reclaim_dangling_thread::*;
pub use kernel::implementation::allocate_free_4k_page::allocate_free_4k_impl_base::{allocate_free_4k_page, allocate_free_4k_page_k};
pub use kernel::implementation::allocate_free_4k_page::allocate_free_4k_pages::allocate_free_4k_pages;
#[cfg(verus_keep_ghost)]
pub use kernel::implementation::allocate_free_4k_page::allocate_free_4k_pages::{allocated_4k_page_lock_perms_wf, page_ptrs_to_indices};
pub use kernel::implementation::allocate_free_2m_page::allocate_free_2m_impl_base::allocate_free_2m_page;
pub use kernel::implementation::create_endpoint_from_staged_page::*;
pub use kernel::implementation::create_process_from_staged_pages::*;
pub use kernel::implementation::create_process_with_iommu_from_staged_pages::*;
pub use kernel::implementation::lock_owned_2m_page_tails::*;
pub use kernel::implementation::create_container_from_staged_pages::*;
pub use kernel::implementation::map_4k::mmap_4k_build_structure::mmap_4k_build_one_structure;
pub use kernel::implementation::map_4k::mmap_4k_build_structure_spec::*;
use kernel::implementation::map_4k::unmap_4k_range::unmap_4k_range;
use kernel::implementation::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;
use kernel::implementation::map_4k::unmap_4k_present::clear_4k_mapping_present;
use kernel::implementation::map_4k::unmap_4k_reclaim_one::reclaim_unmapped_4k_page;
use kernel::implementation::map_4k::unmap_iommu_4k_present::clear_iommu_4k_mapping_present;
use kernel::implementation::map_4k::unmap_iommu_4k_reclaim_one::reclaim_unmapped_iommu_4k_page;
use kernel::implementation::map_4k::unmap_4k_remove::remove_4k_mapping_without_free;
use kernel::implementation::map_4k::unmap_iommu_4k_remove::remove_iommu_4k_mapping_without_free;
use kernel::implementation::map_4k::unmap_4k_tlb::{mark_pcid_needflush_and_load, flush_remote_pcid_and_clear, flush_local_pcid_and_clear};

use kernel::implementation::map_4k::unmap_4k_spec::*;
pub use kernel::implementation::map_4k::share_mapping_4k_spec::*;
pub use kernel::implementation::map_4k::share_mapping_4k::{share_mapping_4k_build_and_share, share_mapping_4k_source_owner_precheck, share_mapping_4k_source_precheck};
#[cfg(verus_keep_ghost)]
pub use kernel::implementation::map_4k::share_mapping_4k::{share_mapping_4k_leaf_owner_compatible, share_mapping_4k_range_owner_compatible, share_mapping_4k_source_range_present};
#[cfg(verus_keep_ghost)]
pub use kernel::implementation::map_4k::share_mapping_4k::{share_mapping_4k_range_owner_compatible_own_container, share_mapping_4k_source_range_present_from_wf};
#[cfg(verus_keep_ghost)]
pub use kernel::implementation::locker_unlocker::container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock;
pub use kernel::implementation::transfer_staged_4k_page::*;

verus! {
global size_of usize == 8;
}

fn main() {}
