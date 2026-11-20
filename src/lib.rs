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
pub mod iommu_table;
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
pub use iommu_table::*;
pub use kernel::*;
pub use kernel::implementation::merge_2m::{merge_2m_commit::merge_2m_commit,
    merge_2m_locking::{freeze_merge_2m_sources, thaw_merge_2m_sources, merge_2m_lock_block, merge_2m_unlock_block},
    merge_2m_cursor_queue::Merge2mCursor, merge_2m_scanner::Merge2mScanner, merge_2m_sort::merge_2m_sort_sources};
#[cfg(verus_keep_ghost)]
pub use kernel::implementation::merge_2m::merge_2m_scanner_spec::{merge_2m_source_pages, merge_2m_complete_heads, merge_2m_cursor_suffix};
pub use kernel::implementation::split_2m::{split_2m_commit::split_2m_commit,
    split_2m_locking::{freeze_split_2m_sources, thaw_split_2m_sources}, split_2m_sources::split_2m_select_source};
#[cfg(verus_keep_ghost)]
use kernel::implementation::split_2m::split_2m_entry_points::{thread_quota_2m_implies_allocator_free_count_positive, thread_quota_4k_implies_split_quota_capacity};
pub use kernel::implementation::free_4k_page::*;
pub use kernel::implementation::free_2m_page::drain_2m_cache_batch;
pub use kernel::implementation::reclaim_dangling_thread::*;
pub use kernel::implementation::allocate_free_4k_page::allocate_free_4k_impl_base::allocate_free_4k_page;
pub use kernel::implementation::allocate_free_4k_page::allocate_free_4k_pages::allocate_free_4k_pages;
#[cfg(verus_keep_ghost)]
pub use kernel::implementation::allocate_free_4k_page::allocate_free_4k_pages::{allocated_4k_page_lock_perms_wf, page_ptrs_to_indices};
pub use kernel::implementation::allocate_free_2m_page::allocate_free_2m_impl_base::allocate_free_2m_page;
pub use kernel::implementation::create_endpoint_from_staged_page::*;
pub use kernel::implementation::create_process_from_staged_pages::*;
pub use kernel::implementation::create_process_with_iommu_from_staged_pages::*;
pub use kernel::implementation::page_2m_region::*;
pub use kernel::implementation::page_1g_region::*;
pub use kernel::implementation::create_container_from_staged_pages::*;
pub use kernel::implementation::map_4k::mmap_4k_build_structure::mmap_4k_build_one_structure;
use kernel::implementation::map_4k::mmap_4k_build_structure::MissingPageTableLevel;
pub use kernel::implementation::map_4k::mmap_4k_install_one::install_one_mmap_4k_directory_page;
pub use kernel::implementation::map_4k::share_mapping_4k_child_structure::build_new_child_structure;
pub use kernel::implementation::map_4k::mmap_4k_build_structure_spec::*;
pub use kernel::implementation::map_4k::mmap_1g_install_directory::*;
pub use kernel::implementation::map_4k::mmap_1g_install_directory_spec::*;
#[cfg(verus_keep_ghost)]
use kernel::implementation::allocate_free_1g_page::allocate_free_1g_page_lemmas::kernel_inv_implies_container_allocator_1g_quota_bounded;
pub use kernel::implementation::map_4k::map_iommu_4k_spec::*;
pub use kernel::implementation::map_4k::map_iommu_4k::map_shared_page_into_iommu_4k;
pub use kernel::implementation::map_4k::map_iommu_4k_directory::install_staged_4k_iommu_table_page;
use kernel::implementation::map_4k::unmap_4k_range::unmap_4k_range;
use kernel::implementation::map_4k::refund_unmap_4k_quota_to_thread::refund_unmap_4k_quota_to_thread;
use kernel::implementation::map_4k::unmap_4k_lock_running_thread::{unmap_4k_lock_current_thread, unmap_4k_lock_running_thread, Unmap4kLocked};
use kernel::implementation::map_4k::mmap_4k_lock_current_thread::{mmap_4k_lock_current_thread, mmap_4k_range_l2_bounds, mmap_4k_unlock_and_finish, mmap_4k_unlock_read_rejected};
use kernel::implementation::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;
pub use kernel::implementation::map_4k::mmap_4k_install_one::install_one_mmap_2m_directory_page;
use kernel::implementation::map_4k::hide_empty_l1_in_window::hide_empty_l1_in_window;
use kernel::implementation::map_4k::reclaim_hidden_l1_page_in_window::reclaim_hidden_l1_page_in_window;
use kernel::implementation::map_4k::unmap_iommu_4k_present::clear_iommu_4k_mapping_present;
use kernel::implementation::map_4k::unmap_iommu_4k_reclaim_one::{reclaim_unmapped_iommu_4k_page, reclaim_detached_iommu_4k_page};
use kernel::implementation::map_4k::flush_iommu_tlb::flush_iommu_tlb_for_table;
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
pub use kernel::implementation::map_4k::share_mapping_4k_trace::share_4k_range_steps_from_directory;
#[cfg(verus_keep_ghost)]
pub use kernel::implementation::locker_unlocker::container_nonlock_fields_and_quotas_unchanged_for_cpu_set_relock;
pub use kernel::implementation::transfer_staged_4k_page::*;

verus! {
global size_of usize == 8;
// Layouts of the lock objects retyped from owned pages, checked against rustc; callers of `retype_page_perm_to_rwlock`
// and `retype_page_perm_2m_to_rwlock` discharge the layout `requires` with `broadcast use crate::VERUS_layout_of_<type>`.
global layout ThreadRwLock is size == 760, align == 8;
global layout Registers is size == 168, align == 8;
global layout ProcessRwLock is size == 256, align == 8;
global layout EndpointRwLock is size == 72, align == 8;
global layout CpuSetRwLock is size == 1856, align == 64;
global layout IommuTableRwLock is size == 64, align == 8;
global layout PageTableRwLock is size == 2176, align == 64;
global layout PcidAllocatorRwLock is size == 32776, align == 8;
}

fn main() {}
