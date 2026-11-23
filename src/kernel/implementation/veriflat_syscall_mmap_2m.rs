#![no_std]

use vstd::prelude::*;

use veriflat_kernel_core::*;
use veriflat_map_4k::*;
use veriflat_map_4k::map_4k::mmap_4k_build_structure::MissingPageTableLevel;
use veriflat_alloc_page::allocate_free_2m_page::allocate_free_2m_impl_base::allocate_free_2m_page;
pub use veriflat_map_4k::map_4k::mmap_4k_install_one::install_one_mmap_2m_directory_page;
use veriflat_map_4k::map_4k::hide_empty_l1_in_window::hide_empty_l1_in_window;
use veriflat_map_4k::map_4k::reclaim_hidden_l1_page_in_window::reclaim_hidden_l1_page_in_window;
use veriflat_map_4k::map_4k::unmap_4k_flush_all::flush_pagetable_tlbs;

#[cfg(verus_keep_ghost)]
use veriflat_map_4k::map_4k::unmap_4k_trace::unmap_4k_tlb_flush_steps_from_k;
pub mod syscall_mmap_2m;

verus! {
global size_of usize == 8;
}
