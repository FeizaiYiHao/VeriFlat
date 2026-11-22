#![no_std]

use vstd::prelude::*;

use veriflat_kernel_core::*;

pub mod allocate_free_4k_page;
pub mod allocate_free_2m_page;
pub mod allocate_free_1g_page;
pub(crate) mod allocator_cache_spec;
pub mod free_4k_page;
pub mod free_2m_page;
pub mod free_1g_page;
pub mod reclaim_dangling_thread;
pub mod merge_2m;
pub mod split_2m;

verus! {
global size_of usize == 8;
}
