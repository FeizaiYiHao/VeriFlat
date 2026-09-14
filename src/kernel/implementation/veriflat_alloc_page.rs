#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;

pub mod allocate_free_4k_page;
pub mod allocate_free_2m_page;
pub mod free_4k_page;

verus! {
global size_of usize == 8;
}

pub(crate) mod allocator_cache_spec;
