#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_alloc_page::allocate_free_4k_page::allocate_free_4k_impl_basd::allocate_free_4k_page;
use veriflat_kernel_core::*;

pub mod map_4k;
pub use map_4k::*;

verus! {
global size_of usize == 8;
}
