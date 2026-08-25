#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_kernel_core::*;

pub mod allocate_free_4k_page;

verus! {
global size_of usize == 8;
}
