#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_map_4k::map_4k::unmap_4k_spec::*;

pub mod syscall_unmap_2m;

verus! {
global size_of usize == 8;
}
