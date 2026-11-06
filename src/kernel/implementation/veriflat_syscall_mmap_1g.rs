#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_map_4k::*;
use veriflat_map_4k::map_4k::mmap_1g_install_directory::*;

pub mod syscall_mmap_1g;

verus! {
global size_of usize == 8;
}
