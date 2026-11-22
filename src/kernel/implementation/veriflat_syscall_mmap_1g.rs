#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_map_4k::*;
use veriflat_map_4k::map_4k::mmap_1g_install_directory::*;
use veriflat_map_4k::map_4k::mmap_1g_install_directory_spec::*;

pub mod syscall_mmap_1g;

verus! {
global size_of usize == 8;
}
