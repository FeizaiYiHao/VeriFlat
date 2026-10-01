#![feature(adt_const_params)]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_map_4k::map_4k::unmap_4k_range::unmap_4k_range;
use veriflat_map_4k::share_mapping_4k_source_precheck;
use veriflat_map_4k::map_4k::unmap_4k_spec::*;

pub mod syscall_unmap_4k;

verus! {
global size_of usize == 8;
}
