#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_alloc_page::allocate_free_4k_page::allocate_free_4k_impl_basd::allocate_free_4k_page;
use veriflat_kernel_core::*;

pub mod map_4k;
pub use map_4k::mmap_4k_build_structure::mmap_4k_build_one_structure;
pub use map_4k::share_mapping_4k::{
    empty_4k_directory_page_count,
    empty_4k_directory_page_count_spec,
    share_mapping_4k_build_and_share,
    share_mapping_4k_range_owner_compatible,
    share_mapping_4k_target_map_after,
    share_mapping_4k_source_owner_precheck,
    share_mapping_4k_source_precheck,
    share_mapping_4k_source_range_present,
};

verus! {
global size_of usize == 8;
}
