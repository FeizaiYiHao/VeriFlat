#![feature(adt_const_params)]

use vstd::prelude::*;

use veriflat_alloc_page::allocate_free_4k_page::allocate_free_4k_impl_base::allocate_free_4k_page;
use veriflat_kernel_core::*;
use veriflat_alloc_page::free_4k_page::{drain_4k_cache_batch, refund_unmap_4k_quota};

pub mod map_4k;
pub use map_4k::mmap_4k_build_structure::mmap_4k_build_one_structure;
pub use map_4k::share_mapping_4k::{
    required_4k_directory_pages_for_empty_target,
    spec_required_4k_directory_pages_for_empty_target,
    share_mapping_4k_build_and_share,
    share_mapping_4k_range_owner_compatible,
    share_mapping_4k_target_map_with_shared_prefix,
    share_mapping_4k_source_owner_precheck,
    share_mapping_4k_source_precheck,
    share_mapping_4k_source_range_present,
};

verus! {
global size_of usize == 8;
}
