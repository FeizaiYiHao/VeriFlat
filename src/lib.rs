#![feature(adt_const_params)]

use vstd::prelude::*;
pub mod define;
pub mod lemma;
pub mod util;
pub mod primitive;
pub mod locks;
pub mod linkedlist;
pub mod page;
pub mod cpu;
pub mod proc;
pub mod allocator;
pub mod pagetable_seq;
pub mod iommu;
pub mod test;
pub mod kernel;

pub use define::*;
pub use lemma::*;
pub use util::*;
pub use primitive::*;
pub use locks::*;
pub use linkedlist::*;
pub use page::*;
pub use cpu::*;
pub use proc::*;
pub use allocator::*;
pub use pagetable_seq::*;
pub use iommu::*;
pub use kernel::*;
pub use kernel::implementation::allocate_free_4k_page::allocate_free_4k_impl_basd::allocate_free_4k_page;
pub use kernel::implementation::allocate_free_4k_page::allocate_free_4k_pages::{
    allocate_free_4k_pages,
    allocated_4k_page_lock_perms_wf,
    page_ptrs_to_indices,
};
pub use kernel::implementation::create_process_from_staged_pages::*;
pub use kernel::implementation::create_process_with_iommu_from_staged_pages::*;
pub use kernel::implementation::map_4k::mmap_4k_context::{
    mmap_4k_allocation_ready,
    mmap_4k_held_context,
    mmap_4k_no_page_locks,
    staged_4k_page_op_ensures,
    staged_4k_page_op_requires,
    staged_4k_page_table_op_requires,
};
pub use kernel::implementation::map_4k::mmap_4k_stage_page::stage_mmap_4k_page;
pub use kernel::implementation::map_4k::mmap_4k_build_structure::mmap_4k_build_one_structure;
pub use kernel::implementation::map_4k::share_mapping_4k::{
    share_mapping_4k_build_and_share,
    share_mapping_4k_held_context,
    share_mapping_4k_range_owner_compatible,
    share_mapping_4k_source_owner_precheck,
    share_mapping_4k_source_precheck,
    share_mapping_4k_source_range_present,
};

verus! {
global size_of usize == 8;

fn test(){
    assert(1 + 1 == 2);
}

}

fn main(){

}
