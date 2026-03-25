pub mod pages_container_spec;
pub mod pages_process_spec;
pub mod pages_allocator_spec;

pub mod page_array_pagetable_dom_spec;
pub mod page_array_pagetable_dom_impl;

pub mod pagetable_tlb_spec;

pub mod allocator_spec;
pub mod huge_page_spec;

pub use allocator_spec::*;
pub use huge_page_spec::*;
