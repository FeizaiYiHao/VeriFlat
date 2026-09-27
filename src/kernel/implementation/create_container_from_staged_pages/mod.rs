pub(super) use crate::kernel::implementation::lock_owned_2m_page_tails::{
    distinct_2m_heads_have_disjoint_all_ptrs,
    distinct_2m_heads_have_disjoint_tails,
    owned_4k_page_not_in_2m_region,
    owned_4k_page_not_in_2m_tail,
    page_2m_all_ptrs_contains_head,
    page_2m_all_ptrs_contains_index,
    page_2m_ptr_prefix_member_bounds,
    page_ptr_indices_disjoint_from_2m_tail,
    page_ptr_sequence_index_in_equal_set,
    page_ptr_sequence_index_in_mapped_set,
    set_owned_2m_page_tail_pair_container,
};

mod publish;
mod publish_objects;
mod eof_pages;
mod eof_allocator;
mod eof_process;
mod eof_close;
mod eof_publish;

pub use publish::*;
pub use publish_objects::*;
pub use eof_pages::*;
pub use eof_allocator::*;
pub use eof_process::*;
pub use eof_close::*;
pub use eof_publish::*;
