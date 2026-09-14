mod mmap_4k_create_entry_install;
mod mmap_4k_install_one;
pub mod mmap_4k_build_structure;
pub mod share_mapping_4k;

pub mod unmap_4k_present;
pub mod unmap_4k_remove;
pub mod unmap_4k_tlb;
pub mod unmap_4k_reclaim;
mod unmap_4k_reclaim_eof;
mod unmap_4k_reclaim_spec;
pub mod unmap_4k_flush_all;
pub mod unmap_4k_reclaim_one;
pub mod unmap_4k_range;
