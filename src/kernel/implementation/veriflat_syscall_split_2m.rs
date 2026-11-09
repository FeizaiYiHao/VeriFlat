#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_alloc_page::split_2m::{split_2m_commit::split_2m_commit,
    split_2m_locking::{freeze_split_2m_sources, thaw_split_2m_sources}, split_2m_sources::split_2m_select_source};
#[cfg(verus_keep_ghost)]
use veriflat_alloc_page::split_2m::split_2m_entry_points::{thread_quota_2m_implies_allocator_free_count_positive, thread_quota_4k_implies_split_quota_capacity};
use veriflat_alloc_page::merge_2m::merge_2m_locking::{merge_2m_lock_block, merge_2m_unlock_block};
pub mod syscall_split_2m;

verus! {
global size_of usize == 8;
}
