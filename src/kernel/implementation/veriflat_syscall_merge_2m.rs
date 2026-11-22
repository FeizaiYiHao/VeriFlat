#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_alloc_page::merge_2m::{merge_2m_commit::merge_2m_commit,
    merge_2m_locking::{freeze_merge_2m_sources, thaw_merge_2m_sources, merge_2m_lock_block, merge_2m_unlock_block},
    merge_2m_cursor_queue::Merge2mCursor, merge_2m_scanner::Merge2mScanner, merge_2m_sort::merge_2m_sort_sources};

#[cfg(verus_keep_ghost)]
use veriflat_alloc_page::merge_2m::merge_2m_scanner_spec::{merge_2m_source_pages, merge_2m_complete_heads, merge_2m_cursor_suffix};
pub mod syscall_merge_2m;

verus! {
global size_of usize == 8;
}
