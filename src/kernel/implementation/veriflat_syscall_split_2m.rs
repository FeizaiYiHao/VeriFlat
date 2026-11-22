#![feature(adt_const_params)]
#![no_std]

use vstd::prelude::*;
use veriflat_kernel_core::*;
use veriflat_alloc_page::split_2m::{split_2m_commit::split_2m_commit,
    split_2m_locking::{freeze_split_2m_sources, thaw_split_2m_sources}, split_2m_sources::split_2m_select_source};
#[cfg(verus_keep_ghost)]
use veriflat_alloc_page::merge_2m::{merge_2m_quota_folds::{allocator_free_page_ptrs_wf_implies_free_count_fold_bounded, container_process_allocator_quota_4k_wf_at, container_process_allocator_quota_2m_wf_at},
    merge_2m_entry_points::{container_allocator_4k_forward_wf_at, container_allocator_2m_forward_wf_at},
    merge_2m_entry_folds::{container_thread_and_perms_wf_implies_4k_fold_sum_ge_thread_quota, container_thread_and_perms_wf_implies_2m_fold_sum_ge_thread_quota}};
use veriflat_alloc_page::merge_2m::merge_2m_locking::{merge_2m_lock_block, merge_2m_unlock_block};
pub mod syscall_split_2m;

verus! {
global size_of usize == 8;
}
