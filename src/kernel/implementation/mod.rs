#[cfg(not(feature = "split-crates"))]
pub mod syscall_alloc_quota;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_new_thread;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_new_thread_with_endpoint;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_new_endpoint;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_thread_exit;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_kill_process;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_kill_container;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_new_process;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_new_container;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_mmap_4k;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_unmap_4k;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_ipc;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_schedule;
#[cfg(not(feature = "split-crates"))]
pub mod rebalance_pull;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_cpu_hotplug;
#[cfg(not(feature = "split-crates"))]
pub mod syscall_pci;
pub mod locker_unlocker;
pub mod attach_endpoint_reference_and_unlock;
mod attach_endpoint_reference_and_unlock_eof;
pub mod create_thread_from_staged_page;
mod create_thread_from_staged_page_eof;
pub mod create_endpoint_from_staged_page;
mod create_endpoint_from_staged_page_eof;
pub mod create_process_from_staged_pages;
pub mod create_process_with_iommu_from_staged_pages;
pub mod create_container_from_staged_pages;
pub mod transfer_staged_4k_page;
mod transfer_staged_4k_page_eof;
pub mod lock_owned_2m_page_tails;
pub mod lock_allocated_2m_page_tails;
#[cfg(not(feature = "split-crates"))]
pub mod map_4k;
#[cfg(not(feature = "split-crates"))]
pub mod allocate_free_4k_page;
#[cfg(not(feature = "split-crates"))]
pub mod allocate_free_2m_page;

#[cfg(not(feature = "split-crates"))]
pub(crate) mod allocator_cache_spec;

#[cfg(not(feature = "split-crates"))]
pub mod free_4k_page;
#[cfg(not(feature = "split-crates"))]
pub mod reclaim_dangling_thread;
