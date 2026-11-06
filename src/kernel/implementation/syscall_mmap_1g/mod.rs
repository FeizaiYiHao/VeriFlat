pub mod syscall_mmap_1g_spec;
mod syscall_mmap_1g_map_owned;
mod syscall_mmap_1g_map_owned_eof;
mod syscall_mmap_1g_hide_entry;
mod syscall_mmap_1g_hide_entry_eof;
mod syscall_mmap_1g_map_trace;
mod syscall_mmap_1g_map_one_leaf;
mod syscall_mmap_1g_map_range;
mod syscall_mmap_1g_precheck;
mod syscall_mmap_1g_trace;
mod syscall_mmap_1g_exit;
mod syscall_mmap_1g_clear_trace;
mod syscall_mmap_1g_clear_reclaim;
mod syscall_mmap_1g_clear_range;
mod syscall_mmap_1g_helpers;
mod syscall_mmap_1g_lock;
mod syscall_mmap_1g;

pub use syscall_mmap_1g::syscall_mmap_1g;
