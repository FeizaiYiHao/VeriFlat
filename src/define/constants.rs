use vstd::prelude::*;

verus! {

// -------------------- Begin of Const --------------------
pub const MAX_NUM_ENDPOINT_DESCRIPTORS: usize = 128;

pub const MAX_NUM_THREADS_PER_PROC: usize = 128;

pub const MAX_NUM_THREADS_PER_ENDPOINT: usize = 128;

pub const MAX_NUM_PROCS: usize = PCID_MAX;

pub const MAX_NUM_THREADS: usize = 500 * 4096;

pub const IPC_MESSAGE_LEN: usize = 1024;

pub const IPC_PAGEPAYLOAD_LEN: usize = 128;

//1 for now
pub const KERNEL_MEM_END_L4INDEX: usize = 1;

//8GiB
pub const NUM_PAGES: usize = 2 * 1024 * 1024;

pub const PAGE_SZ_4k: usize = 1usize << 12;

pub const PAGE_SZ_2m: usize = 1usize << 21;

pub const PAGE_SZ_1g: usize = 1usize << 30;

pub const MAX_USIZE: u64 = 31 * 1024 * 1024 * 1024;

pub const PCID_MAX: usize = 4096;

pub const IOID_MAX: usize = 4096;

pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_2m_MASK: u64 = 0x0000_ffff_ffe0_0000;

pub const MEM_1g_MASK: u64 = 0x0000_fffc_0000_0000;

pub const VA_PERM_MASK: u64 = 0x8000_0000_0000_0002;

pub const READ: usize = 0x8000_0000_0000_0000u64 as usize;

pub const READ_WRITE: usize = 0x8000_0000_0000_0002u64 as usize;

pub const READ_EXECUTE: usize = 0x0000_0000_0000_0000u64 as usize;

pub const READ_WRITE_EXECUTE: usize = 0x0000_0000_0000_0002u64 as usize;

pub const PCID_ENABLE_MASK: usize = 0x8000_0000_0000_0000u64 as usize;

pub const NUM_CPUS: usize = 32;

pub const PAGE_ENTRY_PRESENT_SHIFT: u64 = 0;

pub const PAGE_ENTRY_WRITE_SHIFT: u64 = 1;

pub const PAGE_ENTRY_USER_SHIFT: u64 = 2;

pub const PAGE_ENTRY_PS_SHIFT: u64 = 7;

pub const PAGE_ENTRY_KERNEL_PRESENT_SHIFT: u64 = 52;

pub const PAGE_ENTRY_EXECUTE_SHIFT: u64 = 63;

pub const PAGE_ENTRY_PRESENT_MASK: u64 = 0x1;

pub const PAGE_ENTRY_WRITE_MASK: u64 = 0x1u64 << PAGE_ENTRY_WRITE_SHIFT;

pub const PAGE_ENTRY_USER_MASK: u64 = 0x1u64 << PAGE_ENTRY_USER_SHIFT;

pub const PAGE_ENTRY_PS_MASK: u64 = 0x1u64 << PAGE_ENTRY_PS_SHIFT;

pub const PAGE_ENTRY_EXECUTE_MASK: u64 = 0x1u64 << PAGE_ENTRY_EXECUTE_SHIFT;

pub const PAGE_ENTRY_KERNEL_PRESENT_MASK: u64 = 0x1u64 << PAGE_ENTRY_KERNEL_PRESENT_SHIFT;

pub const CONTAINER_PROC_LIST_LEN: usize = 10;

pub const CONTAINER_CHILD_LIST_LEN: usize = 10;

pub const PROC_CHILD_LIST_LEN: usize = 10;

pub const CONTAINER_ENDPOINT_LIST_LEN: usize = 10;

pub const MAX_CONTAINER_SCHEDULER_LEN: usize = 10;

// -------------------- End of Const --------------------

}