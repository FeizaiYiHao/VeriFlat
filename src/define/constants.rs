use vstd::prelude::*;
use super::super::*;
verus! {
// -------------------- Begin of Const --------------------
pub const MAX_NUM_ENDPOINT_DESCRIPTORS: usize = 128;

//1 for now
pub const KERNEL_MEM_END_L4INDEX: usize = 1;

//1GiB
pub const NUM_PAGES: usize = 256 * 1024;
pub const PAGE_SZ_4K: usize = 1usize << 12;
pub const PAGE_SZ_2M: usize = 1usize << 21;
pub const PAGE_SZ_1G: usize = 1usize << 30;
pub const PCID_MAX: usize = 4096;
pub const KERNEL_DEFAULT_PCID: Pcid = 0;

pub open spec fn pcid_valid(pcid: Pcid) -> bool { 0 <= pcid < PCID_MAX }
pub open spec fn usize_in_range<const RANGE: usize>(value: usize) -> bool { 0 <= value < RANGE }
pub open spec fn index_valid(range: usize, index: usize) -> bool { 0 <= index < range }

pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;
pub const MEM_4K_MASK: u64 = 0x0000_ffff_ffff_f000;
pub const MEM_2M_MASK: u64 = 0x0000_ffff_ffe0_0000;
pub const MEM_1G_MASK: u64 = 0x0000_ffff_c000_0000;
pub const PCID_ENABLE_MASK: usize = 0x8000_0000_0000_0000u64 as usize;
pub const NUM_CPUS: usize = 32;

pub open spec fn edp_idx_valid(edp_idx: EndpointIdx) -> bool { 0 <= edp_idx < MAX_NUM_ENDPOINT_DESCRIPTORS }

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
pub const MAX_CONTAINER_TREE_DEPTH: usize = 1024;

pub const PT_TYPE: PTType = true;
pub const IOMMU_TYPE: PTType = false;

pub const ALLOCATOR_MIN_WATERMARK: usize = 0;
pub const ALLOCATOR_MAX_WATERMARK: usize = 256;
pub const ALLOCATOR_BATCH: usize = 64;

pub const NO_KILL_STATE: bool = false;
pub const HAS_KILL_STATE: bool = true;

pub const PAGE_TABLE_HAS_KILL_STATE: bool = NO_KILL_STATE;
pub const CPU_HAS_KILL_STATE: bool = HAS_KILL_STATE;

pub const CONTAINER_HAS_KILL_STATE: bool = HAS_KILL_STATE;
pub const PCID_ALLOCATOR_HAS_KILL_STATE: bool = NO_KILL_STATE;
pub const CPU_SET_HAS_KILL_STATE: bool = HAS_KILL_STATE;
pub const PROCESS_HAS_KILL_STATE: bool = HAS_KILL_STATE;
pub const THREAD_HAS_KILL_STATE: bool = HAS_KILL_STATE;
pub const ENDPOINT_HAS_KILL_STATE: bool = NO_KILL_STATE;
// -------------------- End of Const --------------------
}
