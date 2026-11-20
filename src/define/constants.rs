use vstd::prelude::*;
use super::super::*;
verus! {
// -------------------- Begin of Const --------------------
pub const MAX_NUM_ENDPOINT_DESCRIPTORS: usize = 32;

//1 for now
pub const KERNEL_MEM_END_L4INDEX: usize = 1;

//4GiB
pub const NUM_PAGES: usize = 1024 * 1024;
pub const PAGE_SZ_4K: usize = 1usize << 12;
pub const PAGE_SZ_2M: usize = 1usize << 21;
pub const PAGE_SZ_1G: usize = 1usize << 30;
/// One list-node slot carved off the tail of an object's page.
pub const NODE_SLOT_SZ: usize = 64;
pub const PAGE_SZ_4K_LESS_1_NODE_SLOT: usize = 4096 - NODE_SLOT_SZ;
pub const PAGE_SZ_4K_LESS_2_NODE_SLOTS: usize = 4096 - 2 * NODE_SLOT_SZ;
pub const PAGE_SZ_4K_LESS_3_NODE_SLOTS: usize = 4096 - 3 * NODE_SLOT_SZ;
/// The trap-frame slot of a thread page, right below its three node slots; the saved `Registers` end at the slot end.
pub const TRAP_FRAME_SLOT_SZ: usize = 192;
/// Size of the saved user registers, `Registers`.
pub const TRAP_FRAME_SZ: usize = 168;
pub const PAGE_SZ_4K_LESS_3_NODE_SLOTS_AND_TRAP_FRAME: usize = PAGE_SZ_4K_LESS_3_NODE_SLOTS - TRAP_FRAME_SLOT_SZ;
pub const PAGE_SZ_2M_LESS_1_NODE_SLOT: usize = 0x200000 - NODE_SLOT_SZ;
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
pub const NUM_CPUS: usize = 28;

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
/// Software bit 53 marks a leaf that maps device (IO) memory rather than system RAM.
pub const PAGE_ENTRY_IO_MASK: u64 = 1u64 << 53;
/// PCD and PWT, set with the IO bit so device memory is mapped uncached.
pub const PAGE_ENTRY_IO_CACHE_MASK: u64 = (1u64 << 4) | (1u64 << 3);
// Preset on present entries so hardware never performs the Accessed/Dirty read-modify-write on a page-table word the kernel's PointsTo claims.
pub const PAGE_ENTRY_ACCESSED_MASK: u64 = 0x1u64 << 5;
pub const PAGE_ENTRY_DIRTY_MASK: u64 = 0x1u64 << 6;
pub const MAX_CONTAINER_TREE_DEPTH: usize = 1024;

pub const PT_TYPE: PTType = true;
pub const IOMMU_TYPE: PTType = false;

pub const ALLOCATOR_MIN_WATERMARK: usize = 0;
pub const ALLOCATOR_MAX_WATERMARK: usize = 4096;
pub const ALLOCATOR_BATCH: usize = 64;
/// Per-CPU 2M cache bound that triggers draining: 4096 cached 2M pages would hold 8 GiB.
pub const ALLOCATOR_MAX_WATERMARK_2M: usize = 8;
pub const ALLOCATOR_BATCH_2M: usize = 4;

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

// The node-slot region sizes are spelled with literal page sizes so the verifier sees their values.
const _: () = assert!(PAGE_SZ_4K == 4096 && PAGE_SZ_2M == 0x200000);
