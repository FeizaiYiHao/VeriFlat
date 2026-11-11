//! Port of Atmosphere's user-level NVMe driver (`nvme_driver/src/lib.rs`) and of its benchmark to dom0.
//!
//! The driver files keep Atmosphere's split: `cmd`, `device`, `queue`, `regs`, and `nvme_test` (the
//! statically linked benchmark); `dma` is libdma (`Dma`, `NvmeCommand`, `NvmeCompletion`),
//! `ring_buffer` the shared-memory ring, `time` libtime, `pci` the `PciBarAddr` of pcid, and `client`
//! dom0's `nvme_client` with the two-process configurations. Every "physical address" is the virtual
//! address: each process maps its DMA memory into its own IOMMU table at IOVA = VA (`heap`).

pub mod client;
pub mod cmd;
pub mod device;
pub mod dma;
pub mod nvme_test;
pub mod pci;
mod queue;
mod regs;
pub mod ring_buffer;
pub mod time;

pub(crate) use log::info as println;

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum BlockOp {
    Read,
    Write,
}

#[derive(Debug, Clone, Copy)]
pub struct BlockReq {
    pub block: u64,
    pub num_blocks: u16,
    pub data: usize,
    pub op: BlockOp,
}

impl BlockReq {
    pub fn new(block: u64, num_blocks: u16, data: usize, op: BlockOp) -> BlockReq {
        BlockReq { block, num_blocks, data, op }
    }
}
