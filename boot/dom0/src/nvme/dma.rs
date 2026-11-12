//! Port of Atmosphere's libdma (`dma.rs`, `allocator.rs`, `nvme.rs`). A `Dma<T>` is a box from the
//! process's heap, which maps every page into the process's IOMMU table at IOVA = VA, so `physical()`
//! is the virtual address, as in Atmosphere. `zeroed` builds the box in place instead of moving a
//! zeroed `T` through the stack.

use alloc::boxed::Box;
use core::ops::{Deref, DerefMut};

pub struct Dma<T> {
    value: Box<T>,
}

impl<T> Dma<T> {
    pub unsafe fn zeroed() -> Result<Dma<T>, i32> {
        Ok(Dma { value: unsafe { Box::<T>::new_zeroed().assume_init() } })
    }

    pub fn physical(&self) -> usize {
        let tr: &T = &self.value;
        tr as *const _ as usize
    }
}

impl<T> Deref for Dma<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T> DerefMut for Dma<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

pub trait DmaAllocator
where
    Self: Sized,
{
    fn allocate() -> Result<Dma<Self>, i32>;
}

macro_rules! zeroed_allocator {
    ($t: ty) => {
        impl DmaAllocator for $t {
            fn allocate() -> Result<Dma<Self>, i32> {
                unsafe { Dma::zeroed() }
            }
        }
    };
}

#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct NvmeCompletion {
    command_specific: u32,
    _rsvd: u32,
    pub sq_head: u16,
    pub sq_id: u16,
    pub cid: u16,
    pub status: u16,
}

impl NvmeCompletion {
    /// Dword 0, the command-specific result.
    pub fn command_specific(&self) -> u32 {
        self.command_specific
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct NvmeCommand {
    /// Opcode
    pub opcode: u8,
    /// Flags
    pub flags: u8,
    /// Command ID
    pub cid: u16,
    /// Namespace identifier
    pub nsid: u32,
    /// Reserved
    pub _rsvd: u64,
    /// Metadata pointer
    pub mptr: u64,
    /// Data pointer
    pub dptr: [u64; 2],
    /// Command dword 10
    pub cdw10: u32,
    /// Command dword 11
    pub cdw11: u32,
    /// Command dword 12
    pub cdw12: u32,
    /// Command dword 13
    pub cdw13: u32,
    /// Command dword 14
    pub cdw14: u32,
    /// Command dword 15
    pub cdw15: u32,
}

zeroed_allocator!([NvmeCommand; 1024]);
zeroed_allocator!([NvmeCompletion; 1024]);
zeroed_allocator!([u8; 4096]);
zeroed_allocator!([u32; 1024]);

pub fn allocate_dma<T>() -> Result<Dma<T>, i32>
where
    T: DmaAllocator,
{
    T::allocate()
}
