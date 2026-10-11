//! Xen x86/HVM direct boot ABI.
//!
//! More info: <https://xenbits.xen.org/docs/4.9-testing/misc/hvmlite.html>

use core::iter::Iterator;
use core::ptr;

use num_traits::FromPrimitive;

use super::StartInfo;
use crate::memory::{AcpiMemoryType, MemoryRange};

pub const HVM_START_INFO_MAGIC: u32 = 0x336ec578;

/// The Xen x86/HVM start info structure.
///
/// <https://patchwork.kernel.org/project/qemu-devel/patch/1547554687-12687-4-git-send-email-liam.merwick@oracle.com>
#[repr(C)]
#[derive(Debug)]
pub struct HvmStartInfo {
    /// Contains the magic value 0x336ec578.
    magic: u32,

    /// Version of this structure.
    version: u32,

    /// Flags.
    flags: u32,

    /// Number of modules.
    nr_modules: u32,

    /// Physical address of an array of `ModlistEntry`.
    modlist_paddr: u64,

    /// Physical address of the command line.
    cmdline_paddr: u64,

    /// Physical address of the RSDP ACPI data structure.
    rdsp_paddr: u64,

    /// Physical address of an array of `MemmapTableEntry`.
    memmap_paddr: u64,

    /// Number of entries in the memmap table.
    memmap_entries: u32,

    _reserved: u32,
}

/// A entry in the physical memory table.
#[repr(C)]
#[derive(Debug)]
pub struct MemmapTableEntry {
    /// Base address of the memory region.
    addr: u64,

    /// Size of the memory region in bytes.
    size: u64,

    /// Mapping type.
    map_type: u32,

    _reserved: u32,
}

/// A entry in the module list.
#[repr(C)]
#[derive(Debug)]
pub struct ModlistEntry {
    /// Physical address of the module.
    pub paddr: u64,

    /// Size of the module in bytes.
    pub size: u64,

    /// Physical address of the command line.
    cmdline_paddr: u64,

    _reserved: u64,
}

/// An iterator over the physical memory region table.
pub struct MemmapTableIterator<'si> {
    start_info: &'si HvmStartInfo,
    index: usize,
    done: bool,
}

/// An iterator over the module list.
pub struct ModlistIterator<'si> {
    start_info: &'si HvmStartInfo,
    index: usize,
}

impl StartInfo for HvmStartInfo {
    fn iter_memory_regions(
        &self,
    ) -> impl Iterator<Item = (MemoryRange, Option<AcpiMemoryType>)> + '_ {
        self.iter_raw_memmap()
            .map(|entry| (MemoryRange::new(entry.addr, entry.size), entry.map_type()))
    }

    fn iter_modlist(&self) -> impl Iterator<Item = MemoryRange> + '_ {
        self.iter_raw_modlist()
            .map(|entry| entry.to_memory_range())
    }
}

impl HvmStartInfo {
    pub unsafe fn load(start_info_ptr: *const u8) -> Option<Self> {
        let start_info = ptr::read_unaligned(start_info_ptr as *const HvmStartInfo);

        if start_info.validate() {
            Some(start_info)
        } else {
            None
        }
    }

    /// Creates an iterator through the module list entries.
    fn iter_raw_modlist(&self) -> ModlistIterator {
        ModlistIterator {
            start_info: self,
            index: 0,
        }
    }

    /// Validates the start info data structure.
    fn validate(&self) -> bool {
        0x336ec578 == self.magic
    }

    /// Creates an iterator through the physical memory map entries.
    fn iter_raw_memmap(&self) -> MemmapTableIterator {
        MemmapTableIterator {
            start_info: self,
            index: 0,
            done: false,
        }
    }
}

impl MemmapTableEntry {
    pub fn map_type(&self) -> Option<AcpiMemoryType> {
        FromPrimitive::from_u32(self.map_type)
    }
}

impl ModlistEntry {
    pub fn to_memory_range(&self) -> MemoryRange {
        MemoryRange::new(self.paddr, self.size)
    }
}

impl<'si> Iterator for MemmapTableIterator<'si> {
    type Item = MemmapTableEntry;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done || self.index >= self.start_info.memmap_entries as usize {
            return None;
        }

        // FIXME: Correct abstraction for P->V conversion
        // For now everything is identity mapped.
        let base = self.start_info.memmap_paddr as *const MemmapTableEntry;
        let entry_ptr = unsafe { base.add(self.index) };
        let entry = unsafe { ptr::read_unaligned(entry_ptr) };

        if entry.map_type == 0 {
            // End of the memory map array
            self.done = true;
            None
        } else {
            // Valid entry
            self.index += 1;
            Some(entry)
        }
    }
}

impl<'si> Iterator for ModlistIterator<'si> {
    type Item = ModlistEntry;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.start_info.nr_modules as usize {
            return None;
        }

        // FIXME: Correct abstraction for P->V conversion
        // For now everything is identity mapped.
        let base = self.start_info.modlist_paddr as *const ModlistEntry;
        let entry_ptr = unsafe { base.add(self.index) };
        let entry = unsafe { ptr::read_unaligned(entry_ptr) };

        self.index += 1;
        Some(entry)
    }
}
