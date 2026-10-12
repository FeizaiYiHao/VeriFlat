//! Boot manager handoff.

use core::ffi::c_void;
use core::ptr;

use crate::heapless::Vec as ArrayVec;
use crate::string::ArrayString;

/// The number of 4K pages the kernel manages. Must equal `veriflat_monolith::NUM_PAGES`;
/// the kernel asserts this at build time.
pub const MAX_PAGES: usize = 256 * 1024;

/// The most processors the loader reports. Must equal `veriflat_monolith::NUM_CPUS`.
pub const MAX_CPUS: usize = 32;

/// The most VT-d remapping units (DMAR DRHD entries) the loader reports.
pub const MAX_IOMMU_UNITS: usize = 8;

/// The type of physical memory.
///
/// This is a simplified version of `BootMemoryType` in aloader.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum PhysicalMemoryType {
    /// Used by the kernel.
    Kernel,

    /// Used by page tables.
    PageTable,

    /// Used by a domain.
    Domain,

    /// Available to be allocated.
    Available,

    /// Reserved for other use.
    Reserved,
}

/// Boot manager handoff information.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct BootInfo {
    /// The kernel command line.
    pub command_line: ArrayString<4096>,

    /// The kernel (default) page table: identity map of physical memory only.
    pub pml4: *const c_void,

    /// The dom0 page table: the same identity map plus the dom0 user mappings.
    pub dom0_pml4: *const c_void,

    /// The initial domain.
    pub dom0: Option<DomainMapping>,

    /// The payload mapped into dom0.
    pub payload: Option<Payload>,

    /// All physical pages and their state, indexed by page number.
    pub pages: ArrayVec<(u64, PhysicalMemoryType), MAX_PAGES>,

    /// Whether Tagged TLB is enabled.
    pub pcide: bool,

    /// Register bases of every VT-d remapping unit, in DMAR order. Together they cover every PCI
    /// function of segment 0; the kernel points each at the same root table.
    pub iommu_units: ArrayVec<u64, MAX_IOMMU_UNITS>,

    /// Local APIC IDs of the enabled processors, in ACPI MADT order.
    pub apic_ids: ArrayVec<u8, MAX_CPUS>,

    /// The PCI device the kernel's DMA self-test drives, if present.
    pub dma_test_device: Option<DmaTestDevice>,

    /// Base of the zeroed stack CPU 0 runs the kernel's initialization on; the kernel reports how
    /// much of it was used so the loader's reservation can be sized.
    pub kernel_stack_base: u64,

    /// Size of that stack in bytes.
    pub kernel_stack_size: u64,
}

/// A PCI function that can issue DMA on request (QEMU `edu`), with its first BAR identity mapped.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct DmaTestDevice {
    /// `(bus << 8) | (device << 3) | function`.
    pub bdf: u16,

    /// Physical (= kernel virtual) base of BAR0.
    pub mmio: u64,
}

/// A loaded domain.
///
/// The loader only loads and relocates the ELF in identity-mapped memory.
/// The kernel is responsible for setting up everything else.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct DomainMapping {
    /// The beginning of the contiguous reserved space (physical).
    pub reserved_start: *mut u8,

    /// The size of the reserved space.
    pub reserved_size: usize,

    /// The beginning of the virtual address.
    pub virt_start: *mut u8,

    /// The load bias of the domain.
    ///
    /// load_addr = load_bias + vaddr
    pub load_bias: usize,

    /// The entry point.
    pub entry_point: *const c_void,
}

/// A payload.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct Payload {
    /// The beginning of the binary in virtual memory.
    pub base: *mut u8,

    /// The size of the binary.
    pub size: usize,
}

impl BootInfo {
    /// Creates an empty BootInfo struct.
    pub const fn empty() -> Self {
        Self {
            command_line: ArrayString::empty(),
            dom0: None,
            payload: None,
            pml4: ptr::null(),
            dom0_pml4: ptr::null(),
            pages: ArrayVec::new(),
            pcide: false,
            iommu_units: ArrayVec::new(),
            apic_ids: ArrayVec::new(),
            dma_test_device: None,
            kernel_stack_base: 0,
            kernel_stack_size: 0,
        }
    }
}
