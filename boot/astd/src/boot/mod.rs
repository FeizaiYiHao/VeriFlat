//! Boot manager handoff.

use core::ffi::c_void;
use core::ptr;

use crate::heapless::Vec as ArrayVec;
use crate::string::ArrayString;

/// The number of 4K pages the kernel manages. Must equal `veriflat_monolith::NUM_PAGES`;
/// the kernel asserts this at build time.
pub const MAX_PAGES: usize = 1024 * 1024;

/// The most processors the loader reports. Must equal `veriflat_monolith::NUM_CPUS`.
pub const MAX_CPUS: usize = 28;

/// The most VT-d remapping units (DMAR DRHD entries) the loader reports; it panics on more. Sized for a two-socket
/// server (one unit per PCIe stack plus accelerator stacks per socket). What scales with it: `BootInfo.iommu_units`
/// (8 bytes each) and the kernel's `iommu::UNITS` (8 bytes each); the work per invalidation and the loader's one
/// mapped register page per unit follow the units present, not this bound. Boot-only: the verified kernel never sees it.
pub const MAX_IOMMU_UNITS: usize = 16;

/// The most PCI functions with a device BAR0 the loader records.
pub const MAX_PCI_DEVICES: usize = 16;

/// The most assigned memory BARs the loader reports; it panics on more rather than leave one out.
pub const MAX_BAR_SLOTS: usize = 1024;

/// The most firmware RAM ranges the loader reports; it panics on more.
pub const MAX_RAM_RANGES: usize = 256;

/// The most PCI ECAM (MMCONFIG) windows the loader reports.
pub const MAX_MMCONFIG_WINDOWS: usize = 8;

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

    /// The NVMe, Ethernet and `edu` functions whose BAR0 the loader enabled, in B/D/F order (`NR_PCI_INFO` reads them).
    pub pci_devices: ArrayVec<PciDevice, MAX_PCI_DEVICES>,

    /// Every assigned memory BAR of every PCI function (type 0 headers: 6 registers, type 1: 2; a 64-bit BAR takes
    /// two), in B/D/F and BAR order: the PCI table's BAR slots, in the order of the kernel's BAR table:
    /// slot `i` here is BAR-table index `i` of `map_pci_bar_4k/2m`. Nothing maps them at boot.
    pub bar_slots: ArrayVec<BarSlot, MAX_BAR_SLOTS>,

    /// The firmware memory map's RAM ranges as `(base, size)`, above 4 GiB too: usable, ACPI reclaim, ACPI NVS,
    /// unusable and disabled memory. No BAR may overlap one.
    pub ram_ranges: ArrayVec<(u64, u64), MAX_RAM_RANGES>,

    /// The PCI ECAM (MMCONFIG) windows of the MCFG table as `(base, size)`.
    pub mmconfig: ArrayVec<(u64, u64), MAX_MMCONFIG_WINDOWS>,

    /// The DMAR host address width in bits (HAW + 1): the physical addresses the VT-d units can reach.
    pub iommu_address_width: u8,

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

/// A PCI function whose memory BAR0 the loader enabled.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct PciDevice {
    /// `(bus << 8) | (device << 3) | function`.
    pub bdf: u16,
    /// PCI vendor ID.
    pub vendor: u16,
    /// PCI device ID.
    pub device: u16,
    /// PCI base class code.
    pub class: u8,
    /// PCI subclass code.
    pub subclass: u8,
    /// Physical base of BAR0.
    pub bar0_base: u64,
    /// Number of 4K pages of BAR0's page envelope.
    pub bar0_pages: u64,
}

/// One assigned memory BAR: a BAR slot of the PCI table, keyed by `(bdf, bar)`, with its exact byte range.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct BarSlot {
    /// `(bus << 8) | (device << 3) | function`.
    pub bdf: u16,
    /// BAR register index, 0 to 5; a 64-bit BAR is keyed by its low register.
    pub bar: u8,
    /// PCI vendor ID of the function.
    pub vendor: u16,
    /// PCI device ID of the function.
    pub device: u16,
    /// Physical base: the BAR register's address bits.
    pub base: u64,
    /// Size in bytes, a power of two.
    pub size: u64,
}

impl BarSlot {
    /// The slot's outward-rounded 4K page envelope as `(first page, end)`; `None` when `base + size` overflows.
    pub fn envelope(&self) -> Option<(u64, u64)> {
        let end = self.base.checked_add(self.size)?.checked_add(0xfff)? & !0xfff;
        Some((self.base & !0xfff, end))
    }
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
            pci_devices: ArrayVec::new(),
            bar_slots: ArrayVec::new(),
            ram_ranges: ArrayVec::new(),
            mmconfig: ArrayVec::new(),
            iommu_address_width: 0,
            kernel_stack_base: 0,
            kernel_stack_size: 0,
        }
    }
}
