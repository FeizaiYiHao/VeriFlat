//! NVMe discovery over `sys_pci_info` and the BAR address type (Atmosphere's `pcid::utils::PciBarAddr`).

use vsys::{sys_pci_info, PCI_BAR_WINDOW_BASE};

/// PCI class and subclass of an NVMe controller (mass storage, non-volatile memory).
const CLASS_STORAGE: usize = 0x01;
const SUBCLASS_NVME: usize = 0x08;

#[derive(Clone, Copy, Debug)]
pub struct PciBarAddr {
    base: u64,
    #[allow(dead_code)]
    size: usize,
}

impl PciBarAddr {
    pub fn new(base: u64, size: usize) -> PciBarAddr {
        PciBarAddr { base, size }
    }

    pub fn get_base(&self) -> u64 {
        self.base
    }
}

/// An NVMe function the loader recorded.
#[derive(Clone, Copy, Debug)]
pub struct NvmeFunction {
    pub bus: usize,
    pub dev: usize,
    pub fun: usize,
    pub vendor: usize,
    pub device: usize,
    /// BAR0 physical base and page count.
    pub bar_phys: usize,
    pub bar_pages: usize,
}

impl NvmeFunction {
    /// Where every process of the benchmark maps BAR0: dom0's loader window, and the same address
    /// in the driver process that receives the pages.
    pub fn bar_va(&self) -> usize {
        PCI_BAR_WINDOW_BASE + self.bar_phys
    }

    pub fn bar(&self) -> PciBarAddr {
        PciBarAddr::new(self.bar_va() as u64, self.bar_pages * 4096)
    }
}

/// The recorded NVMe function with the lowest B/D/F, on any bus.
pub fn find_nvme() -> Option<NvmeFunction> {
    for bus in 0..256 {
        for dev in 0..32 {
            for fun in 0..8 {
                let (rax, base, pages) = unsafe { sys_pci_info(bus, dev, fun) };
                if rax < 0 {
                    continue;
                }
                let id = rax as usize;
                if (id >> 48) & 0xff == CLASS_STORAGE && (id >> 40) & 0xff == SUBCLASS_NVME {
                    return Some(NvmeFunction { bus, dev, fun, vendor: (id >> 16) & 0xffff, device: id & 0xffff, bar_phys: base, bar_pages: pages });
                }
            }
        }
    }
    None
}
