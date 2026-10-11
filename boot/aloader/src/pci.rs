//! PCI configuration space access (legacy 0xCF8/0xCFC mechanism) for the DMA test device.

use astd::boot::DmaTestDevice;
use x86::io::{inl, outl};

const CONFIG_ADDRESS: u16 = 0xCF8;
const CONFIG_DATA: u16 = 0xCFC;

/// QEMU's `edu` educational device.
const EDU_VENDOR_DEVICE: u32 = 0x11e8_1234;

const COMMAND: u8 = 0x04;
const BAR0: u8 = 0x10;
const COMMAND_MEMORY: u32 = 1 << 1;
const COMMAND_BUS_MASTER: u32 = 1 << 2;

fn config_address(bus: u8, device: u8, function: u8, offset: u8) -> u32 {
    (1 << 31) | ((bus as u32) << 16) | ((device as u32) << 11) | ((function as u32) << 8) | (offset as u32 & 0xfc)
}

unsafe fn read(bus: u8, device: u8, function: u8, offset: u8) -> u32 {
    outl(CONFIG_ADDRESS, config_address(bus, device, function, offset));
    inl(CONFIG_DATA)
}

unsafe fn write(bus: u8, device: u8, function: u8, offset: u8, value: u32) {
    outl(CONFIG_ADDRESS, config_address(bus, device, function, offset));
    outl(CONFIG_DATA, value);
}

/// Finds an `edu` device on bus 0, enables its memory decoding and bus mastering, and returns
/// its B/D/F and BAR0. Test-only: the kernel uses it to issue DMA through the IOMMU.
pub fn probe_dma_test_device() -> Option<DmaTestDevice> {
    for device in 0..32u8 {
        for function in 0..8u8 {
            if unsafe { read(0, device, function, 0) } != EDU_VENDOR_DEVICE {
                continue;
            }
            let mmio = unsafe { read(0, device, function, BAR0) } as u64 & !0xf;
            unsafe {
                let command = read(0, device, function, COMMAND) & 0xffff;
                write(0, device, function, COMMAND, command | COMMAND_MEMORY | COMMAND_BUS_MASTER);
            }
            let bdf = ((device as u16) << 3) | function as u16;
            log::info!("DMA test device 00:{:02x}.{} BAR0 {:#x}", device, function, mmio);
            return Some(DmaTestDevice { bdf, mmio });
        }
    }
    None
}
