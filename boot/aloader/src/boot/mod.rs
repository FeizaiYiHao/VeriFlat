//! Boot loader integration.

mod hvm;
mod multiboot2;

use core::ptr;

use crate::memory::init_physical_memory_map;
use crate::memory::{AcpiMemoryType, MemoryRange};
use astd::string::ArrayString;
use astd::sync::Mutex;

/// The kernel image passed by the bootloader.
static KERNEL_IMAGE: Mutex<Option<MemoryRange>> = Mutex::new(None);

/// The `serial=`, `ramlog=` and `reset_after=` options of the boot command line, which the loader passes on as the
/// kernel's command line.
static KERNEL_OPTIONS: Mutex<astd::heapless::String<256>> = Mutex::new(astd::heapless::String::new());

/// A copy of the RSDP the bootloader passed, if any, made before the loader's allocator can reuse the boot information.
static RSDP: Mutex<Option<[u8; 36]>> = Mutex::new(None);

#[cfg(not(test))]
//#[link(name = "crt0")]
extern "C" {
    static bootinfo: u64;
    static __loader_start: u8;
    static __loader_end: u8;
    static stack_bottom: u8;
    static stack_top: u8;
    static p3_table: u8;
    static ramlog_p2: u8;
}

#[cfg(test)]
static mut bootinfo: u64 = 0;

#[cfg(test)]
static mut __loader_start: u8 = 0;

#[cfg(test)]
static mut __loader_end: u8 = 0;

/// A type of bootloader.
#[derive(Debug)]
enum Bootloader {
    /// Multiboot 2.
    Multiboot2,

    /// Xen x86/HVM direct boot ABI.
    Hvm,
}

trait StartInfo {
    /// The boot command line; empty when the bootloader passes none.
    fn command_line(&self) -> &str {
        ""
    }

    /// The bytes of the ACPI RSDP that the bootloader passes, as a copy in its boot information or as the firmware's own; `None` when it passes none.
    fn rsdp(&self) -> Option<&[u8]> {
        None
    }

    /// Creates an iterator through all memory regions.
    fn iter_memory_regions(
        &self,
    ) -> impl Iterator<Item = (MemoryRange, Option<AcpiMemoryType>)> + '_;

    /// Creates an iterator through the module list entries.
    fn iter_modlist(&self) -> impl Iterator<Item = MemoryRange> + '_;

    /// Dumps the physical memory map to the log.
    fn dump_memmap(&self) {
        log::info!("Physical memory map:");
        for (region, ty) in self.iter_memory_regions() {
            log::info!(
                "[mem {:#016x}-{:#016x}] {:?}",
                region.base(),
                region.end_inclusive(),
                ty.unwrap(),
            );
        }
    }

    /// Dumps the module list to the log.
    fn dump_modlist(&self) {
        log::info!("Module list:");
        for module in self.iter_modlist() {
            log::info!(
                "[mod {:#016x}-{:#016x}] ({} bytes)",
                module.base(),
                module.end_inclusive(),
                module.size(),
            );
        }
    }
}

/// The size of the loader's own stack (`crt0.asm`).
pub fn loader_stack_size() -> usize {
    unsafe { &stack_top as *const u8 as usize - &stack_bottom as *const u8 as usize }
}

/// How much of the loader's stack has been touched: it lies in .bss, so the first non-zero byte
/// above the bottom bounds the deepest frame.
pub fn loader_stack_high_water() -> usize {
    let size = loader_stack_size();
    let stack = unsafe { core::slice::from_raw_parts(&stack_bottom as *const u8, size) };
    size - stack.iter().position(|b| *b != 0).unwrap_or(size)
}

/// Returns the range of the loader itself.
pub fn get_loader_image_range() -> MemoryRange {
    let start = unsafe { &__loader_start as *const _ as u64 };
    let end_exclusive = unsafe { &__loader_end as *const _ as u64 };
    let size = end_exclusive - start;

    MemoryRange::new(start, size)
}

/// The kernel command line: the `serial=`, `ramlog=` and `reset_after=` options of the boot command line, or empty.
pub fn get_kernel_command_line() -> ArrayString<4096> {
    ArrayString::new(KERNEL_OPTIONS.lock().as_str()).unwrap_or(ArrayString::empty())
}

/// Maps the RAM log buffer at `addr` (checked by `ramlog::parse`) identity in crt0's page table with 2M pages:
/// kernel-only, writable, write-through and no-execute, under one new L2 table at the L3 entry of its 1 GiB region.
#[cfg(not(test))]
unsafe fn map_ramlog_in_loader_table(addr: usize) {
    let p3 = &raw const p3_table as *mut u64;
    let p2 = &raw const ramlog_p2 as *mut u64;
    for i in 0..ns16550a::ramlog::SIZE >> 21 {
        let page = addr + (i << 21);
        ptr::write_volatile(p2.add((page >> 21) & 511), page as u64 | 1 | 2 | 8 | 0x80 | 1 << 63);
    }
    ptr::write_volatile(p3.add((addr >> 30) & 511), p2 as u64 | 1 | 2);
    core::arch::asm!("mov {0}, cr3", "mov cr3, {0}", out(reg) _);
}

#[cfg(test)]
unsafe fn map_ramlog_in_loader_table(_addr: usize) {}

/// The physical address of the RSDP the bootloader passed (a copy in the loader's own memory), if any.
pub fn get_rsdp_address() -> Option<usize> {
    RSDP.lock().as_ref().map(|r| r.as_ptr() as usize)
}

/// Returns the range of the kernel image.
pub fn get_kernel_image_range() -> Option<MemoryRange> {
    KERNEL_IMAGE.lock().clone()
}

/// Initializes the boot loader information.
pub unsafe fn init() {
    let loader_range = get_loader_image_range();
    log::info!(
        "[ldr {:#016x}-{:#016x}]",
        loader_range.base(),
        loader_range.end_inclusive()
    );

    fn consume_start_info<S: StartInfo>(start_info: S) {
        log::info!("Boot command line {:?}", start_info.command_line());
        if let Some(option) = start_info.command_line().split_ascii_whitespace().find(|c| c.starts_with("serial=")) {
            let port = match option {
                "serial=com1" => 0x3f8,
                "serial=com2" => 0x2f8,
                "serial=com3" => 0x3e8,
                "serial=com4" => 0x2e8,
                _ => panic!("unknown boot option {:?}: serial= takes com1, com2, com3 or com4", option),
            };
            unsafe { crate::console::use_port(port) };
            log::info!("Console on {}", option);
        }
        if let Some(option) = start_info.command_line().split_ascii_whitespace().find(|c| c.starts_with("ramlog=")) {
            let addr = ns16550a::ramlog::parse(&option["ramlog=".len()..]).unwrap_or_else(|e| panic!("{}: {:?}", e, option));
            unsafe {
                map_ramlog_in_loader_table(addr);
                let _console = crate::console::get_writer();
                ns16550a::ramlog::start(addr);
            }
            log::info!("RAM log at {:#x}, {} bytes", addr, ns16550a::ramlog::SIZE);
        }
        for option in start_info.command_line().split_ascii_whitespace() {
            if ["serial=", "ramlog=", "reset_after="].iter().any(|p| option.starts_with(p)) {
                let mut options = KERNEL_OPTIONS.lock();
                let pushed = (options.is_empty() || options.push(' ').is_ok()) && options.push_str(option).is_ok();
                assert!(pushed, "boot options for the kernel are longer than 256 bytes");
            }
        }
        if let Some(rsdp) = start_info.rsdp() {
            let mut copy = [0; 36];
            let len = rsdp.len().min(copy.len());
            copy[..len].copy_from_slice(&rsdp[..len]);
            log::info!("RSDP from the bootloader ({} bytes, revision {})", rsdp.len(), copy[15]);
            *RSDP.lock() = Some(copy);
        }
        start_info.dump_memmap();
        start_info.dump_modlist();

        let regions = start_info
            .iter_memory_regions()
            .map(|(r, t)| (r, t.expect("Unknown memory type")));
        let loader_range = get_loader_image_range();
        let image_ranges = start_info
            .iter_modlist();

        init_physical_memory_map(regions, loader_range, image_ranges);

        if let Some(module) = start_info.iter_modlist().next() {
            let mut kernel_image = KERNEL_IMAGE.lock();
            *kernel_image = Some(module);
        };
    }

    let start_info_ptr = bootinfo as *const u8;
    match detect_bootloader() {
        Some(Bootloader::Hvm) => {
            log::info!("Booted via Xen x86/HVM");
            let start_info =
                unsafe { hvm::HvmStartInfo::load(start_info_ptr).expect("Invalid Xen x86/HVM start info") };
            consume_start_info(start_info);
        }
        Some(Bootloader::Multiboot2) => {
            log::info!("Booted via Multiboot2");
            let start_info =
                unsafe { multiboot2::Multiboot2StartInfo::load(start_info_ptr).expect("Invalid Multiboot2 start info") };
            consume_start_info(start_info);
        }
        _ => {
            panic!("Failed to detect bootloader, cannot continue");
        }
    }
}

fn detect_bootloader() -> Option<Bootloader> {
    let bootinfo_addr = unsafe { bootinfo };

    if bootinfo_addr == 0 {
        return None;
    }

    let magic4 = {
        let magic_ptr = bootinfo_addr as *const u32;
        unsafe { ptr::read_unaligned(magic_ptr) }
    };

    if magic4 == hvm::HVM_START_INFO_MAGIC {
        Some(Bootloader::Hvm)
    } else {
        Some(Bootloader::Multiboot2)
    }
}
