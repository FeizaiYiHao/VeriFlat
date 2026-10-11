//! The VeriFlat early loader (adapted from the Atmosphere loader).
//!
//! It builds two page tables that share the kernel identity map of the first
//! `MAX_PHYSICAL_MEMORY` bytes (L4[0]): the kernel (default) table and the dom0
//! table that additionally holds the dom0 user mappings under L4[1]. It loads
//! the kernel ELF and dom0 ELF from the concatenated `jumbo` module, reserves
//! the kernel stack, records every physical page's type, and calls the kernel
//! entry with `rdi = &BootInfo` on the kernel stack.

#![no_std]
#![no_main]
#![deny(
    asm_sub_register,
    deprecated,
    missing_abi,
    unused_macros,
    unused_must_use,
    unused_unsafe
)]
#![deny(clippy::from_over_into, clippy::needless_question_mark)]

pub mod acpi;
pub mod boot;
pub mod console;
pub mod debugger;
pub mod logging;
pub mod memory;
pub mod pci;

use core::arch::asm;
use core::panic::PanicInfo;
use core::slice;

use x86::cpuid::cpuid;

use aelf::ElfHandle;
use astd::boot::{BootInfo, DomainMapping, Payload, PhysicalMemoryType, MAX_PAGES};
use astd::io::{Cursor, Read, Seek, SeekFrom};
use astd::memory::{USERSPACE_BASE, USERSPACE_PAYLOAD_BASE};

use memory::{
    AddressSpace, BootMemoryType, PhysicalAllocator, UserspaceMapper, MAX_PHYSICAL_MEMORY, PAGE_SIZE,
};

/// Kernel image (`KernelK` lives in its .bss) + kernel stack.
const KERNEL_RESERVATION: usize = 320 * 1024 * 1024;
/// The kernel builds `KernelK` (~60 MiB) by value on this stack before moving it into place.
const KERNEL_STACK_SIZE: usize = 192 * 1024 * 1024;
const DOM0_RESERVATION: usize = 256 * 1024 * 1024; // 256 MiB
const DOM0_STACK_SIZE: u64 = 16 * 1024 * 1024;

/// MMIO pages the kernel needs identity mapped (not part of the page array).
const LAPIC_BASE: u64 = 0xFEE0_0000;
const IOAPIC_BASE: u64 = 0xFEC0_0000;

/// Loader entry point (called from `crt0.asm` in long mode).
#[no_mangle]
pub extern "C" fn main() -> ! {
    unsafe {
        console::init();
        logging::init();
    }

    log::info!("** VeriFlat Loader **");

    unsafe {
        boot::init();
        memory::init();
    }

    let bootstrap_allocator = memory::bootstrap_allocator();

    log::info!("Mapping physical memory 0..{:#x} with 4K pages", MAX_PHYSICAL_MEMORY);
    let mut kernel_space = AddressSpace::new(bootstrap_allocator);
    let mut cur = 0u64;
    while cur < MAX_PHYSICAL_MEMORY as u64 {
        unsafe {
            kernel_space.map(bootstrap_allocator, cur, cur, false, false, false);
        }
        cur += PAGE_SIZE as u64;
    }
    let iommu_base = acpi::probe_iommu();
    let dma_test_device = pci::probe_dma_test_device();
    unsafe {
        kernel_space.map(bootstrap_allocator, LAPIC_BASE, LAPIC_BASE, false, false, true);
        kernel_space.map(bootstrap_allocator, IOAPIC_BASE, IOAPIC_BASE, false, false, true);
        if let Some(base) = iommu_base {
            kernel_space.map(bootstrap_allocator, base, base, false, false, true);
        }
        if let Some(device) = dma_test_device {
            kernel_space.map(bootstrap_allocator, device.mmio, device.mmio, false, false, true);
        }
    }

    // Dom0 shares the kernel half (L4[0]) and gets its own user subtree.
    let mut dom0_space = AddressSpace::new(bootstrap_allocator);
    unsafe {
        dom0_space.share_l4_entry(&kernel_space, 0);
    }

    let mut boot_info = BootInfo::empty(); // stays on the loader stack
    boot_info.pcide = cpu_has_pcid();

    if boot_info.pcide {
        log::info!("Enabling Tagged TLB");
        unsafe {
            asm!(
                "mov {cr4}, cr4",
                "or {cr4}, {cr4_pcide}",
                "mov cr4, {cr4}",
                cr4 = out(reg) _,
                cr4_pcide = const (1 << 17),
            );
        }
    } else {
        // Kept bootable for emulators without PCID (QEMU TCG): the kernel faults at its first
        // PCID-tagged CR3 write, after the boot glue has run.
        log::warn!("CPU does not support PCID, which VeriFlat requires");
    }

    log::info!("Switching to PML4 @ {:x?}", kernel_space.pml4());
    unsafe {
        asm!(
            "mov cr3, {pml4}",
            pml4 = inout(reg) kernel_space.pml4() => _,
        );
    }

    boot_info.pml4 = kernel_space.pml4();
    boot_info.dom0_pml4 = dom0_space.pml4();
    boot_info.iommu_base = iommu_base;
    boot_info.dma_test_device = dma_test_device;
    boot_info.apic_ids = acpi::probe_cpus();
    log::info!("Processors (APIC IDs): {:?}", boot_info.apic_ids);

    let (jumbo_file, jumbo_size) = {
        let range = boot::get_kernel_image_range().expect("No kernel image was passed");

        let f = unsafe { slice::from_raw_parts(range.base() as *const _, range.size() as usize) };
        (Cursor::new(f), f.len())
    };

    let kernel_elf = ElfHandle::parse(jumbo_file, 4096).unwrap();
    let kernel_end = kernel_elf.elf_len();

    let (_, mut kernel_allocator) = memory::reserve(KERNEL_RESERVATION, BootMemoryType::Kernel);
    let (kernel_map, mut jumbo_file) = kernel_elf.load(&mut kernel_allocator).unwrap();

    let stack_base = unsafe { kernel_allocator.allocate_physical(KERNEL_STACK_SIZE).0 };
    log::info!(
        "Kernel loaded at {:#x} (bias {:#x}), stack {:#x}..{:#x}",
        kernel_map.load_addr,
        kernel_map.load_bias,
        stack_base,
        stack_base + KERNEL_STACK_SIZE as u64,
    );

    debugger::add_binary("kernel", kernel_map.load_bias);

    // Load dom0
    jumbo_file
        .seek(SeekFrom::Start(kernel_end as u64))
        .expect("Kernel file incomplete");

    match load_domain("dom0", jumbo_file, &mut dom0_space, bootstrap_allocator) {
        Ok(mut domain) => {
            boot_info.dom0 = Some(domain.mapping);

            // Copy payload as-is into dom0
            let payload_size = jumbo_size as u64 - domain.remaining_file.pos();
            if payload_size != 0 {
                log::info!("Loading payload ({})", payload_size);
                boot_info.payload = Some(Payload {
                    base: USERSPACE_PAYLOAD_BASE as *mut u8,
                    size: payload_size as usize,
                });

                let phys_base =
                    unsafe { domain.allocator.allocate_physical(payload_size as usize).0 };
                let virt_base = USERSPACE_PAYLOAD_BASE;
                let mut cur = virt_base;
                while cur < virt_base + payload_size {
                    unsafe {
                        let paddr = cur - virt_base + phys_base;
                        let page = slice::from_raw_parts_mut(paddr as *mut u8, PAGE_SIZE);

                        dom0_space.map(bootstrap_allocator, cur, paddr, true, false, false);

                        domain
                            .remaining_file
                            .read(page)
                            .expect("Failed to copy payload page");
                    }
                    cur += PAGE_SIZE as u64;
                }
            }
        }
        Err(e) => {
            log::warn!("No valid Dom0: {:?}", e);
        }
    }

    log::info!("Physical memory map after loading:");
    memory::dump_physical_memory_map();

    populate_pages(&mut boot_info);

    debugger::on_ready();

    log::info!("Calling into kernel @ {:x?}", kernel_map.entry_point);
    unsafe {
        asm!(
            // clear segment state
            "xor r15, r15",
            "mov ds, r15w",
            "mov fs, r15w",
            "mov gs, r15w",
            "mov ss, r15w",

            // rdi = &boot_info, rsp = kernel stack top
            "mov rsp, rsi",
            "xor rsi, rsi",

            "call rax",
            "ud2",

            in("rax") kernel_map.entry_point,
            in("rdi") &boot_info as *const _,
            in("rsi") stack_base + KERNEL_STACK_SIZE as u64,
            options(noreturn),
        );
    }
}

/// Records the type of every page below `MAX_PHYSICAL_MEMORY`, in page order.
fn populate_pages(boot_info: &mut BootInfo) {
    let mut free_page_count = 0usize;
    let mut cur = 0u64;
    let mut map = memory::get_physical_memory_map();
    map.sort();

    log::info!("Populating physical page list");
    for (region, label) in map.regions.iter() {
        let page_type: PhysicalMemoryType = (*label).into();
        log::info!("{:<60} {:?} -> {:?}", region, *label, page_type);

        while cur < region.base() && !boot_info.pages.is_full() {
            boot_info
                .pages
                .push((cur, PhysicalMemoryType::Reserved))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
        while cur < region.end_inclusive() && !boot_info.pages.is_full() {
            if page_type == PhysicalMemoryType::Available {
                free_page_count += 1;
            }
            boot_info
                .pages
                .push((cur, page_type))
                .expect("Too many pages");
            cur += PAGE_SIZE as u64;
        }
    }
    while !boot_info.pages.is_full() {
        boot_info
            .pages
            .push((cur, PhysicalMemoryType::Reserved))
            .expect("Too many pages");
        cur += PAGE_SIZE as u64;
    }
    assert_eq!(boot_info.pages.len(), MAX_PAGES);

    log::info!("{} of {} pages are free", free_page_count, MAX_PAGES);
}

struct Domain<F, A> {
    mapping: DomainMapping,
    remaining_file: F,
    allocator: A,
}

fn load_domain<F, A>(
    name: &'static str,
    mut elf: F,
    address_space: &mut AddressSpace,
    page_table_allocator: &mut A,
) -> Result<Domain<F, impl PhysicalAllocator>, aelf::Error>
where
    F: Read + Seek,
    F::Error: Into<aelf::Error>,
    A: PhysicalAllocator,
{
    let dom_start = elf.stream_position().unwrap() as usize;
    let parsed = ElfHandle::parse(elf, PAGE_SIZE)?;
    let dom_end = dom_start + parsed.elf_len();
    log::info!("Loading {}...", name);

    let (reserved_start, mut allocator) = memory::reserve(DOM0_RESERVATION, BootMemoryType::Domain);

    let mut userspace_mapper =
        UserspaceMapper::new(address_space, &mut allocator, page_table_allocator);
    let (dom_map, mut elf) = parsed
        .load(&mut userspace_mapper)
        .expect("Failed to map dom0");

    // Allocate and map the stack at the top of the reservation.
    let phys_base = unsafe { allocator.allocate_physical(DOM0_STACK_SIZE as usize).0 };
    let virt_base = USERSPACE_BASE + DOM0_RESERVATION as u64 - DOM0_STACK_SIZE;

    let mut cur = virt_base;
    while cur < virt_base + DOM0_STACK_SIZE {
        unsafe {
            address_space.map(
                page_table_allocator,
                cur,
                cur - virt_base + phys_base,
                true,
                false,
                false,
            );
        }
        cur += PAGE_SIZE as u64;
    }

    elf.seek(SeekFrom::Start(dom_end as u64))
        .expect("dom0 incomplete");

    log::debug!("{} end: {}", name, dom_end);

    debugger::add_binary(name, dom_map.load_bias);

    let mapping = DomainMapping {
        reserved_start,
        reserved_size: DOM0_RESERVATION,
        virt_start: USERSPACE_BASE as *mut u8,
        entry_point: dom_map.entry_point,
        load_bias: dom_map.load_bias,
    };

    Ok(Domain {
        mapping,
        remaining_file: elf,
        allocator,
    })
}

fn cpu_has_pcid() -> bool {
    let cpuid_1 = cpuid!(0x1);
    (cpuid_1.ecx & (1 << 17)) != 0
}

/// The loader panic handler.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("loader panic: {}", info);
    loop {
        unsafe { asm!("hlt") };
    }
}
