//! The VeriFlat trap layer.
//!
//! This crate is the unverified platform glue around the verified kernel (`veriflat_monolith`,
//! compiled with ghost code erased): boot, GDT/IDT, the syscall entry, and the platform hooks.

#![no_std]
#![no_main]
#![allow(dead_code)]

mod boot;
mod console;
mod cpu;
mod debugger;
mod error;
mod gdt;
mod glue;
mod interrupt;
mod iommu;
mod logging;
mod platform;
mod ring_buffer;
mod smp;
mod syscalls;
mod utils;

use core::panic::PanicInfo;

use astd::boot::BootInfo;

/// CPU 0 entry point, called by aloader on the kernel stack.
#[unsafe(no_mangle)]
pub extern "C" fn _start(boot_info: *const BootInfo) -> ! {
    unsafe {
        console::early_init();
        logging::early_init();

        cpu::init_cpu(0);
        gdt::init_cpu();

        interrupt::init();
        interrupt::init_cpu();

        syscalls::init_cpu();

        boot::init(boot_info);
        logging::init();
    }

    log::info!("VeriFlat trap layer: command line {:?}", boot::get_raw_command_line());

    assert!(platform::has_invpcid(), "VeriFlat's remote TLB flush needs INVPCID");
    unsafe {
        glue::init_kernel(boot::get_boot_info());
        iommu::init(glue::iommu_root_table());
        cpu::mark_started(0);
        smp::start_aps();
        syscalls::enter_first_thread();
    }
}

/// The verified kernel links `alloc` but never allocates at runtime.
struct NoAlloc;

unsafe impl core::alloc::GlobalAlloc for NoAlloc {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        panic!("unexpected heap allocation of {} bytes", layout.size());
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: core::alloc::Layout) {}
}

#[global_allocator]
static ALLOCATOR: NoAlloc = NoAlloc;

/// The kernel panic handler.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("panic! {}", info);
    unsafe { boot::exit_qemu(4) }
}
