//! Bootloader integration.
//!
//! We are loaded by the boot manager which implements Xen PVH and Multiboot v2.

pub mod ap_start;
pub mod command_line;

use core::arch::asm;

use astd::boot::BootInfo;
use x86::io::{outb, outl, outw};

pub use command_line::get_command_line;

static mut BOOT_INFO: BootInfo = BootInfo::empty();

/// Global Tagged TLB toggle.
pub static mut PCIDE: u64 = 0;

/// The QEMU `isa-debug-exit` port (`-device isa-debug-exit,iobase=0xf4,iosize=0x04`).
const QEMU_DEBUG_EXIT_PORT: u16 = 0xf4;

pub unsafe fn init(boot_info: *const BootInfo) {
    BOOT_INFO = (&*boot_info).clone();
    PCIDE = if BOOT_INFO.pcide { 1 } else { 0 };

    command_line::init(BOOT_INFO.command_line.as_str()).expect("Invalid kernel command-line");
}

pub fn get_boot_info() -> &'static BootInfo {
    unsafe { &BOOT_INFO }
}

/// How much of the zeroed boot stack CPU 0 has touched: the first non-zero byte above its base
/// bounds the deepest frame. Only meaningful while CPU 0 still runs on that stack.
pub fn boot_stack_high_water() -> usize {
    let info = get_boot_info();
    let size = info.kernel_stack_size as usize;
    let stack = unsafe { core::slice::from_raw_parts(info.kernel_stack_base as *const u8, size) };
    size - stack.iter().position(|b| *b != 0).unwrap_or(size)
}

/// Returns the raw kernel command line.
pub fn get_raw_command_line() -> &'static str {
    unsafe { BOOT_INFO.command_line.as_str() }
}

/// Exits QEMU with status `(code << 1) | 1`.
pub unsafe fn exit_qemu(code: u32) -> ! {
    use core::sync::atomic::Ordering::Relaxed;
    use crate::platform::{NMI_FLUSHES, REMOTE_EVICTIONS, REMOTE_FLUSHES, WAKE_IPIS};
    let high_water = (0..crate::cpu::present_cpus()).map(crate::cpu::kernel_stack_high_water).max().unwrap_or(0);
    let (sysret, iret) = crate::cpu::restore_frame_exits();
    log::info!(
        "exit({}): kernel stack high-water {} KiB; remote flushes {} (served {}), remote evictions {}, wake IPIs {}; ring-3 returns: {} sysretq, {} iretq",
        code, high_water / 1024, REMOTE_FLUSHES.load(Relaxed), NMI_FLUSHES.load(Relaxed), REMOTE_EVICTIONS.load(Relaxed), WAKE_IPIS.load(Relaxed), sysret, iret,
    );
    outl(QEMU_DEBUG_EXIT_PORT, code);
    spin_forever();
}

/// Shutdown the system.
///
/// On virtual platforms it's possible to set an exit code to
/// be returned by the hypervisor.
pub unsafe fn shutdown(success: bool) -> ! {
    log::info!("The system is shutting down...");

    let cmdline = get_command_line();

    // QEMU isa-debug-exit
    //
    // <https://github.com/qemu/qemu/blob/bd662023e683850c085e98c8ff8297142c2dd9f2/hw/misc/debugexit.c>
    if let Some(io_base) = cmdline.qemu_debug_exit_io_base {
        if !success {
            log::debug!(
                "Trying QEMU isa-debug-exit shutdown (IO Port {:#x})",
                io_base
            );

            // QEMU will exit with (val << 1) | 1
            outw(io_base, 0x0);
        }
    }

    // Bochs APM
    if let Some(io_base) = cmdline.bochs_apm_io_base {
        let success_marker = if success {
            "BOCHS_SUCCESS"
        } else {
            "BOCHS_FAILURE"
        };
        log::debug!(
            "Trying Bochs APM shutdown (IO Port {:#x}) - {}",
            io_base,
            success_marker
        );

        let shutdown = "Shutdown";

        for ch in shutdown.chars() {
            outb(io_base, ch as u8);
        }
    }

    // QEMU
    outw(0x604, 0x2000);

    log::info!("It is now safe to turn off your computer"); // ;)

    spin_forever();
}

/// Enters a busy loop.
pub unsafe fn spin_forever() -> ! {
    loop {
        asm!("hlt");
    }
}
