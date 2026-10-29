//! Serial console.
//!
//! Outputs from the kernel and applications are typically
//! done through [`log`] macros so verbosity can be controlled
//! as needed. `print!` and `println!` are intentionally
//! omitted from the kernel.
//!
//! The serial port defaults to COM1 (0x3F8), and can be
//! configured through the kernel command line:
//!
//! `serial=[com1|com2|com3|com4]`

use core::arch::asm;
use core::mem::ManuallyDrop;
use core::ops::{Deref, DerefMut};

use crate::boot;
use astd::sync::{Mutex, MutexGuard};
use ns16550a::PioSerial;

#[allow(dead_code)]
const COM1: usize = 0x3f8;
#[allow(dead_code)]
const COM2: usize = 0x2f8;

/// The serial device.
static SERIAL: Mutex<PioSerial> = Mutex::new(unsafe { PioSerial::new(COM1) });

/// RFLAGS.IF.
const RFLAGS_IF: u64 = 1 << 9;

/// The serial lock with interrupts off while it is held: kernel code logs with interrupts on, and
/// an interrupt handler that logs on the same CPU would otherwise spin on the lock it interrupted.
/// Dropping it unlocks, then turns interrupts back on only if they were on before.
pub struct WriterType {
    guard: ManuallyDrop<MutexGuard<'static, PioSerial>>,
    interrupts_were_on: bool,
}

impl Deref for WriterType {
    type Target = PioSerial;

    fn deref(&self) -> &PioSerial {
        &self.guard
    }
}

impl DerefMut for WriterType {
    fn deref_mut(&mut self) -> &mut PioSerial {
        &mut self.guard
    }
}

impl Drop for WriterType {
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::drop(&mut self.guard);
            if self.interrupts_were_on {
                asm!("sti", options(nostack, preserves_flags));
            }
        }
    }
}

/// Returns a writer that implements `core::fmt::Write`.
pub fn get_writer() -> WriterType {
    let rflags: u64;
    unsafe {
        asm!("pushfq", "pop {}", out(reg) rflags, options(nomem, preserves_flags));
        asm!("cli", options(nostack, preserves_flags));
    }
    WriterType { guard: ManuallyDrop::new(SERIAL.lock()), interrupts_were_on: rflags & RFLAGS_IF != 0 }
}

/// Initializes early logging.
pub unsafe fn early_init() {
    let serial = get_writer();
    serial.init();
}

/// Initializes the serial console.
pub unsafe fn init() {
    let mut serial = get_writer();
    let mut invalid_serial = false;

    let cmdline = boot::get_command_line();
    *serial = PioSerial::new(match cmdline.serial {
        "" | "com1" => 0x3f8,
        "com2" => 0x2f8,
        "com3" => 0x3e8,
        "com4" => 0x2e8,
        _ => {
            invalid_serial = true;
            0x3f8
        }
    });

    serial.init();
    if invalid_serial {
        log::error!(
            "Invalid serial port specified - Valid values for `serial` are: com1, com2, com3, com4"
        );
    }

    /*
    // Clear the screen and move the cursor to (0,0).
    //
    // In some terminals, [2J alone does not reset the cursor position.
    write!(serial, "\x1B[2J\x1B[0;0H").unwrap();
    */
}
