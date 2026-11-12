//! A copy of the console output in a RAM buffer that survives a warm reset, for machines whose serial console
//! nobody reads (boot option `ramlog=<hex physical address>`).
//!
//! The buffer is [`SIZE`] bytes, identity mapped by the loader. Its first [`HEADER_SIZE`] bytes are the header, all
//! little-endian: the magic `VFRAMLOG` at 0, the version (u32) at 8, the header size (u32) at 12, the capacity of the
//! text area (u64) at 16, the bytes written so far (u64) at 24, the exit reason (u32, `REASON_*`) at 32 and the exit
//! code (u32) at 36. The console text follows the header. `boot/tools/ramlog_read.py` reads it back.
//!
//! The loader writes the header ([`start`]); the kernel continues at the header's count ([`attach`]). Every console
//! byte goes through [`put`] under the console lock; bytes past the capacity are dropped.

use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};

pub const MAGIC: [u8; 8] = *b"VFRAMLOG";
pub const VERSION: u32 = 1;
pub const SIZE: usize = 16 * 1024 * 1024;
pub const HEADER_SIZE: usize = 4096;

pub const REASON_RUNNING: u32 = 0;
pub const REASON_EXIT: u32 = 1;
pub const REASON_KERNEL_PANIC: u32 = 2;
pub const REASON_LOADER_PANIC: u32 = 3;
pub const REASON_FATAL_EXCEPTION: u32 = 4;
pub const REASON_TIMEOUT: u32 = 5;

const OFF_VERSION: usize = 8;
const OFF_HEADER_SIZE: usize = 12;
const OFF_CAPACITY: usize = 16;
const OFF_WRITTEN: usize = 24;
const OFF_REASON: usize = 32;
const OFF_CODE: usize = 36;

/// The buffer's address once it is active, else 0.
static BASE: AtomicUsize = AtomicUsize::new(0);

/// Console bytes written before the buffer became active; [`start`] and [`attach`] copy them in.
static mut EARLY: [u8; 2048] = [0; 2048];
static EARLY_LEN: AtomicUsize = AtomicUsize::new(0);

/// Parses the value of `ramlog=`: a hexadecimal physical address, with or without `0x`, at or above 4 GiB,
/// 2 MiB aligned, with the whole buffer inside one 1 GiB region below 512 GiB (one L3 entry of the identity map).
pub fn parse(value: &str) -> Result<usize, &'static str> {
    let digits = value.strip_prefix("0x").unwrap_or(value);
    let addr = usize::from_str_radix(digits, 16).map_err(|_| "ramlog= takes a hexadecimal physical address")?;
    if addr < 1 << 32 || addr % (2 << 20) != 0 {
        return Err("ramlog= must be at or above 4 GiB and 2 MiB aligned");
    }
    if addr >> 30 != (addr + SIZE - 1) >> 30 || addr + SIZE > 1 << 39 {
        return Err("ramlog= buffer must lie inside one 1 GiB region below 512 GiB");
    }
    Ok(addr)
}

/// The active buffer's address, or 0.
pub fn base() -> usize {
    BASE.load(Relaxed)
}

unsafe fn write_u32(base: usize, off: usize, v: u32) {
    core::ptr::write_volatile((base + off) as *mut u32, v)
}

unsafe fn write_u64(base: usize, off: usize, v: u64) {
    core::ptr::write_volatile((base + off) as *mut u64, v)
}

unsafe fn read_u64(base: usize, off: usize) -> u64 {
    core::ptr::read_volatile((base + off) as *const u64)
}

/// Writes a fresh header at `base` (identity mapped, writable), activates the buffer and copies the early bytes in.
pub unsafe fn start(base: usize) {
    core::ptr::write_volatile(base as *mut [u8; 8], MAGIC);
    write_u32(base, OFF_VERSION, VERSION);
    write_u32(base, OFF_HEADER_SIZE, HEADER_SIZE as u32);
    write_u64(base, OFF_CAPACITY, (SIZE - HEADER_SIZE) as u64);
    write_u64(base, OFF_WRITTEN, 0);
    write_u32(base, OFF_REASON, REASON_RUNNING);
    write_u32(base, OFF_CODE, 0);
    activate(base);
}

/// Activates the buffer at `base` that the loader started, continuing at its count; false if its magic is missing.
pub unsafe fn attach(base: usize) -> bool {
    if core::ptr::read_volatile(base as *const [u8; 8]) != MAGIC {
        return false;
    }
    activate(base);
    true
}

unsafe fn activate(base: usize) {
    let early = &*(&raw const EARLY);
    for &byte in early[..EARLY_LEN.load(Relaxed).min(early.len())].iter() {
        append(base, byte);
    }
    BASE.store(base, Relaxed);
}

/// Appends a console byte to the active buffer, or to the early bytes before one is active. The caller holds the
/// console lock.
#[inline(always)]
pub fn put(byte: u8) {
    let base = BASE.load(Relaxed);
    if base != 0 {
        unsafe { append(base, byte) }
    } else {
        put_early(byte)
    }
}

#[cold]
fn put_early(byte: u8) {
    let len = EARLY_LEN.load(Relaxed);
    if len < 2048 {
        unsafe { (*(&raw mut EARLY))[len] = byte };
        EARLY_LEN.store(len + 1, Relaxed);
    }
}

#[inline(never)]
unsafe fn append(base: usize, byte: u8) {
    let written = read_u64(base, OFF_WRITTEN);
    if written < (SIZE - HEADER_SIZE) as u64 {
        core::ptr::write_volatile((base + HEADER_SIZE + written as usize) as *mut u8, byte);
        write_u64(base, OFF_WRITTEN, written + 1);
    }
}

/// Records the exit reason and code in the active buffer's header; does nothing without one.
pub fn finish(reason: u32, code: u32) {
    let base = BASE.load(Relaxed);
    if base != 0 {
        unsafe {
            write_u32(base, OFF_CODE, code);
            write_u32(base, OFF_REASON, reason);
        }
    }
}

/// Writes back the caches and resets the machine: a warm reset through port 0xCF9 (0x02, then 0x06), then the
/// keyboard controller's reset line (0xFE to port 0x64), then halts.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub unsafe fn reset() -> ! {
    use core::arch::asm;
    asm!("cli", "wbinvd", options(nostack));
    asm!("out dx, al", in("dx") 0xcf9u16, in("al") 0x02u8, options(nomem, nostack));
    for _ in 0..1000 {
        asm!("out 0x80, al", in("al") 0u8, options(nomem, nostack));
    }
    asm!("out dx, al", in("dx") 0xcf9u16, in("al") 0x06u8, options(nomem, nostack));
    for _ in 0..100_000 {
        asm!("out 0x80, al", in("al") 0u8, options(nomem, nostack));
    }
    for _ in 0..100_000 {
        let status: u8;
        asm!("in al, 0x64", out("al") status, options(nomem, nostack));
        if status & 2 == 0 {
            break;
        }
    }
    asm!("out 0x64, al", in("al") 0xfeu8, options(nomem, nostack));
    loop {
        asm!("hlt", options(nomem, nostack));
    }
}
