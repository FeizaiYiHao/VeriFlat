//! Utilities.

use core::arch::naked_asm;

/// `memcpy` for the whole kernel image, the verified kernel included; it takes the place of the weak
/// one of `compiler_builtins`, which runs three `rep movs` (byte head, qword body, byte tail) for
/// any size. The hot callers copy 168-byte trap frames: every IPC call and reply moves the caller's
/// and the callee's `Registers` between the CPU's frame slot and the threads (`TrapFrameOption::
/// set_self`, `set_dst`). Up to 256 bytes it copies qwords in a loop, then the remaining bytes;
/// longer copies take one `rep movsb`. Regions must not overlap, as for any `memcpy`.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn memcpy(dst: *mut u8, src: *const u8, len: usize) -> *mut u8 {
    naked_asm!(
        "mov rax, rdi",
        "cmp rdx, 256",
        "ja 4f",
        "mov rcx, rdx",
        "shr rcx, 3",
        "jz 2f",
        // rsi and rdi end past the qwords; rcx counts up from -qwords to 0
        "lea rsi, [rsi + rcx * 8]",
        "lea rdi, [rdi + rcx * 8]",
        "neg rcx",
        "1:",
        "mov r8, [rsi + rcx * 8]",
        "mov [rdi + rcx * 8], r8",
        "inc rcx",
        "jnz 1b",
        "2:",
        "and edx, 7",
        "jz 3f",
        "5:",
        "mov r8b, [rsi]",
        "mov [rdi], r8b",
        "inc rsi",
        "inc rdi",
        "dec edx",
        "jnz 5b",
        "3:",
        "ret",
        "4:",
        "mov rcx, rdx",
        "rep movsb",
        "ret",
    );
}
