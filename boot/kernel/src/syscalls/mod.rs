//! Syscall entry, dispatch into the verified kernel, and the idle loop.
//!
//! Every entry saves the complete user register file as a [`Registers`] frame at the top of the
//! per-CPU kernel stack, and every exit restores a complete frame. The verified kernel switches
//! threads by rewriting that frame (`syscall_schedule` swaps it with the next thread's trap frame),
//! so no register may be treated as clobbered: [`restore_frame`] returns with `sysretq` only when
//! that gives exactly the state `iretq` would.
//!
//! Per-CPU data is reached through the GS base. Ring 3 can reload `gs` and so zero that base, so
//! every crossing executes `swapgs`: `sys_entry` and the interrupt trampolines (for frames from
//! ring 3) on the way in, [`restore_frame`] and the trampolines on the way out. The NMI handler and
//! the fatal-exception path may run with either base and use [`cpu::cpu_id_without_gs`] instead.
//!
//! TODO: the frame is not the whole user-visible CPU state. The x87/MMX registers (CR0.EM is 0)
//! and the `fs`/`gs` selectors are neither saved nor reset across a thread switch, so the next
//! thread, of any container, reads what the previous one left. Either set CR0.EM = 1 (the Rust
//! targets are soft-float, nothing in tree uses x87) and reload `fs`/`gs` with 0 before every
//! return to ring 3, or save and restore that state per thread.

use core::arch::naked_asm;
use core::mem::{offset_of, size_of};

use veriflat_monolith::kernel::implementation::rebalance_pull::rebalance_pull::{rebalance_pull, RebalanceResult};
use veriflat_monolith::kernel::implementation::syscall_alloc_quota::syscall_alloc_quota::{
    syscall_alloc_quota_2m, syscall_alloc_quota_4k, syscall_alloc_thread_quota_2m, syscall_alloc_thread_quota_4k,
};
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::cpu_offline_check::{cpu_offline_check, OfflineCheckResult};
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::cpu_online_resume::{cpu_online_resume, OnlineResumeResult};
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_offline_request::syscall_cpu_offline_request;
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_offline_request_child::syscall_cpu_offline_request_child;
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_online::syscall_cpu_online;
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_online_child::syscall_cpu_online_child;
use veriflat_monolith::kernel::implementation::syscall_ipc::syscall_ipc::*;
use veriflat_monolith::kernel::implementation::syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k;
use veriflat_monolith::kernel::implementation::syscall_new_container::{syscall_new_container, syscall_new_container_with_endpoint};
use veriflat_monolith::kernel::implementation::syscall_new_endpoint::syscall_new_endpoint::syscall_new_endpoint;
use veriflat_monolith::kernel::implementation::syscall_new_process::syscall_new_process::syscall_new_process;
use veriflat_monolith::kernel::implementation::syscall_new_process::syscall_new_process_with_endpoint::syscall_new_process_with_endpoint;
use veriflat_monolith::kernel::implementation::syscall_new_process::syscall_new_process_with_iommu_and_endpoint::syscall_new_process_with_iommu_and_endpoint;
use veriflat_monolith::kernel::implementation::syscall_new_thread::syscall_new_thread::syscall_new_thread;
use veriflat_monolith::kernel::implementation::syscall_new_thread_with_endpoint::syscall_new_thread_with_endpoint::syscall_new_thread_with_endpoint;
use veriflat_monolith::kernel::implementation::syscall_pci::syscall_pci_attach_dma::syscall_pci_attach_dma;
use veriflat_monolith::kernel::implementation::syscall_schedule::syscall_schedule::{syscall_schedule, ScheduleResult};
use veriflat_monolith::kernel::implementation::syscall_unmap_4k::syscall_unmap_4k;
use veriflat_monolith::{IPCPayLoad, Registers, RetValueType, MAX_NUM_ENDPOINT_DESCRIPTORS, NUM_CPUS, PCI_BUS_COUNT, PCI_DEVICE_COUNT, PCI_FUNCTION_COUNT};
use vstd::prelude::Tracked;
use x86::msr;
use x86::segmentation::SegmentSelector;
use x86::Ring;

use crate::cpu::{self, Cpu};
use crate::gdt::GlobalDescriptorTable;
use crate::glue::kernel;
use crate::interrupt::{self, Cycles};

const _: () = assert!(size_of::<Registers>() == 21 * 8);

/// RFLAGS bits cleared on `syscall`: TF, IF, DF, NT, AC.
const SYSCALL_FMASK: u64 = (1 << 8) | (1 << 9) | (1 << 10) | (1 << 14) | (1 << 18);

/// RFLAGS bits that keep a return on `iretq`: `sysretq` clears RF, and with TF set it traps before
/// the first user instruction instead of after it.
const SYSRET_UNSAFE_FLAGS: u64 = (1 << 16) | (1 << 8);

/// Model errors are returned as `-(MODEL_ERROR_BASE + index)`.
const MODEL_ERROR_BASE: i64 = 100;

/// LAPIC timer cycles per scheduling tick (about 10 ms under KVM).
const TICK: Cycles = Cycles(5_000_000);

/// Initializes syscalls.
///
/// This must be called only once for each CPU reset.
pub unsafe fn init_cpu() {
    use GlobalDescriptorTable as GDT;

    // syscall: CS = STAR[47:32], SS = CS + 8. sysretq: SS = STAR[63:48] + 8, CS = + 16, both RPL 3.
    let kernel_cs = SegmentSelector::new(GDT::KERNEL_CODE_INDEX, Ring::Ring0);
    let user_base = SegmentSelector::new(GDT::USER_DATA_INDEX - 1, Ring::Ring3);
    let star = ((user_base.bits() as u64) << 48) | ((kernel_cs.bits() as u64) << 32);
    msr::wrmsr(msr::IA32_STAR, star);
    msr::wrmsr(msr::IA32_LSTAR, sys_entry as *const () as u64);
    msr::wrmsr(msr::IA32_CSTAR, 0);
    msr::wrmsr(msr::IA32_FMASK, SYSCALL_FMASK);

    // Enable EFER Bit 0 - System Call Extensions
    let efer = msr::rdmsr(msr::IA32_EFER);
    msr::wrmsr(msr::IA32_EFER, efer | 0x1);
}

// Syscall ABI
//
// Register | User           | Kernel
// ---------------------------------------------
// rax      | Syscall Number | Return value
// rdi      | Arg #1         |
// rsi      | Arg #2         | Return value #3
// rdx      | Arg #3         | Return value #2
// r8       | Arg #4         |
// r9       | Arg #5         |
// r12      | Arg #6         |
// r13      | Arg #7         |
// r14      | Arg #8         |
//
// rcx and r11 are taken by `syscall` (user rip and rflags); r10 is clobbered.
#[unsafe(naked)]
unsafe extern "C" fn sys_entry() -> ! {
    naked_asm!(
        "swapgs",
        "mov r10, rsp",
        "mov rsp, gs:{syscall_sp_offset}",

        // struct Registers, from the highest field down.
        "push {user_ss}", // ss
        "push r10",       // rsp
        "push r11",       // rflags
        "push {user_cs}", // cs
        "push rcx",       // rip
        "push 0",         // error_code
        "push rax",
        "push rdi",
        "push rsi",
        "push rdx",
        "push rcx",
        "push r8",
        "push r9",
        "push r10",
        "push r11",
        "push rbx",
        "push rbp",
        "push r12",
        "push r13",
        "push r14",
        "push r15",

        "mov rdi, rsp",
        "sub rsp, 8", // 21 pushes leave rsp 8 off the 16-byte call alignment
        "call {dispatch}",
        "add rsp, 8",
        "jmp {restore}",

        user_ss = const GlobalDescriptorTable::USER_SS,
        user_cs = const GlobalDescriptorTable::USER_CS,
        syscall_sp_offset = const offset_of!(Cpu, syscall_sp),
        dispatch = sym syscall_dispatch,
        restore = sym restore_frame,
    );
}

/// Restores the frame at `rsp` and returns to it.
///
/// `sysretq` takes `rip` from `rcx` and `rflags` from `r11`, leaves both registers holding them,
/// and loads the selectors `STAR` names, so it gives exactly the state `iretq` would when the frame
/// has `rcx == rip`, `r11 == rflags`, the user `cs` and `ss`, and no [`SYSRET_UNSAFE_FLAGS`]. A
/// frame `sys_entry` saved has all of them; a thread preempted by an interrupt or starting fresh
/// almost never has. `rip` must also lie in the lower canonical half: on Intel CPUs `sysretq` to a
/// non-canonical address faults in ring 0 after the user `rsp` is already loaded. Interrupts stay
/// off until `sysretq`; NMIs and machine checks taken after the user `rsp` is loaded run on IST stacks.
/// The frame is always a ring 3 frame, so both returns `swapgs` unconditionally.
#[unsafe(naked)]
unsafe extern "C" fn restore_frame() -> ! {
    naked_asm!(
        // ZF = 1 selects sysretq. pop leaves the flags alone.
        "mov rcx, [rsp + {frame_rip}]",
        "mov r11, [rsp + {frame_rflags}]",
        "cmp rcx, [rsp + {frame_rcx}]",
        "jne 2f",
        "cmp r11, [rsp + {frame_r11}]",
        "jne 2f",
        "test r11, {unsafe_flags}",
        "jnz 2f",
        "cmp qword ptr [rsp + {frame_cs}], {user_cs}",
        "jne 2f",
        "cmp qword ptr [rsp + {frame_ss}], {user_ss}",
        "jne 2f",
        "mov rax, rcx",
        "shr rax, 47",
        "2:",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbp",
        "pop rbx",
        "pop r11",
        "pop r10",
        "pop r9",
        "pop r8",
        "pop rcx",
        "pop rdx",
        "pop rsi",
        "pop rdi",
        "pop rax",
        "jnz 3f",
        "inc qword ptr gs:[{sysret_exits}]",
        "mov rsp, [rsp + {user_rsp}]", // error_code, rip, cs, rflags, then the user rsp
        "swapgs",
        "sysretq",
        "3:",
        "inc qword ptr gs:[{iret_exits}]",
        "add rsp, 8", // error_code
        "swapgs",
        "iretq",

        frame_rip = const offset_of!(Registers, rip),
        frame_rflags = const offset_of!(Registers, flags),
        frame_rcx = const offset_of!(Registers, rcx),
        frame_r11 = const offset_of!(Registers, r11),
        frame_cs = const offset_of!(Registers, cs),
        frame_ss = const offset_of!(Registers, ss),
        unsafe_flags = const SYSRET_UNSAFE_FLAGS,
        user_cs = const GlobalDescriptorTable::USER_CS,
        user_ss = const GlobalDescriptorTable::USER_SS,
        user_rsp = const offset_of!(Registers, rsp) - offset_of!(Registers, error_code),
        sysret_exits = const offset_of!(Cpu, sysret_exits),
        iret_exits = const offset_of!(Cpu, iret_exits),
    );
}

/// Enters the frame at `frame` (on the current CPU's kernel stack).
#[unsafe(naked)]
unsafe extern "C" fn enter_frame(frame: *const Registers) -> ! {
    naked_asm!(
        "mov rsp, rdi",
        "jmp {restore}",
        restore = sym restore_frame,
    );
}

/// Runs the idle loop on the boot CPU until a thread is chosen, then enters it. Called once
/// after the verified kernel is initialized.
pub unsafe fn enter_first_thread() -> ! {
    let frame = cpu::top_frame();
    frame.write(Registers::zeroed());
    start_timer();
    run_idle(&mut *frame);
    log::info!("entering first thread at {:#x}", (*frame).rip);
    enter_frame(frame);
}

/// Parks a started AP: it is Off in the verified model until `cpu_online` wakes it, then runs the
/// idle loop and enters the thread it finds.
pub unsafe fn enter_off_cpu() -> ! {
    let frame = cpu::top_frame();
    frame.write(Registers::zeroed());
    wait_until_online(cpu::get_cpu_id());
    run_idle(&mut *frame);
    enter_frame(frame);
}

fn start_timer() {
    cpu::get_current().timer_on = true;
    interrupt::set_timer(TICK);
}

/// LAPIC timer tick. From user mode it preempts the running thread; in the kernel it only ends a
/// `hlt` of the idle loop.
pub fn timer_interrupt(regs: &mut Registers) {
    interrupt::end_of_interrupt();
    if cpu::get_current().timer_on {
        interrupt::set_timer(TICK);
    }
    if from_user(regs) {
        schedule_from_running(regs);
    }
}

/// Wake-up IPI. From user mode the CPU runs its offline check (an offline request kicks it); in the
/// kernel it only ends a `hlt`.
pub fn wake_interrupt(regs: &mut Registers) {
    interrupt::end_of_interrupt();
    if from_user(regs) {
        let cpu_id = cpu::get_cpu_id();
        if let OfflineCheckResult::Off = cpu_offline_check(kernel(), Tracked::assume_new(), Tracked::assume_new(), cpu_id, regs) {
            wait_until_online(cpu_id);
            run_idle(regs);
        }
    }
}

fn from_user(regs: &Registers) -> bool {
    regs.cs & 3 == 3
}

/// Writes a verified result into the caller's frame.
fn encode(regs: &mut Registers, ret: RetValueType) {
    use RetValueType::*;
    let (rax, rdx, rsi): (i64, u64, u64) = match ret {
        SuccessUsize { value } => (value as i64, 0, 0),
        SuccessSeqUsize { .. } => (0, 0, 0),
        SuccessPairUsize { value1, value2 } => (value1 as i64, value2 as u64, 0),
        SuccessThreeUsize { value1, value2, value3 } => (value1 as i64, value2 as u64, value3 as u64),
        Success => (0, 0, 0),
        other => (-(MODEL_ERROR_BASE + error_index(other) as i64), 0, 0),
    };
    regs.rax = rax as u64;
    regs.rdx = rdx;
    regs.rsi = rsi;
}

/// The position of an error variant in `RetValueType`; `vsys::error_name` mirrors it.
fn error_index(ret: RetValueType) -> usize {
    use RetValueType::*;
    match ret {
        SuccessUsize { .. } => 0,
        SuccessSeqUsize { .. } => 1,
        SuccessPairUsize { .. } => 2,
        SuccessThreeUsize { .. } => 3,
        Success => 4,
        ErrorNoQuota => 5,
        ErrorVaInUse => 6,
        CpuIdle => 7,
        Error => 8,
        Else => 9,
        NoQuota => 10,
        VaInUse => 11,
        ErrorContainerKilled => 12,
        ErrorContainerQuotaInsufficient => 13,
        ErrorProcessKilled => 14,
        ErrorThreadKilled => 15,
        ErrorNoPcid => 16,
        ErrorInvalidEndpoint => 17,
        ErrorIpcNoPeer => 18,
        ErrorIpcSameDirection => 19,
        ErrorIpcTypeMismatch => 20,
        ErrorIpcPeerKilled => 21,
        ErrorIpcSameProcess => 22,
        ErrorIpcSameContainer => 23,
        ErrorIpcCpuOwnerMismatch => 24,
        ErrorIpcCpuNotOff => 25,
        ErrorIpcPciOwnerMismatch => 26,
        ErrorPciOwnerMismatch => 27,
        ErrorPciNoIommuTable => 28,
        ErrorPciAlreadyAttached => 29,
        ErrorCpuOwnerMismatch => 30,
        ErrorCpuAlreadyOff => 31,
        ErrorCpuNotOff => 32,
        ErrorIpcSourceUnmapped => 33,
        ErrorIpcPageOwnerMismatch => 34,
        ErrorIpcEndpointSourceInvalid => 35,
        ErrorIpcEndpointTargetInUse => 36,
        ErrorIpcEndpointOwnerMismatch => 37,
        ErrorCallAcrossContainers => 38,
        ErrorReplyOutOfPhase => 39,
        ErrorProcessQuotaOverflow => 40,
        ErrorThreadQuotaOverflow => 41,
    }
}

/// The frame a new thread or process starts with: the caller's registers with a new `rip`,
/// `rsp`, and `rax = 0`.
/// A thread may start only at a lower-half canonical address: `iretq` to any other `rip` faults in
/// ring 0 instead of in the new thread.
fn user_ip_ok(ip: usize) -> bool {
    ip >> 47 == 0
}

fn initial_frame(caller: &Registers, ip: usize, sp: usize) -> Registers {
    let mut regs = *caller;
    regs.rip = ip as u64;
    regs.rsp = sp as u64;
    regs.rax = 0;
    regs.error_code = 0;
    regs.cs = GlobalDescriptorTable::USER_CS as u64;
    regs.ss = GlobalDescriptorTable::USER_SS as u64;
    regs
}

fn endpoint_ok(index: usize) -> bool {
    index < MAX_NUM_ENDPOINT_DESCRIPTORS
}

fn bdf_ok(bus: usize, dev: usize, fun: usize) -> bool {
    bus < PCI_BUS_COUNT && dev < PCI_DEVICE_COUNT && fun < PCI_FUNCTION_COUNT
}

fn set_trap_error(regs: &mut Registers, err: isize) {
    regs.rax = err as i64 as u64;
}

/// Dispatches a syscall. On return the frame holds the registers of the thread to resume, which is
/// the caller unless the call blocked or yielded.
extern "C" fn syscall_dispatch(regs: &mut Registers) {
    let nr = regs.rax as usize;
    let (a1, a2, a3, a4, a5, a6, a7) =
        (regs.rdi as usize, regs.rsi as usize, regs.rdx as usize, regs.r8 as usize, regs.r9 as usize, regs.r12 as usize, regs.r13 as usize);
    let cpu_id = cpu::get_cpu_id();
    let k = kernel();
    macro_rules! t {
        () => {
            Tracked::assume_new()
        };
    }
    macro_rules! require {
        ($cond:expr) => {
            if !$cond {
                set_trap_error(regs, vsys::ERR_INVALID_ARGUMENT);
                return;
            }
        };
    }

    let ret = match nr {
        vsys::NR_DEBUG_PRINT => {
            debug_print(a1, a2);
            regs.rax = 0;
            return;
        }
        vsys::NR_DEBUG_EXIT => unsafe { crate::boot::exit_qemu(a1 as u32) },
        vsys::NR_DEBUG_DMA_DEVICE => {
            regs.rax = crate::iommu::dma_test_device().map_or(vsys::ERR_INVALID_SYSCALL, |bdf| bdf as isize) as u64;
            return;
        }
        vsys::NR_DEBUG_DMA_PROBE => {
            regs.rax = crate::iommu::dma_probe().map_or(vsys::ERR_INVALID_SYSCALL, |reason| reason as isize) as u64;
            return;
        }
        vsys::NR_DEBUG_NULL => {
            // The syscall ABI clobbers rcx; any value but `rip` sends the return through `iretq`.
            if a1 != 0 {
                regs.rcx = !regs.rip;
            }
            regs.rax = 0;
            return;
        }
        vsys::NR_SCHEDULE => {
            regs.rax = 0;
            schedule_from_running(regs);
            return;
        }
        vsys::NR_ALLOC_QUOTA_4K => syscall_alloc_quota_4k(k, t!(), t!(), cpu_id, a1),
        vsys::NR_ALLOC_THREAD_QUOTA_4K => syscall_alloc_thread_quota_4k(k, t!(), t!(), cpu_id, a1),
        vsys::NR_ALLOC_QUOTA_2M => syscall_alloc_quota_2m(k, t!(), t!(), cpu_id, a1),
        vsys::NR_ALLOC_THREAD_QUOTA_2M => syscall_alloc_thread_quota_2m(k, t!(), t!(), cpu_id, a1),
        // A CPU ID with no processor behind it stays Off for good.
        vsys::NR_CPU_OFFLINE_REQUEST => {
            require!(a1 < cpu::present_cpus());
            syscall_cpu_offline_request(k, t!(), t!(), cpu_id, a1)
        }
        vsys::NR_CPU_ONLINE => {
            require!(a1 < cpu::present_cpus());
            syscall_cpu_online(k, t!(), t!(), cpu_id, a1)
        }
        vsys::NR_CPU_OFFLINE_REQUEST_CHILD => {
            require!(a2 < cpu::present_cpus());
            syscall_cpu_offline_request_child(k, t!(), t!(), cpu_id, a1, a2)
        }
        vsys::NR_CPU_ONLINE_CHILD => {
            require!(a2 < cpu::present_cpus());
            syscall_cpu_online_child(k, t!(), t!(), cpu_id, a1, a2)
        }
        vsys::NR_NEW_THREAD => {
            require!(user_ip_ok(a1));
            let init = initial_frame(regs, a1, a2);
            syscall_new_thread(k, t!(), t!(), cpu_id, &init)
        }
        vsys::NR_NEW_THREAD_WITH_ENDPOINT => {
            require!(endpoint_ok(a1) && user_ip_ok(a2));
            let init = initial_frame(regs, a2, a3);
            syscall_new_thread_with_endpoint(k, t!(), t!(), cpu_id, a1, &init)
        }
        vsys::NR_NEW_ENDPOINT => {
            require!(endpoint_ok(a1));
            syscall_new_endpoint(k, t!(), t!(), cpu_id, a1)
        }
        vsys::NR_MMAP_4K => syscall_mmap_4k(k, t!(), t!(), cpu_id, a1, a2),
        vsys::NR_UNMAP_4K => syscall_unmap_4k(k, t!(), t!(), cpu_id, a1, a2),
        vsys::NR_NEW_PROCESS => {
            require!(user_ip_ok(a3));
            let init = initial_frame(regs, a3, a4);
            syscall_new_process(k, t!(), t!(), cpu_id, a1, a2, &init)
        }
        vsys::NR_NEW_PROCESS_WITH_ENDPOINT => {
            require!(endpoint_ok(a3) && user_ip_ok(a4));
            let init = initial_frame(regs, a4, a5);
            syscall_new_process_with_endpoint(k, t!(), t!(), cpu_id, a1, a2, a3, &init)
        }
        vsys::NR_NEW_PROCESS_WITH_IOMMU_AND_ENDPOINT => {
            require!(endpoint_ok(a3) && user_ip_ok(a4));
            let init = initial_frame(regs, a4, a5);
            syscall_new_process_with_iommu_and_endpoint(k, t!(), t!(), cpu_id, a1, a2, a3, &init)
        }
        vsys::NR_NEW_CONTAINER => {
            require!(user_ip_ok(a6));
            let init = initial_frame(regs, a6, a7);
            syscall_new_container(k, t!(), t!(), cpu_id, a1, a2, a3, a4, a5, &init)
        }
        vsys::NR_NEW_CONTAINER_WITH_ENDPOINT => {
            require!(endpoint_ok(a6) && user_ip_ok(a7));
            let init = initial_frame(regs, a7, regs.r14 as usize);
            syscall_new_container_with_endpoint(k, t!(), t!(), cpu_id, a1, a2, a3, a4, a5, a6, &init)
        }
        vsys::NR_SEND_EMPTY => {
            require!(endpoint_ok(a1));
            syscall_send_empty(k, t!(), t!(), cpu_id, a1, regs)
        }
        vsys::NR_RECEIVE_EMPTY => {
            require!(endpoint_ok(a1));
            syscall_receive_empty(k, t!(), t!(), cpu_id, a1, regs)
        }
        vsys::NR_SEND_EMPTY_NO_BLOCK => {
            require!(endpoint_ok(a1));
            syscall_send_empty_no_block(k, t!(), t!(), cpu_id, a1, regs)
        }
        vsys::NR_RECEIVE_EMPTY_NO_BLOCK => {
            require!(endpoint_ok(a1));
            syscall_receive_empty_no_block(k, t!(), t!(), cpu_id, a1, regs)
        }
        // A direct handoff leaves `regs` holding the frame of the thread switched to, so the
        // common `encode` below delivers the result to that thread.
        vsys::NR_CALL => {
            require!(endpoint_ok(a1));
            syscall_call(k, t!(), t!(), cpu_id, a1, IPCPayLoad::Empty, regs)
        }
        vsys::NR_CALL_USIZE => {
            require!(endpoint_ok(a1));
            syscall_call(k, t!(), t!(), cpu_id, a1, IPCPayLoad::Usize { value: a2 }, regs)
        }
        vsys::NR_RECEIVE_CALL => {
            require!(endpoint_ok(a1));
            syscall_receive_call(k, t!(), t!(), cpu_id, a1, regs)
        }
        vsys::NR_REPLY_AND_RECEIVE => {
            require!(endpoint_ok(a1));
            syscall_reply_and_receive(k, t!(), t!(), cpu_id, a1, IPCPayLoad::Empty, regs)
        }
        vsys::NR_REPLY_AND_RECEIVE_USIZE => {
            require!(endpoint_ok(a1));
            syscall_reply_and_receive(k, t!(), t!(), cpu_id, a1, IPCPayLoad::Usize { value: a2 }, regs)
        }
        vsys::NR_SEND_CPU => {
            require!(endpoint_ok(a1) && a2 < NUM_CPUS);
            syscall_send_cpu(k, t!(), t!(), cpu_id, a1, a2, regs)
        }
        vsys::NR_RECEIVE_CPU => {
            require!(endpoint_ok(a1));
            syscall_receive_cpu(k, t!(), t!(), cpu_id, a1, regs)
        }
        vsys::NR_SEND_PCI => {
            require!(endpoint_ok(a1) && bdf_ok(a2, a3, a4));
            syscall_send_pci(k, t!(), t!(), cpu_id, a1, a2 as u8, a3 as u8, a4 as u8, regs)
        }
        vsys::NR_RECEIVE_PCI => {
            require!(endpoint_ok(a1) && bdf_ok(a2, a3, a4));
            syscall_receive_pci(k, t!(), t!(), cpu_id, a1, a2 as u8, a3 as u8, a4 as u8, regs)
        }
        vsys::NR_SEND_ENDPOINT => {
            require!(endpoint_ok(a1) && endpoint_ok(a2));
            syscall_send_endpoint(k, t!(), t!(), cpu_id, a1, a2, regs)
        }
        vsys::NR_RECEIVE_ENDPOINT => {
            require!(endpoint_ok(a1) && endpoint_ok(a2));
            syscall_receive_endpoint(k, t!(), t!(), cpu_id, a1, a2, regs)
        }
        vsys::NR_SEND_PAGES => {
            require!(endpoint_ok(a1));
            syscall_send_pages(k, t!(), t!(), cpu_id, a1, a2, a3, regs)
        }
        vsys::NR_RECEIVE_PAGES => {
            require!(endpoint_ok(a1));
            syscall_receive_pages(k, t!(), t!(), cpu_id, a1, a2, a3, regs)
        }
        vsys::NR_PCI_ATTACH_DMA => {
            require!(bdf_ok(a1, a2, a3));
            syscall_pci_attach_dma(k, t!(), t!(), cpu_id, a1, a2, a3)
        }
        _ => {
            set_trap_error(regs, vsys::ERR_INVALID_SYSCALL);
            return;
        }
    };

    if let RetValueType::CpuIdle = ret {
        // The caller blocked; its frame is saved in its thread. Pick the next thread.
        run_idle(regs);
    } else {
        encode(regs, ret);
    }
}

fn debug_print(data: usize, len: usize) {
    // dom0 shares the kernel's identity map, and every user mapping is readable from ring 0.
    let bytes = unsafe { core::slice::from_raw_parts(data as *const u8, len.min(4096)) };
    match core::str::from_utf8(bytes) {
        Ok(s) => log::info!("[user@{}] {}", cpu::get_cpu_id(), s.trim_end()),
        Err(_) => log::info!("[user@{}] <{} non-UTF-8 bytes>", cpu::get_cpu_id(), bytes.len()),
    }
}

/// `sys_schedule` or a timer tick from a running thread: the offline check, then a context switch.
fn schedule_from_running(regs: &mut Registers) {
    let cpu_id = cpu::get_cpu_id();
    let k = kernel();
    if let OfflineCheckResult::Off = cpu_offline_check(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id, regs) {
        wait_until_online(cpu_id);
        run_idle(regs);
        return;
    }
    match syscall_schedule(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id, regs) {
        ScheduleResult::Switched { syscall_return, .. } => {
            if let Some(ret) = syscall_return {
                encode(regs, ret);
            }
        }
        ScheduleResult::Continue => {}
        ScheduleResult::Idle => run_idle(regs),
        ScheduleResult::Off => {
            wait_until_online(cpu_id);
            run_idle(regs);
        }
    }
}

/// The idle loop of a CPU without a running thread. Returns once `regs` holds the frame of the
/// thread the CPU switched to.
fn run_idle(regs: &mut Registers) {
    let cpu_id = cpu::get_cpu_id();
    let k = kernel();
    loop {
        if let OfflineCheckResult::Off = cpu_offline_check(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id, regs) {
            wait_until_online(cpu_id);
            continue;
        }
        match syscall_schedule(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id, regs) {
            ScheduleResult::Switched { syscall_return, .. } => {
                if let Some(ret) = syscall_return {
                    encode(regs, ret);
                }
                return;
            }
            // A killed head was dropped; look again.
            ScheduleResult::Continue => continue,
            ScheduleResult::Off => {
                wait_until_online(cpu_id);
                continue;
            }
            ScheduleResult::Idle => {}
        }
        match rebalance_pull(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id) {
            RebalanceResult::Pulled { .. } => continue,
            // Wait for the next tick or IPI; another CPU may queue a thread here meanwhile.
            RebalanceResult::Nothing => unsafe { core::arch::asm!("sti", "hlt", "cli", options(nomem, nostack)) },
        }
    }
}

/// A CPU that is Off: its timer stops and `cpu_online_resume` halts it until `cpu_online` publishes
/// it Idle again.
fn wait_until_online(cpu_id: usize) {
    log::info!("CPU {} is offline", cpu_id);
    cpu::get_current().timer_on = false;
    interrupt::disarm_timer();
    while let OnlineResumeResult::StillOff = cpu_online_resume(kernel(), Tracked::assume_new(), Tracked::assume_new(), cpu_id) {}
    log::info!("CPU {} is online", cpu_id);
    start_timer();
}
