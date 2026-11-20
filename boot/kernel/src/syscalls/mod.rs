//! Syscall entry, dispatch into the verified kernel, and the idle loop.
//!
//! The trap frame of a thread is the `Registers` slot inside that thread's own 4K page
//! (`thread_trap_frame_addr` of the verified kernel, [`cpu::THREAD_FRAME_OFFSET`]). Every entry from
//! ring 3 saves the complete user register file directly into the slot of the thread the CPU runs:
//! `sys_entry` pushes it below the per-CPU frame-top word (`Cpu::frame_top`), and an interrupt from
//! ring 3 pushes it below TSS.rsp0, which holds the same address. The trampoline then continues on
//! the per-CPU kernel stack. Every exit restores the complete frame of the thread the CPU runs then
//! ([`resume_current_frame`]). The verified kernel switches threads by moving the frame permissions
//! between the threads and its per-CPU slot table and by recording the new current thread in its cpu
//! object; it never copies registers. After every call into it, [`sync_current_frame`] reads that
//! record and points `frame_top` and TSS.rsp0 at the current thread's slot. No register may be
//! treated as clobbered: [`restore_frame`] returns with `sysretq` only when that gives exactly the
//! state `iretq` would. The trap layer writes a thread's frame only while it runs on this CPU: the
//! saves at entry, and the return values (rax, rdx, rsi) that [`encode`] writes into the frame of
//! the thread the CPU returns to (the model's trap-return-values-written event).
//!
//! Per-CPU data is reached through the GS base. Ring 3 can reload `gs` and so zero that base, so
//! every crossing executes `swapgs`: `sys_entry` and the interrupt trampolines (for frames from
//! ring 3) on the way in, [`restore_frame`], the only exit to ring 3, on the way out. The NMI handler
//! and the fatal-exception path may run with either base and use [`cpu::cpu_id_without_gs`] instead.
//!
//! Interrupts are off exactly while this CPU holds its own CPU lock inside a kernel step: the
//! verified kernel's own-CPU lock executes `cli` when it is granted and `sti` after its release
//! (`platform::veriflat_disable_interrupts`, `platform::veriflat_enable_interrupts`). Everywhere
//! else (ring 3, the trampolines, the idle loop, an Off CPU) they are on. `syscall` and the
//! interrupt gates clear IF in hardware; `sys_entry` and the interrupt trampolines (for frames from
//! ring 3) execute `sti` once the frame is saved in the thread's slot and `rsp` is on the kernel
//! stack, and [`resume_current_frame`] and [`restore_frame`] execute `cli` first (the former then
//! enters the latter just after its `cli`), so `rsp` never
//! points into a thread page while interrupts are on, and the last check and the return to ring 3
//! are one step. An interrupt taken in the kernel keeps IF
//! clear in its handler, which only acknowledges, re-arms the timer, or sets a flag.
//!
//! A running-to-idle IPI (`platform::veriflat_ipi_running_to_idle`) makes this CPU abandon its
//! thread at another CPU's request. It is a maskable IPI, so this CPU takes it anywhere outside a
//! kernel step: in ring 3, in a trampoline, in [`run_idle`], or at a `hlt`. The requester holds and
//! marked this CPU's lock, so this CPU is not inside a step and a step that would lock its own CPU
//! returns at once. The IPI loads the kernel page table and sets `Cpu::running_to_idle_pending`;
//! the next exit through [`restore_frame`] diverts to the idle loop instead of ring 3. The handler
//! does not acknowledge: this CPU acknowledges when it enters its idle loop, after it has left the
//! trap path of the thread it ran, and clears the flag there (`platform::acknowledge_running_to_idle`).
//! Until then the requester holds this CPU's lock, so every glue path reaches the idle loop without
//! a step: through [`restore_frame`], or from a syscall or tick whose step found this CPU marked.
//!
//! User mode has no floating point: every CPU enters ring 3 with CR0.TS set (see
//! [`cpu::disable_user_fp`]), so x87/MMX instructions raise #NM and SSE/AVX raise #UD, and the
//! faulting thread exits.
//!
//! TODO: the frame is not the whole user-visible CPU state. The `fs`/`gs` selectors are neither saved
//! nor reset across a thread switch, so the next thread, of any container, reads what the previous
//! one left. Reload `fs`/`gs` with 0 before every return to ring 3, or save and restore them per thread.

use core::arch::naked_asm;
use core::mem::{offset_of, size_of};

use veriflat_monolith::kernel::implementation::rebalance_pull::rebalance_pull::{rebalance_pull, RebalanceResult};
use veriflat_monolith::kernel::implementation::syscall_alloc_quota::syscall_alloc_quota::{
    syscall_alloc_quota_2m, syscall_alloc_quota_4k, syscall_alloc_thread_quota_2m, syscall_alloc_thread_quota_4k,
};
use veriflat_monolith::kernel::implementation::syscall_alloc_quota::syscall_alloc_quota_1g::{syscall_alloc_quota_1g, syscall_alloc_thread_quota_1g};
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_offline_check::{cpu_offline_check, OfflineCheckResult};
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_online_resume::{cpu_online_resume, OnlineResumeResult};
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_offline_request::syscall_cpu_offline_request;
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_offline_request_child::syscall_cpu_offline_request_child;
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_online::syscall_cpu_online;
use veriflat_monolith::kernel::implementation::syscall_cpu_hotplug::syscall_cpu_online_child::syscall_cpu_online_child;
use veriflat_monolith::kernel::implementation::syscall_ipc::syscall_ipc::*;
use veriflat_monolith::kernel::implementation::syscall_kill_process::syscall_kill_process::syscall_kill_process;
use veriflat_monolith::kernel::implementation::syscall_kill_container::syscall_kill_container::syscall_kill_container;
use veriflat_monolith::kernel::implementation::syscall_iommu_map_4k::syscall_iommu_map_4k::syscall_iommu_map_4k;
use veriflat_monolith::kernel::implementation::syscall_iommu_unmap_4k::syscall_iommu_unmap_4k::syscall_iommu_unmap_4k;
use veriflat_monolith::kernel::implementation::syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k;
use veriflat_monolith::kernel::implementation::syscall_merge_2m::syscall_merge_2m::syscall_merge_2m;
use veriflat_monolith::kernel::implementation::syscall_split_2m::syscall_split_2m::syscall_split_2m;
use veriflat_monolith::kernel::implementation::syscall_mmap_2m::syscall_mmap_2m::syscall_mmap_2m;
use veriflat_monolith::kernel::implementation::syscall_new_container::{syscall_new_container, syscall_new_container_with_endpoint};
use veriflat_monolith::kernel::implementation::syscall_new_endpoint::syscall_new_endpoint::syscall_new_endpoint;
use veriflat_monolith::kernel::implementation::syscall_new_process::syscall_new_process::syscall_new_process;
use veriflat_monolith::kernel::implementation::syscall_new_process::syscall_new_process_with_endpoint::syscall_new_process_with_endpoint;
use veriflat_monolith::kernel::implementation::syscall_new_process::syscall_new_process_with_iommu_and_endpoint::syscall_new_process_with_iommu_and_endpoint;
use veriflat_monolith::kernel::implementation::syscall_new_thread::syscall_new_thread::syscall_new_thread;
use veriflat_monolith::kernel::implementation::syscall_new_thread_with_endpoint::syscall_new_thread_with_endpoint::syscall_new_thread_with_endpoint;
use veriflat_monolith::kernel::implementation::syscall_pci::syscall_pci_attach_dma::syscall_pci_attach_dma;
use veriflat_monolith::kernel::implementation::syscall_pci::syscall_pci_claim::syscall_pci_claim;
use veriflat_monolith::kernel::implementation::syscall_pci_bar::{syscall_map_pci_bar_2m, syscall_map_pci_bar_4k, syscall_unmap_pci_bar_2m, syscall_unmap_pci_bar_4k};
use veriflat_monolith::kernel::implementation::syscall_schedule::syscall_schedule::{syscall_schedule, ScheduleResult};
use veriflat_monolith::kernel::implementation::syscall_thread_exit::syscall_thread_exit::syscall_thread_exit;
use veriflat_monolith::kernel::implementation::syscall_unmap_4k::syscall_unmap_4k;
use veriflat_monolith::kernel::implementation::syscall_unmap_2m::syscall_unmap_2m;
use veriflat_monolith::kernel::implementation::syscall_mmap_1g::syscall_mmap_1g;
use veriflat_monolith::kernel::implementation::syscall_unmap_1g::syscall_unmap_1g;
use veriflat_monolith::{IPCPayLoad, Registers, RetValueType, TRAP_FRAME_SZ, MAX_NUM_ENDPOINT_DESCRIPTORS, NUM_CPUS, PCI_BUS_COUNT, PCI_DEVICE_COUNT, PCI_FUNCTION_COUNT};
use vstd::prelude::Tracked;
use x86::msr;
use x86::segmentation::SegmentSelector;
use x86::Ring;

use crate::cpu::{self, Cpu};
use crate::gdt::GlobalDescriptorTable;
use crate::glue::kernel;
use crate::interrupt::{self, Cycles};
use crate::platform;

const _: () = assert!(size_of::<Registers>() == 21 * 8 && TRAP_FRAME_SZ == size_of::<Registers>());

/// RFLAGS bits cleared on `syscall`: TF, IF, DF, NT, AC.
const SYSCALL_FMASK: u64 = (1 << 8) | (1 << 9) | (1 << 10) | (1 << 14) | (1 << 18);

/// RFLAGS bits that keep a return on `iretq`: `sysretq` clears RF, and with TF set it traps before
/// the first user instruction instead of after it.
const SYSRET_UNSAFE_FLAGS: u64 = (1 << 16) | (1 << 8);

/// Model errors are returned as `-(MODEL_ERROR_BASE + index)`.
const MODEL_ERROR_BASE: i64 = 100;

/// LAPIC timer cycles per scheduling tick (about 10 ms under KVM).
const TICK: Cycles = Cycles(5_000_000);

/// User addresses lie in the lower canonical half; a non-canonical read raises #GP, which
/// [`copy_from_user`] has no fixup for.
const USER_END: usize = 1 << 47;

unsafe extern "C" {
    /// The loop of [`copy_from_user`] and its exit.
    static veriflat_user_copy_begin: u8;
    static veriflat_user_copy_end: u8;
}

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

/// cpu_op states (model of this TCB). The verified model keeps each CPU in one of five states, and
/// this file makes the transitions. Interrupts are off exactly in InStep:
/// - Off: halted in [`wait_until_online`], interrupts on.
/// - Idle: the [`run_idle`] loop and its `hlt`, interrupts on.
/// - User: ring 3, interrupts on.
/// - Trap: the trampoline without this CPU's own lock, interrupts on. User to Trap at `sys_entry`
///   and the interrupt gates, which clear IF until the trampoline's `sti` after the frame is saved in
///   the running thread's slot (the trap entry: the user registers become that frame);
///   Trap to User at the `sysretq`/`iretq` of [`restore_frame`], whose `cli` (on the path from
///   [`resume_current_frame`], that function's `cli`) makes its check and the return one step; Trap to Idle when [`restore_frame`] diverts on `running_to_idle_pending`,
///   or when a syscall returns CpuIdle into [`run_idle`]. A running-to-idle IPI is acknowledged
///   only there, in [`run_idle`], once the trap path is left.
/// - InStep: the verified kernel holds this CPU's own lock, interrupts off, from its `wlock_cpu` of
///   this CPU (the lock executes `cli` when granted) until its unlock (the lock releases
///   and executes `sti`).
///
/// The running-to-idle IPI moves a CPU whose lock the killer holds from User or Trap to Idle; the
/// wake IPI moves an Off CPU to Idle after `cpu_online` published it Idle.
#[unsafe(naked)]
unsafe extern "C" fn sys_entry() -> ! {
    naked_asm!(
        "swapgs",
        "mov r10, rsp",
        // The frame slot in the page of the thread this CPU runs.
        "mov rsp, gs:{frame_top_offset}",

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

        // The frame is saved: continue on the kernel stack, and Trap runs with interrupts on. No
        // interrupt may arrive before the switch: it would push below the slot, into the thread.
        "mov rdi, rsp",
        "mov rsp, gs:{kernel_sp_offset}",
        "sti",
        "call {dispatch}",
        "jmp {resume}",

        user_ss = const GlobalDescriptorTable::USER_SS,
        user_cs = const GlobalDescriptorTable::USER_CS,
        frame_top_offset = const offset_of!(Cpu, frame_top),
        kernel_sp_offset = const offset_of!(Cpu, kernel_sp),
        dispatch = sym syscall_dispatch,
        resume = sym resume_current_frame,
    );
}

/// Restores the frame at `rsp` (the current thread's slot, or for an exception that returns to ring 3
/// its frame on the exception IST stack) and returns to it.
///
/// `sysretq` takes `rip` from `rcx` and `rflags` from `r11`, leaves both registers holding them,
/// and loads the selectors `STAR` names, so it gives exactly the state `iretq` would when the frame
/// has `rcx == rip`, `r11 == rflags`, the user `cs` and `ss`, and no [`SYSRET_UNSAFE_FLAGS`]. A
/// frame `sys_entry` saved has all of them; a thread preempted by an interrupt or starting fresh
/// almost never has. `rip` must also lie in the lower canonical half: on Intel CPUs `sysretq` to a
/// non-canonical address faults in ring 0 after the user `rsp` is already loaded. The first
/// instruction turns interrupts off, and `sysretq`/`iretq` turn them on again from the user
/// `rflags`; NMIs and machine checks taken after the user `rsp` is loaded run on IST stacks. The
/// frame is always a ring 3 frame, so both returns `swapgs` unconditionally. The exception and IRQ
/// trampolines enter at the top with interrupts on; [`resume_current_frame`], which has already
/// turned them off, enters at `veriflat_restore_frame_after_cli`, just after the `cli`.
///
/// A CPU forced from running to idle goes to the idle loop instead, which acknowledges the IPI.
/// Interrupts are off from the check to the return, so a running-to-idle IPI that arrives after the
/// check stays pending until the CPU is back in ring 3, takes it there, and comes back here through
/// the trampoline. The check is the only running-to-idle work on this path.
#[unsafe(naked)]
#[allow(named_asm_labels)]
pub(crate) unsafe extern "C" fn restore_frame() -> ! {
    naked_asm!(
        "cli",
        ".globl veriflat_restore_frame_after_cli",
        "veriflat_restore_frame_after_cli:",
        "cmp byte ptr gs:[{running_to_idle_pending}], 0",
        "jne {running_to_idle}",
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
        "mov rsp, [rsp + {user_rsp}]", // error_code, rip, cs, rflags, then the user rsp
        "swapgs",
        "sysretq",
        "3:",
        "add rsp, 8", // error_code
        "swapgs",
        "iretq",

        running_to_idle_pending = const offset_of!(Cpu, running_to_idle_pending),
        running_to_idle = sym running_to_idle_kernel_gs,

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
    );
}

/// Returns to the thread this CPU runs: restores the frame below `frame_top`, which
/// [`sync_current_frame`] keeps on the current thread's slot. The tail of every path to ring 3; a
/// pending running-to-idle request diverts it before the frame is read. Interrupts go off before
/// `rsp` moves into the thread's page: an interrupt taken there would push into the thread object.
/// That `cli` is the only one on this path: the jump enters [`restore_frame`] just after its own.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn resume_current_frame() -> ! {
    naked_asm!(
        "cli",
        "mov rsp, gs:{frame_top_offset}",
        "sub rsp, {frame_size}",
        "jmp veriflat_restore_frame_after_cli",
        frame_top_offset = const offset_of!(Cpu, frame_top),
        frame_size = const size_of::<Registers>(),
    );
}

/// The thread the verified kernel records as this CPU's current one (`Cpu::current_thread` of its own cpu object).
/// Read outside kernel steps only. Trusted: only this CPU's own steps write that field, and a killer that holds
/// this CPU's lock clears it only after the running-to-idle acknowledgement, which this CPU gives only in
/// [`run_idle`]; so between steps the value is stable, and a thread read here keeps its page until this CPU
/// acknowledges.
fn current_thread() -> Option<usize> {
    unsafe { (*cpu::get_current().verified_cpu).current_thread() }
}

/// Points `frame_top` and TSS.rsp0 at the trap-frame slot of the thread this CPU runs and returns that frame, or
/// returns `None` when the CPU runs no thread. Called after every kernel step that may have changed the thread.
fn sync_current_frame() -> Option<*mut Registers> {
    let thread = current_thread()?;
    let top = (thread + cpu::THREAD_FRAME_TOP_OFFSET) as u64;
    let cpu = cpu::get_current();
    if cpu.frame_top != top {
        cpu.frame_top = top;
        cpu.tss.rsp[0] = top;
    }
    Some((top as usize - size_of::<Registers>()) as *mut Registers)
}

/// The frame of the thread this CPU runs after a kernel step, synchronized; runs the idle loop first if the step left
/// the CPU without a thread.
fn running_frame() -> *mut Registers {
    loop {
        if let Some(frame) = sync_current_frame() {
            return frame;
        }
        run_idle();
    }
}

/// Ends the current thread after a fault in ring 3, exactly as if it had made the `thread_exit`
/// syscall. The exception trampoline has done what `sys_entry` does (`swapgs`, `cld`, the complete
/// frame, interrupts on), but the frame lies on the exception IST stack, which the next exception
/// reuses: it moves unchanged into the faulting thread's own slot, where `sys_entry` would have
/// saved it (the trap entry), and [`fault_exit_on_kernel_stack`] continues on the kernel stack.
pub(crate) fn exit_faulting_thread(name: &str, regs: &Registers) -> ! {
    log::warn!("CPU {}: {} in ring 3 at rip {:#x}; the thread exits", cpu::get_cpu_id(), name, regs.rip);
    unsafe {
        cpu::current_frame().write(*regs);
        fault_exit_on_kernel_stack()
    }
}

/// Runs [`fault_exit`] on the current CPU's kernel stack and returns to the thread the CPU then runs,
/// like the tail of `sys_entry`.
#[unsafe(naked)]
unsafe extern "C" fn fault_exit_on_kernel_stack() -> ! {
    naked_asm!(
        "mov rsp, gs:{kernel_sp_offset}",
        "call {fault_exit}",
        "jmp {resume}",
        kernel_sp_offset = const offset_of!(Cpu, kernel_sp),
        fault_exit = sym fault_exit,
        resume = sym resume_current_frame,
    );
}

/// The `thread_exit` of a faulting thread. On `CpuIdle` the thread is gone and the idle loop picks
/// the next thread, as `syscall_dispatch` does. Any other result (a kill or lock-order conflict in
/// progress) leaves the saved frame untouched: the thread re-runs the faulting instruction with its
/// own registers, faults again, and retries.
extern "C" fn fault_exit() {
    let ret = syscall_thread_exit(kernel(), Tracked::assume_new(), Tracked::assume_new(), cpu::get_cpu_id());
    if let RetValueType::CpuIdle = ret {
        run_idle();
    }
    running_frame();
}

/// Abandons the current thread for the idle loop: restarts at the top of this CPU's kernel stack,
/// which holds nothing on the way out to ring 3. Entered from [`restore_frame`] with the kernel GS
/// base and interrupts off, and turns them on once on the new stack: the idle loop runs with
/// interrupts on. The abandoned thread's frame is not touched again.
#[unsafe(naked)]
unsafe extern "C" fn running_to_idle_kernel_gs() -> ! {
    naked_asm!(
        "mov rsp, gs:{kernel_sp_offset}",
        "sti",
        "call {entry}",
        "ud2",
        kernel_sp_offset = const offset_of!(Cpu, kernel_sp),
        entry = sym running_to_idle_entry,
    );
}

/// The idle loop of a CPU forced from running to idle, then the thread it finds. Like
/// [`enter_first_thread`], but the timer already runs.
extern "C" fn running_to_idle_entry() -> ! {
    unsafe {
        run_idle();
        resume_current_frame();
    }
}

/// Runs the idle loop on the boot CPU until a thread is chosen, then enters it. Called once
/// after the verified kernel is initialized. The boot CPU runs with interrupts off until here; the
/// idle loop runs with them on.
pub unsafe fn enter_first_thread() -> ! {
    cpu::assert_user_fp_disabled();
    start_timer();
    platform::veriflat_enable_interrupts();
    run_idle();
    log::info!("entering first thread at {:#x}", (*cpu::current_frame()).rip);
    resume_current_frame();
}

/// Parks a started AP: it is Off in the verified model until `cpu_online` wakes it, then runs the
/// idle loop and enters the thread it finds. The AP trampoline turned interrupts off; an Off CPU
/// runs with them on, so its halts end at the wake IPI.
pub unsafe fn enter_off_cpu() -> ! {
    cpu::assert_user_fp_disabled();
    platform::veriflat_enable_interrupts();
    wait_until_online(cpu::get_cpu_id());
    run_idle();
    resume_current_frame();
}

/// Arms the scheduling tick and keeps it re-armed. With feature `no-timer` it arms nothing and leaves
/// `timer_on` false, for timing runs: no tick then preempts a thread, ends an idle CPU's `hlt`, or
/// makes a CPU notice an offline request. With `reset_after=` it still arms one TSC-deadline interrupt on CPU 0 at
/// the reset deadline, so a run that hangs resets itself and keeps its RAM log.
fn start_timer() {
    if cfg!(feature = "no-timer") {
        let deadline = unsafe { crate::boot::RESET_DEADLINE };
        if deadline != 0 && cpu::get_cpu_id() == 0 && !interrupt::arm_tsc_deadline(deadline) {
            log::warn!("reset_after: no TSC-deadline timer, so a hung no-timer run does not reset itself");
        }
        return;
    }
    cpu::get_current().timer_on = true;
    interrupt::set_timer(TICK);
}

/// LAPIC timer tick. From user mode it preempts the running thread; in the kernel, where it arrives
/// outside a step (in a trampoline, the idle loop, or its `hlt`), it only re-arms the timer. It
/// sets `wake_seen` either way: the idle loop waits for ticks too.
pub fn timer_interrupt(regs: &mut Registers) {
    interrupt::end_of_interrupt();
    crate::boot::check_reset_deadline();
    cpu::set_wake_seen();
    if cpu::get_current().timer_on {
        interrupt::set_timer(TICK);
    }
    if from_user(regs) {
        schedule_from_running();
    }
}

/// Wake-up IPI (`platform::veriflat_send_ipi`, sent by `cpu_online`). It ends a `hlt`, the one of
/// [`wait_until_online`] or of the idle loop, and sets `wake_seen`, so a halt that has not started
/// yet returns at once (`platform::veriflat_halt_until_ipi`). An offline request sends no IPI: its
/// target notices the request at its next timer tick or syscall.
pub fn wake_interrupt(_regs: &mut Registers) {
    interrupt::end_of_interrupt();
    cpu::set_wake_seen();
}

fn from_user(regs: &Registers) -> bool {
    regs.cs & 3 == 3
}

/// Writes a verified result into `regs`, the frame of the thread this CPU returns to: the model's
/// trap-return-values-written event of this CPU.
fn encode(regs: *mut Registers, ret: RetValueType) {
    use RetValueType::*;
    let (rax, rdx, rsi): (i64, u64, u64) = match ret {
        SuccessUsize { value } => (value as i64, 0, 0),
        SuccessSeqUsize { .. } => (0, 0, 0),
        SuccessPairUsize { value1, value2 } => (value1 as i64, value2 as u64, 0),
        SuccessThreeUsize { value1, value2, value3 } => (value1 as i64, value2 as u64, value3 as u64),
        Success => (0, 0, 0),
        other => (-(MODEL_ERROR_BASE + error_index(other) as i64), 0, 0),
    };
    unsafe {
        (*regs).rax = rax as u64;
        (*regs).rdx = rdx;
        (*regs).rsi = rsi;
    }
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
        ErrorContainerZombie => 42,
        ErrorIpcCalleeExited => 43,
        ErrorIpcCallerKilled => 44,
        ErrorInvalidChild => 45,
        ErrorIommuIovaAlreadyMapped => 46,
        ErrorIommuIovaNotMapped => 47,
        ErrorIommuVaNotMapped => 48,
        ErrorContainerLockOrderConflict => 49,
        ErrorIpcRangeNotUser => 50,
        ErrorIpcPciBarMapped => 51,
        ErrorIpcPciReceiverFull => 52,
        ErrorPciNotRootProcess => 53,
        ErrorPciAlreadyOwned => 54,
        ErrorPciFunctionArrayFull => 55,
        ErrorPciBarSlotInvalid => 56,
        ErrorPciBarNotMapped => 57,
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

/// Dispatches a syscall of the thread whose frame is `regs` (its slot). On return `frame_top` is on
/// the slot of the thread to resume, which is the caller unless the call blocked, yielded, or handed
/// the CPU off; `regs` is not touched after a kernel step that may have ended the caller.
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
        vsys::NR_DEBUG_EXIT => unsafe { crate::boot::exit_qemu(ns16550a::ramlog::REASON_EXIT, a1 as u32) },
        vsys::NR_DEBUG_DMA_DEVICE => {
            regs.rax = crate::iommu::dma_test_device().map_or(vsys::ERR_INVALID_SYSCALL, |bdf| bdf as isize) as u64;
            return;
        }
        vsys::NR_PCI_INFO => {
            // Reads the loader's PCI record only, outside any kernel step.
            let bdf = (a1 < 256 && a2 < 32 && a3 < 8).then(|| ((a1 << 8) | (a2 << 3) | a3) as u16);
            let found = bdf.and_then(|bdf| crate::boot::get_boot_info().pci_devices.iter().find(|d| d.bdf == bdf));
            match found {
                Some(d) => {
                    regs.rax = (d.class as u64) << 48 | (d.subclass as u64) << 40 | (d.vendor as u64) << 16 | d.device as u64;
                    regs.rdx = d.bar0_base;
                    regs.rsi = d.bar0_pages;
                }
                None => {
                    set_trap_error(regs, vsys::ERR_INVALID_ARGUMENT);
                    (regs.rdx, regs.rsi) = (0, 0);
                }
            }
            return;
        }
        vsys::NR_PCI_BAR => {
            // Reads the loader's BAR slot record only, outside any kernel step. The glue built the kernel's BAR table from
            // this list in this order, so slot `a1` here is BAR-table index `a1` of `map_pci_bar_4k/2m`.
            match crate::boot::get_boot_info().bar_slots.get(a1) {
                Some(b) => {
                    regs.rax = (b.vendor as u64) << 40 | (b.device as u64) << 24 | (b.bdf as u64) << 8 | b.bar as u64;
                    (regs.rdx, regs.rsi) = (b.base, b.size);
                }
                None => {
                    set_trap_error(regs, vsys::ERR_INVALID_ARGUMENT);
                    (regs.rdx, regs.rsi) = (0, 0);
                }
            }
            return;
        }
        vsys::NR_DEBUG_DMA_PROBE => {
            let result = match a1 {
                0 => crate::iommu::dma_probe(),
                1 => crate::iommu::dma_write_probe(),
                _ => None,
            };
            regs.rax = result.map_or(vsys::ERR_INVALID_SYSCALL, |reason| reason as isize) as u64;
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
            schedule_from_running();
            return;
        }
        vsys::NR_ALLOC_QUOTA_4K => syscall_alloc_quota_4k(k, t!(), t!(), cpu_id, a1),
        vsys::NR_ALLOC_THREAD_QUOTA_4K => syscall_alloc_thread_quota_4k(k, t!(), t!(), cpu_id, a1),
        vsys::NR_ALLOC_QUOTA_2M => syscall_alloc_quota_2m(k, t!(), t!(), cpu_id, a1),
        vsys::NR_ALLOC_THREAD_QUOTA_2M => syscall_alloc_thread_quota_2m(k, t!(), t!(), cpu_id, a1),
        vsys::NR_ALLOC_QUOTA_1G => syscall_alloc_quota_1g(k, t!(), t!(), cpu_id, a1),
        vsys::NR_ALLOC_THREAD_QUOTA_1G => syscall_alloc_thread_quota_1g(k, t!(), t!(), cpu_id, a1),
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
        vsys::NR_THREAD_EXIT => syscall_thread_exit(k, t!(), t!(), cpu_id),
        vsys::NR_KILL_PROCESS => syscall_kill_process(k, t!(), t!(), cpu_id, a1),
        vsys::NR_KILL_CONTAINER => syscall_kill_container(k, t!(), t!(), cpu_id, a1),
        vsys::NR_MMAP_4K => syscall_mmap_4k(k, t!(), t!(), cpu_id, a1, a2).0,
        vsys::NR_MERGE_2M => syscall_merge_2m(k, t!(), t!(), cpu_id, a1).0,
        vsys::NR_SPLIT_2M => syscall_split_2m(k, t!(), t!(), cpu_id, a1),
        vsys::NR_UNMAP_4K => syscall_unmap_4k(k, t!(), t!(), cpu_id, a1, a2),
        vsys::NR_MMAP_2M => syscall_mmap_2m(k, t!(), t!(), cpu_id, a1, a2).0,
        vsys::NR_UNMAP_2M => syscall_unmap_2m(k, t!(), t!(), cpu_id, a1, a2).0,
        vsys::NR_MMAP_1G => syscall_mmap_1g(k, t!(), t!(), cpu_id, a1, a2).0,
        vsys::NR_UNMAP_1G => syscall_unmap_1g(k, t!(), t!(), cpu_id, a1, a2).0,
        vsys::NR_IOMMU_MAP_4K => syscall_iommu_map_4k(k, t!(), t!(), cpu_id, a1, a2, a3),
        vsys::NR_IOMMU_UNMAP_4K => syscall_iommu_unmap_4k(k, t!(), t!(), cpu_id, a1, a2),
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
            syscall_send_empty(k, t!(), t!(), cpu_id, a1)
        }
        vsys::NR_RECEIVE_EMPTY => {
            require!(endpoint_ok(a1));
            syscall_receive_empty(k, t!(), t!(), cpu_id, a1)
        }
        vsys::NR_SEND_EMPTY_NO_BLOCK => {
            require!(endpoint_ok(a1));
            syscall_send_empty_no_block(k, t!(), t!(), cpu_id, a1)
        }
        vsys::NR_RECEIVE_EMPTY_NO_BLOCK => {
            require!(endpoint_ok(a1));
            syscall_receive_empty_no_block(k, t!(), t!(), cpu_id, a1)
        }
        // A direct handoff makes the thread switched to this CPU's current thread, so the common
        // `encode` below delivers the result into that thread's frame.
        vsys::NR_CALL => {
            require!(endpoint_ok(a1));
            syscall_call(k, t!(), t!(), cpu_id, a1, IPCPayLoad::Empty)
        }
        vsys::NR_CALL_USIZE => {
            require!(endpoint_ok(a1));
            syscall_call(k, t!(), t!(), cpu_id, a1, IPCPayLoad::Usize { value: a2 })
        }
        vsys::NR_RECEIVE_CALL => {
            require!(endpoint_ok(a1));
            syscall_receive_call(k, t!(), t!(), cpu_id, a1)
        }
        vsys::NR_REPLY_AND_RECEIVE => {
            require!(endpoint_ok(a1));
            syscall_reply_and_receive(k, t!(), t!(), cpu_id, a1, IPCPayLoad::Empty)
        }
        vsys::NR_REPLY_AND_RECEIVE_USIZE => {
            require!(endpoint_ok(a1));
            syscall_reply_and_receive(k, t!(), t!(), cpu_id, a1, IPCPayLoad::Usize { value: a2 })
        }
        vsys::NR_SEND_CPU => {
            require!(endpoint_ok(a1) && a2 < NUM_CPUS);
            syscall_send_cpu(k, t!(), t!(), cpu_id, a1, a2)
        }
        vsys::NR_RECEIVE_CPU => {
            require!(endpoint_ok(a1));
            syscall_receive_cpu(k, t!(), t!(), cpu_id, a1)
        }
        vsys::NR_SEND_PCI => {
            require!(endpoint_ok(a1) && bdf_ok(a2, a3, a4));
            syscall_send_pci(k, t!(), t!(), cpu_id, a1, a2 as u8, a3 as u8, a4 as u8)
        }
        vsys::NR_RECEIVE_PCI => {
            require!(endpoint_ok(a1) && bdf_ok(a2, a3, a4));
            syscall_receive_pci(k, t!(), t!(), cpu_id, a1, a2 as u8, a3 as u8, a4 as u8)
        }
        vsys::NR_SEND_ENDPOINT => {
            require!(endpoint_ok(a1) && endpoint_ok(a2));
            syscall_send_endpoint(k, t!(), t!(), cpu_id, a1, a2)
        }
        vsys::NR_RECEIVE_ENDPOINT => {
            require!(endpoint_ok(a1) && endpoint_ok(a2));
            syscall_receive_endpoint(k, t!(), t!(), cpu_id, a1, a2)
        }
        vsys::NR_SEND_PAGES => {
            require!(endpoint_ok(a1));
            syscall_send_pages(k, t!(), t!(), cpu_id, a1, a2, a3)
        }
        vsys::NR_RECEIVE_PAGES => {
            require!(endpoint_ok(a1));
            syscall_receive_pages(k, t!(), t!(), cpu_id, a1, a2, a3)
        }
        vsys::NR_PCI_ATTACH_DMA => {
            require!(bdf_ok(a1, a2, a3));
            syscall_pci_attach_dma(k, t!(), t!(), cpu_id, a1, a2, a3)
        }
        vsys::NR_PCI_CLAIM => {
            require!(bdf_ok(a1, a2, a3));
            syscall_pci_claim(k, t!(), t!(), cpu_id, a1, a2, a3)
        }
        // The BAR calls take any argument: a bad slot, page or chunk index, or VA is a verified result.
        vsys::NR_MAP_PCI_BAR_4K => syscall_map_pci_bar_4k(k, t!(), t!(), cpu_id, a1, a2, a3),
        vsys::NR_MAP_PCI_BAR_2M => syscall_map_pci_bar_2m(k, t!(), t!(), cpu_id, a1, a2, a3),
        vsys::NR_UNMAP_PCI_BAR_4K => syscall_unmap_pci_bar_4k(k, t!(), t!(), cpu_id, a1),
        vsys::NR_UNMAP_PCI_BAR_2M => syscall_unmap_pci_bar_2m(k, t!(), t!(), cpu_id, a1),
        _ => {
            set_trap_error(regs, vsys::ERR_INVALID_SYSCALL);
            return;
        }
    };

    if let RetValueType::CpuIdle = ret {
        // The caller blocked (its frame stays in its thread) or exited (its thread is gone). Pick the next thread.
        run_idle();
    } else {
        encode(running_frame(), ret);
    }
}

/// Copies `len` bytes from `src` to `dst` and returns how many it copied: fewer when a read of `src`
/// page faults, and `page_fault` resumes at the exit.
#[unsafe(naked)]
unsafe extern "C" fn copy_from_user(dst: *mut u8, src: *const u8, len: usize) -> usize {
    naked_asm!(
        "xor eax, eax",
        ".globl veriflat_user_copy_begin",
        "veriflat_user_copy_begin:",
        "2:",
        "cmp rax, rdx",
        "je 3f",
        "mov cl, byte ptr [rsi + rax]",
        "mov byte ptr [rdi + rax], cl",
        "inc rax",
        "jmp 2b",
        "3:",
        ".globl veriflat_user_copy_end",
        "veriflat_user_copy_end:",
        "ret",
    );
}

/// Where a kernel page fault at `regs.rip` resumes: the exit of [`copy_from_user`] for a fault in its loop.
pub fn user_copy_fixup(regs: &Registers) -> Option<u64> {
    let (begin, end) = (&raw const veriflat_user_copy_begin as u64, &raw const veriflat_user_copy_end as u64);
    (!from_user(regs) && (begin..end).contains(&regs.rip)).then_some(end)
}

/// Whether the loaded page table maps `va` present and user-accessible at every level, so the
/// calling thread could read it itself. Page-table pages are identity-mapped in the kernel half.
fn user_readable(va: usize) -> bool {
    const PRESENT_USER: u64 = 0b101;
    const HUGE: u64 = 1 << 7;
    const ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;
    let cr3: u64;
    unsafe { core::arch::asm!("mov {}, cr3", out(reg) cr3, options(nomem, nostack, preserves_flags)) };
    let mut table = cr3 & ADDR_MASK;
    for level in (0..4).rev() {
        let entry = unsafe { core::ptr::read_volatile((table as *const u64).add((va >> (12 + 9 * level)) & 511)) };
        if entry & PRESENT_USER != PRESENT_USER {
            return false;
        }
        if level == 0 || (level < 3 && entry & HUGE != 0) {
            return true;
        }
        table = entry & ADDR_MASK;
    }
    false
}

fn debug_print(data: usize, len: usize) {
    let len = len.min(4096);
    if data.checked_add(len).is_none_or(|end| end > USER_END) {
        return;
    }
    // Reads only bytes whose pages the thread's own page table maps present and user-accessible.
    if len > 0 && !(data & !0xfff..data + len).step_by(4096).all(user_readable) {
        log::info!("[user@{}] <buffer {:#x}+{:#x} not user-readable>", cpu::get_cpu_id(), data, len);
        return;
    }
    let mut buffer = [0u8; 4096];
    let copied = unsafe { copy_from_user(buffer.as_mut_ptr(), data as *const u8, len) };
    match core::str::from_utf8(&buffer[..copied]) {
        _ if copied < len => log::info!("[user@{}] <page fault reading {:#x}>", cpu::get_cpu_id(), data + copied),
        Ok(s) => log::info!("[user@{}] {}", cpu::get_cpu_id(), s.trim_end()),
        Err(_) => log::info!("[user@{}] <{} non-UTF-8 bytes>", cpu::get_cpu_id(), len),
    }
}

/// `sys_schedule` or a timer tick from a running thread: the offline check, then a context switch.
fn schedule_from_running() {
    let cpu_id = cpu::get_cpu_id();
    let k = kernel();
    if let OfflineCheckResult::Off = cpu_offline_check(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id).0 {
        wait_until_online(cpu_id);
        run_idle();
        return;
    }
    match syscall_schedule(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id) {
        ScheduleResult::Switched { syscall_return, .. } => {
            let frame = running_frame();
            if let Some(ret) = syscall_return {
                encode(frame, ret);
            }
        }
        ScheduleResult::Continue => {
            running_frame();
        }
        ScheduleResult::Idle => run_idle(),
    }
}

/// The idle loop of a CPU without a running thread; it runs with interrupts on. Returns once the CPU
/// runs a thread and `frame_top` is on that thread's slot. A forced running-to-idle transition ends here:
/// through [`restore_frame`], or from a syscall or tick whose step found this CPU marked.
///
/// This is the only place that acknowledges a running-to-idle IPI
/// (`platform::acknowledge_running_to_idle`): on entry, where this CPU has left the trap path of the
/// thread it ran, and at the top of every iteration, for an IPI that lands inside this loop, between
/// steps or at the `hlt`. The acknowledgement clears `running_to_idle_pending` together with the owed
/// flag; the handler sets both, so outside it they are equal and the entry needs no other clear. Until
/// the acknowledgement the sender holds this CPU's lock, so every step here returns at once
/// (`syscall_schedule` with Idle, `rebalance_pull` with Nothing) and the halt does not sleep while the
/// owed flag is set (`platform::veriflat_halt_until_ipi`): the next iteration acknowledges. An IPI that
/// lands after the step that switched to a thread sets `running_to_idle_pending`, so
/// [`restore_frame`] diverts back here and the entry acknowledges.
fn run_idle() {
    platform::acknowledge_running_to_idle();
    let cpu_id = cpu::get_cpu_id();
    let k = kernel();
    loop {
        platform::acknowledge_running_to_idle();
        if let OfflineCheckResult::Off = cpu_offline_check(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id).0 {
            wait_until_online(cpu_id);
            continue;
        }
        match syscall_schedule(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id) {
            ScheduleResult::Switched { syscall_return, .. } => {
                // No acknowledgement can have happened since the step, so the thread it chose is still current.
                let frame = sync_current_frame().expect("switched to no thread");
                if let Some(ret) = syscall_return {
                    encode(frame, ret);
                }
                return;
            }
            // A killed head was dropped; look again.
            ScheduleResult::Continue => continue,
            ScheduleResult::Idle => {}
        }
        match rebalance_pull(k, Tracked::assume_new(), Tracked::assume_new(), cpu_id) {
            RebalanceResult::Pulled { .. } => continue,
            // Wait for the next tick or IPI; another CPU may queue a thread here meanwhile.
            RebalanceResult::Nothing => platform::veriflat_halt_until_ipi(),
        }
    }
}

/// A CPU that is Off: its timer stops and `cpu_online_resume` halts it, with interrupts on, until
/// `cpu_online` publishes it Idle again.
fn wait_until_online(cpu_id: usize) {
    log::info!("CPU {} is offline", cpu_id);
    cpu::get_current().timer_on = false;
    interrupt::disarm_timer();
    while let OnlineResumeResult::StillOff = cpu_online_resume(kernel(), Tracked::assume_new(), Tracked::assume_new(), cpu_id) {}
    log::info!("CPU {} is online", cpu_id);
    start_timer();
}
