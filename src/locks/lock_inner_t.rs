use vstd::prelude::*;
use crate::define::*;
use core::sync::atomic::*;
use crate::locks::*;

// Platform implementation: clear and set the calling cpu's interrupt flag.
unsafe extern "C" {
    fn veriflat_disable_interrupts();
    fn veriflat_enable_interrupts();
}

// `SpinWord` layout: bit 0 is the write bit, bit 1 the kill mark, bits 2-3 the tag of the recorded dynamic owner, and the
// remaining bits the depth of a `LockOwnerId::Some` owner.
const WORD_WRITER: usize = 1;
const WORD_KILLED: usize = 2;
const WORD_OWNER_SOME: usize = 1 << 2;
const WORD_OWNER_HIGH: usize = 2 << 2;
const WORD_OWNER_TAG_MASK: usize = 3 << 2;
const WORD_OWNER_DEPTH_SHIFT: usize = 4;

fn encode_owner(owner: LockOwnerId) -> usize {
    match owner {
        LockOwnerId::None => 0,
        LockOwnerId::Some(depth) => {
            debug_assert!(depth >> (usize::BITS as usize - WORD_OWNER_DEPTH_SHIFT) == 0, "owner depth exceeds the lock word");
            WORD_OWNER_SOME | (depth << WORD_OWNER_DEPTH_SHIFT)
        }
        LockOwnerId::High => WORD_OWNER_HIGH,
    }
}

fn decode_owner(word: usize) -> LockOwnerId {
    match word & WORD_OWNER_TAG_MASK {
        WORD_OWNER_SOME => LockOwnerId::Some(word >> WORD_OWNER_DEPTH_SHIFT),
        WORD_OWNER_HIGH => LockOwnerId::High,
        _ => LockOwnerId::None,
    }
}

// `PerCpuReaderSlots` slot values: free, read-held by the slot's cpu, write-held; a waiting writer may add the pending
// bit to a busy slot, which keeps a newly freed slot from new readers until that writer takes it.
// Slot 0 may also carry the kill mark.
const SLOT_FREE: usize = 0;
const SLOT_READER: usize = 1;
const SLOT_WRITER: usize = 2;
const SLOT_PENDING: usize = 4;
const SLOT_KILLED: usize = 8;

verus! {
/// TCB: test-and-test-and-set lock word of an object taken only by writers. Every method takes `&self` and stays out of
/// line, so a caller's `&mut` to the enclosing lock never lets the compiler keep the word in a register across a spin.
/// Only the holder changes the word while the write bit is set.
#[verifier::external_body]
pub struct SpinWord(AtomicUsize);

impl SpinLockInner for SpinWord {
    #[verifier::external_body]
    fn new_unlocked() -> Self { SpinWord(AtomicUsize::new(0)) }

    #[verifier::external_body]
    fn new_wlocked_for_retype(owner: LockOwnerId) -> Self { SpinWord(AtomicUsize::new(WORD_WRITER | encode_owner(owner))) }

    #[verifier::external_body]
    #[inline(never)]
    fn wlock(&self) {
        loop {
            let v = self.0.load(Ordering::Relaxed);
            if v & WORD_WRITER == 0 && self.0.compare_exchange_weak(v, v | WORD_WRITER, Ordering::Acquire, Ordering::Relaxed).is_ok() { return; }
            core::hint::spin_loop();
        }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn wunlock(&self) {
        let v = self.0.load(Ordering::Relaxed);
        debug_assert!(v & WORD_WRITER != 0, "wunlock called on object that is not write-locked");
        self.0.store(v & !WORD_WRITER, Ordering::Release);
    }
}

impl KillableLockInner for SpinWord {
    #[verifier::external_body]
    #[inline(never)]
    fn wlock_unless_killed(&self) -> bool {
        loop {
            let v = self.0.load(Ordering::Relaxed);
            if v & WORD_KILLED != 0 {
                fence(Ordering::Acquire);
                return false;
            }
            if v & WORD_WRITER == 0 && self.0.compare_exchange_weak(v, v | WORD_WRITER, Ordering::Acquire, Ordering::Relaxed).is_ok() { return true; }
            core::hint::spin_loop();
        }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn wlock_unless_killed_cli(&self) -> bool {
        loop {
            let v = self.0.load(Ordering::Relaxed);
            if v & WORD_KILLED != 0 {
                fence(Ordering::Acquire);
                return false;
            }
            if v & WORD_WRITER == 0 {
                // The interrupt flag is clear before the acquisition can become visible to another cpu.
                unsafe { veriflat_disable_interrupts(); }
                if self.0.compare_exchange_weak(v, v | WORD_WRITER, Ordering::Acquire, Ordering::Relaxed).is_ok() { return true; }
                unsafe { veriflat_enable_interrupts(); }
            }
            core::hint::spin_loop();
        }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn try_wlock_and_mark_kill(&self) -> bool {
        loop {
            let v = self.0.load(Ordering::Relaxed);
            if v & WORD_KILLED != 0 {
                fence(Ordering::Acquire);
                return false;
            }
            if v & WORD_WRITER == 0 && self.0.compare_exchange_weak(v, v | WORD_WRITER | WORD_KILLED, Ordering::Acquire, Ordering::Relaxed).is_ok() { return true; }
            core::hint::spin_loop();
        }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn mark_kill(&self) {
        debug_assert!(self.0.load(Ordering::Relaxed) & WORD_WRITER != 0, "mark_kill called on object that is not write-locked");
        self.0.fetch_or(WORD_KILLED, Ordering::Release);
    }

    #[verifier::external_body]
    #[inline(never)]
    fn unkill(&self) {
        debug_assert!(self.0.load(Ordering::Relaxed) & (WORD_WRITER | WORD_KILLED) == WORD_WRITER | WORD_KILLED, "unkill called on object that is not write-locked and marked");
        self.0.fetch_and(!WORD_KILLED, Ordering::Release);
    }

    #[verifier::external_body]
    #[inline(never)]
    fn wunlock_sti(&self) {
        let v = self.0.load(Ordering::Relaxed);
        debug_assert!(v & WORD_WRITER != 0, "wunlock_sti called on object that is not write-locked");
        self.0.store(v & !WORD_WRITER, Ordering::Release);
        unsafe { veriflat_enable_interrupts(); }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn dynamic_wlock(&self, requested: LockOwnerId) -> DynamicWLockOutcome {
        loop {
            let v = self.0.load(Ordering::Relaxed);
            if v & WORD_KILLED != 0 {
                fence(Ordering::Acquire);
                return DynamicWLockOutcome::Killed;
            }
            if v & WORD_WRITER != 0 {
                let holder = decode_owner(v);
                if lock_owner_lt(holder, requested) { return DynamicWLockOutcome::DepthConflict(holder); }
            } else if self.0.compare_exchange_weak(v, WORD_WRITER | encode_owner(requested), Ordering::Acquire, Ordering::Relaxed).is_ok() {
                return DynamicWLockOutcome::Acquired;
            }
            core::hint::spin_loop();
        }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn dynamic_wunlock(&self) {
        let v = self.0.load(Ordering::Relaxed);
        debug_assert!(v & WORD_WRITER != 0, "dynamic_wunlock called on object that is not write-locked");
        self.0.store(v & WORD_KILLED, Ordering::Release);
    }
}

/// TCB: one reader slot of a `PerCpuReaderSlots` lock on its own cache line.
#[verifier::external_body]
#[repr(C, align(64))]
struct ReaderSlot(AtomicUsize);

/// TCB: big-reader lock. A reader takes only the slot of its own cpu; a writer takes every slot in increasing cpu order,
/// so a reader never touches a cache line written by another reader. Slot 0 alone carries the kill mark, which only a
/// writer holding every slot sets or clears; readers do not check it.
#[verifier::external_body]
#[repr(C, align(64))]
pub struct PerCpuReaderSlots {
    slots: [ReaderSlot; NUM_CPUS],
}

impl PerCpuReaderSlots {
    /// While slot `i` is busy the writer keeps the pending mark set on it, so the slot never reads free again before the
    /// writer takes it and no new reader overtakes the waiting writer. The kill mark of slot 0 is kept.
    #[verifier::external_body]
    #[inline(always)]
    fn wlock_slot(&self, i: usize) {
        let slot = &self.slots[i].0;
        loop {
            let v = slot.load(Ordering::Relaxed);
            let busy = v & !(SLOT_PENDING | SLOT_KILLED);
            if busy == SLOT_FREE && slot.compare_exchange_weak(v, SLOT_WRITER | (v & SLOT_KILLED), Ordering::Acquire, Ordering::Relaxed).is_ok() { return; }
            if busy != SLOT_FREE && v & SLOT_PENDING == 0 { slot.fetch_or(SLOT_PENDING, Ordering::Relaxed); }
            core::hint::spin_loop();
        }
    }

    /// Takes slot 0 unless it carries the kill mark, then every other slot; `false` leaves the lock unchanged. With `cli`
    /// the interrupt flag is clear before the slot 0 acquisition can become visible to another cpu.
    #[verifier::external_body]
    #[inline(always)]
    fn wlock_unless_killed_with(&self, cli: bool) -> bool {
        let slot = &self.slots[0].0;
        loop {
            let v = slot.load(Ordering::Relaxed);
            if v & SLOT_KILLED != 0 {
                fence(Ordering::Acquire);
                return false;
            }
            if v & !SLOT_PENDING == SLOT_FREE {
                if cli { unsafe { veriflat_disable_interrupts(); } }
                if slot.compare_exchange_weak(v, SLOT_WRITER, Ordering::Acquire, Ordering::Relaxed).is_ok() { break; }
                if cli { unsafe { veriflat_enable_interrupts(); } }
            } else if v & SLOT_PENDING == 0 {
                slot.fetch_or(SLOT_PENDING, Ordering::Relaxed);
            }
            core::hint::spin_loop();
        }
        let mut i = 1;
        while i < NUM_CPUS {
            self.wlock_slot(i);
            i += 1;
        }
        true
    }
}

impl SpinLockInner for PerCpuReaderSlots {
    #[verifier::external_body]
    fn new_unlocked() -> Self { PerCpuReaderSlots { slots: [const { ReaderSlot(AtomicUsize::new(SLOT_FREE)) }; NUM_CPUS] } }

    #[verifier::external_body]
    fn new_wlocked_for_retype(owner: LockOwnerId) -> Self {
        debug_assert!(owner == LockOwnerId::None, "a per-cpu reader lock records no dynamic owner");
        PerCpuReaderSlots { slots: [const { ReaderSlot(AtomicUsize::new(SLOT_WRITER)) }; NUM_CPUS] }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn wlock(&self) {
        let mut i = 0;
        while i < NUM_CPUS {
            self.wlock_slot(i);
            i += 1;
        }
    }

    /// Only slot 0 keeps its kill mark; no other cpu changes the mark while the writer holds slot 0.
    #[verifier::external_body]
    #[inline(never)]
    fn wunlock(&self) {
        let v = self.slots[0].0.load(Ordering::Relaxed);
        debug_assert!(v & !(SLOT_PENDING | SLOT_KILLED) == SLOT_WRITER, "wunlock called on object that is not write-locked");
        self.slots[0].0.store(v & SLOT_KILLED, Ordering::Release);
        let mut i = 1;
        while i < NUM_CPUS {
            debug_assert!(self.slots[i].0.load(Ordering::Relaxed) & !SLOT_PENDING == SLOT_WRITER, "wunlock called on object that is not write-locked");
            self.slots[i].0.store(SLOT_FREE, Ordering::Release);
            i += 1;
        }
    }
}

impl RwLockInner for PerCpuReaderSlots {
    #[verifier::external_body]
    #[inline(never)]
    fn rlock(&self, cpu_id: CpuId) {
        let slot = &self.slots[cpu_id].0;
        loop {
            let v = slot.load(Ordering::Relaxed);
            if v & !SLOT_KILLED == SLOT_FREE && slot.compare_exchange_weak(v, v | SLOT_READER, Ordering::Acquire, Ordering::Relaxed).is_ok() { return; }
            core::hint::spin_loop();
        }
    }

    /// Clearing only the reader bit keeps a waiting writer's pending mark and the kill mark on the slot.
    #[verifier::external_body]
    #[inline(never)]
    fn runlock(&self, cpu_id: CpuId) {
        debug_assert!(self.slots[cpu_id].0.load(Ordering::Relaxed) & !(SLOT_PENDING | SLOT_KILLED) == SLOT_READER, "runlock called on object that is not read-locked");
        self.slots[cpu_id].0.fetch_and(!SLOT_READER, Ordering::Release);
    }

    /// The caller's own slot turns into a reader before any other slot is freed, and a later writer stops at that slot, so
    /// the caller stays the only reader. Slot 0 keeps its kill mark.
    #[verifier::external_body]
    #[inline(never)]
    fn downgrade(&self, cpu_id: CpuId) {
        let killed = self.slots[0].0.load(Ordering::Relaxed) & SLOT_KILLED;
        self.slots[cpu_id].0.store(if cpu_id == 0 { SLOT_READER | killed } else { SLOT_READER }, Ordering::Release);
        let mut i = 0;
        while i < NUM_CPUS {
            if i != cpu_id { self.slots[i].0.store(if i == 0 { killed } else { SLOT_FREE }, Ordering::Release); }
            i += 1;
        }
    }
}

/// The kill mark lives in slot 0, so a marked lock fails at slot 0 before any other slot is touched. A per-cpu reader
/// lock records no dynamic owner, so a dynamic acquisition never reports a depth conflict.
impl KillableLockInner for PerCpuReaderSlots {
    #[verifier::external_body]
    #[inline(never)]
    fn wlock_unless_killed(&self) -> bool { self.wlock_unless_killed_with(false) }

    #[verifier::external_body]
    #[inline(never)]
    fn wlock_unless_killed_cli(&self) -> bool { self.wlock_unless_killed_with(true) }

    /// The mark is set only once every slot is held, so no reader holds the lock when the mark becomes visible.
    #[verifier::external_body]
    #[inline(never)]
    fn try_wlock_and_mark_kill(&self) -> bool {
        if !self.wlock_unless_killed_with(false) { return false; }
        self.slots[0].0.fetch_or(SLOT_KILLED, Ordering::Release);
        true
    }

    #[verifier::external_body]
    #[inline(never)]
    fn mark_kill(&self) {
        debug_assert!(self.slots[0].0.load(Ordering::Relaxed) & SLOT_WRITER != 0, "mark_kill called on object that is not write-locked");
        self.slots[0].0.fetch_or(SLOT_KILLED, Ordering::Release);
    }

    #[verifier::external_body]
    #[inline(never)]
    fn unkill(&self) {
        debug_assert!(self.slots[0].0.load(Ordering::Relaxed) & (SLOT_WRITER | SLOT_KILLED) == SLOT_WRITER | SLOT_KILLED, "unkill called on object that is not write-locked and marked");
        self.slots[0].0.fetch_and(!SLOT_KILLED, Ordering::Release);
    }

    #[verifier::external_body]
    #[inline(never)]
    fn wunlock_sti(&self) {
        self.wunlock();
        unsafe { veriflat_enable_interrupts(); }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn dynamic_wlock(&self, _requested: LockOwnerId) -> DynamicWLockOutcome {
        if self.wlock_unless_killed_with(false) { DynamicWLockOutcome::Acquired } else { DynamicWLockOutcome::Killed }
    }

    #[verifier::external_body]
    #[inline(never)]
    fn dynamic_wunlock(&self) { self.wunlock() }
}
}

// Layout contract: a lock word is one machine word, and the per-cpu reader lock is one cache line per cpu.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(core::mem::size_of::<SpinWord>() == 8);
const _: () = assert!(core::mem::align_of::<PerCpuReaderSlots>() == 64);
const _: () = assert!(core::mem::size_of::<PerCpuReaderSlots>() == NUM_CPUS * 64);
