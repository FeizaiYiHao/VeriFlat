//! The application/driver exchange of the two-process E810 shapes, which both kernels' front ends run unchanged:
//! an application thread and the driver thread that owns a queue pair share one `Shared` block (two
//! single-producer single-consumer rings of frame entries and a few counters, in memory both processes map).
//!
//! - Two-core ring shape: the driver thread loops `Driver::control` + `Driver::step` on a core of its own while the
//!   application thread loops `App::step` on another; nothing but the shared block passes between them (after
//!   Atmosphere's ixgbe ring-buffer tests, which also hand packet buffers through rings in shared memory).
//! - IPC shape: the application thread calls the driver once per batch; each call runs one `Driver::control` +
//!   `Driver::step` on the caller's request and answers.
//!
//! Modes, one per phase (`App::begin` posts a phase command, the driver acknowledges it in `control`):
//! - `tx`: the application writes up to `batch` frames per step into its Tx slots (each with a sequence number) and
//!   pushes them; the driver queues them on its Tx queue. A slot is free again once the device reported it sent.
//! - `rx`: the driver takes up to `batch` received frames per step from its Rx queues and pushes them in place (zero
//!   copy); the application reads each frame's sequence number and releases it; the driver re-arms released frames.
//! - `fwd`: as `rx`, but the application rewrites each frame's source and destination MAC (the per-packet work of
//!   Atmosphere's `run_fwd_udptest`) and pushes it back for transmission from its Rx buffer (zero copy); the driver
//!   re-arms a buffer once the device reported its frame sent.
//! - `maglev`: as `fwd`, with the per-packet work of Atmosphere's maglev benchmark instead (`Maglev::process`, then
//!   the MAC rewrite for a frame with a backend), as `bench::run_forwarder`.
//!
//! Data paths (`Path`, fixed per application and carried in each phase command):
//! - `Zero` (above): frames stay in the memory both processes map; ring entries point at them.
//! - `Copy`: the application keeps private buffers and the shared memory is a bounce area. Tx: the application builds
//!   each frame in a private slot and copies it into a shared Tx slot (one copy). Rx: it copies each received frame
//!   out of the shared Rx buffer into a private buffer (one copy), works on the copy and releases the shared buffer at
//!   once. Fwd: one copy out, the work on the private copy, one copy into a shared Tx slot; the Rx buffer is released
//!   at the copy out, the Tx slot once the device reported it sent.
//! - `Map`: the pages of the frames change owner. Both sides defer what makes a frame visible to the other until the
//!   front end moved the frame's pages (`App::commit`, `Driver::commit` after `pending`/`handled`), and the driver runs
//!   a front-end hook after it read what the application released and before it re-arms or transmits anything
//!   (`Driver::control_with`, `Driver::step_with`), where the front end maps the pages the application gave back for
//!   the device again. Mode `tx` runs as `Zero` (the application's Tx slots are shared); `rx`, `fwd` and `maglev` move
//!   the pages of the Rx buffers.
//!
//! `Touch` (per application) adds a pass over every frame's payload: `Read` sums every byte of the frame (the
//! application of `rx`, `fwd`, `maglev`), `Write` writes every payload byte after the sequence number; a sender
//! (`tx`) always writes its payload when the touch is not `Off`.
//!
//! In a phase of c pairs the driver of pair k polls Rx queues k, k + c, k + 2c, .. of the device, so that a
//! generator spreading its frames over every queue loads each pair count fully (as mode `fwd` of the line-rate
//! benchmark). Every Tx queue sends a write-back request only on the last descriptor of each aligned batch of 32
//! (`TxQueue::send_frames`).

use crate::maglev::{Maglev, NO_BACKEND};
use crate::packet::{UdpFrame, HEADERS};
use crate::queue::{RxQueue, TxQueue};
use crate::{DmaRegion, Platform};
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU64, Ordering};

/// Entries per ring.
pub const RING: usize = 512;
/// Most frames per step.
pub const MAX_BATCH: usize = 32;
/// Bytes per Tx slot unless the application asks for larger ones (`App::new_with`).
pub const SLOT_BYTES: usize = 2048;
/// Where a frame carries its sequence number (the first payload bytes after the UDP header).
pub const SEQ_OFFSET: usize = HEADERS;
/// A thread that polls Rx queues waits `RX_HOLDOFF_CYCLES` after a step that found fewer than `RX_HOLDOFF_MIN`
/// frames, as `bench::run_queue_pair` and `bench::run_forwarder` do: polling the descriptors the device writes back
/// without a pause slows the whole port.
pub const RX_HOLDOFF_MIN: usize = 32;
pub const RX_HOLDOFF_CYCLES: u64 = 4000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Idle,
    Tx,
    Rx,
    Fwd,
    Maglev,
}

impl Mode {
    pub fn parse(s: &str) -> Option<Mode> {
        match s {
            "tx" => Some(Mode::Tx),
            "rx" => Some(Mode::Rx),
            "fwd" => Some(Mode::Fwd),
            "maglev" => Some(Mode::Maglev),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Mode::Idle => "idle",
            Mode::Tx => "tx",
            Mode::Rx => "rx",
            Mode::Fwd => "fwd",
            Mode::Maglev => "maglev",
        }
    }

    fn code(self) -> u64 {
        match self {
            Mode::Idle => 0,
            Mode::Tx => 1,
            Mode::Rx => 2,
            Mode::Fwd => 3,
            Mode::Maglev => 4,
        }
    }

    fn of_code(c: u64) -> Mode {
        match c {
            1 => Mode::Tx,
            2 => Mode::Rx,
            3 => Mode::Fwd,
            4 => Mode::Maglev,
            _ => Mode::Idle,
        }
    }

    /// Whether the driver polls Rx queues in this mode.
    pub fn polls(self) -> bool {
        matches!(self, Mode::Rx | Mode::Fwd | Mode::Maglev)
    }
}

/// How frames pass between the application and the driver (see the module comment).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Path {
    Zero,
    Copy,
    Map,
}

impl Path {
    pub fn parse(s: &str) -> Option<Path> {
        match s {
            "zero" | "z" => Some(Path::Zero),
            "copy" | "c" => Some(Path::Copy),
            "map" | "m" => Some(Path::Map),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Path::Zero => "zero",
            Path::Copy => "copy",
            Path::Map => "map",
        }
    }

    fn code(self) -> u64 {
        match self {
            Path::Zero => 0,
            Path::Copy => 1,
            Path::Map => 2,
        }
    }

    fn of_code(c: u64) -> Path {
        match c {
            1 => Path::Copy,
            2 => Path::Map,
            _ => Path::Zero,
        }
    }
}

/// The application's pass over each frame's payload (see the module comment).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Touch {
    Off,
    Read,
    Write,
}

impl Touch {
    pub fn parse(s: &str) -> Option<Touch> {
        match s {
            "off" | "none" => Some(Touch::Off),
            "read" => Some(Touch::Read),
            "write" => Some(Touch::Write),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Touch::Off => "off",
            Touch::Read => "read",
            Touch::Write => "write",
        }
    }
}

/// The sum of the 64-bit words of `[p, p + len)` (a trailing partial word as zero-padded), so that every byte is read.
pub fn sum_bytes(p: *const u8, len: usize) -> u64 {
    let mut sum = 0u64;
    let words = len / 8;
    for i in 0..words {
        sum = sum.wrapping_add(unsafe { (p.add(i * 8) as *const u64).read_unaligned() });
    }
    let mut tail = [0u8; 8];
    unsafe { core::ptr::copy_nonoverlapping(p.add(words * 8), tail.as_mut_ptr(), len % 8) };
    sum.wrapping_add(u64::from_le_bytes(tail))
}

/// Writes `v` over every byte of `[p + from, p + len)`.
pub fn fill_bytes(p: *mut u8, from: usize, len: usize, v: u64) {
    let mut off = from;
    while off + 8 <= len {
        unsafe { (p.add(off) as *mut u64).write_unaligned(v) };
        off += 8;
    }
    while off < len {
        unsafe { p.add(off).write(v as u8) };
        off += 1;
    }
}

/// Coalesces the frames of `ents`, each of which owns the `pages` 4 KiB pages from its (page-aligned) `va` on, into
/// runs of contiguous pages in the order given, and hands each run to `f` as (first VA, page count).
pub fn page_runs(ents: &[Entry], pages: usize, mut f: impl FnMut(u64, usize)) {
    let mut run: Option<(u64, usize)> = None;
    for e in ents {
        let va = e.va & !0xfff;
        run = match run {
            Some((start, n)) if start + (n * 4096) as u64 == va => Some((start, n + pages)),
            Some((start, n)) => {
                f(start, n);
                Some((va, pages))
            }
            None => Some((va, pages)),
        };
    }
    if let Some((start, n)) = run {
        f(start, n);
    }
}

/// A frame in a ring: its address for the CPU and for the device, and its length.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Entry {
    pub va: u64,
    pub iova: u64,
    pub len: u32,
    pub _pad: u32,
}

/// A counter on a cache line of its own.
#[repr(C, align(64))]
struct Counter(AtomicU64);

/// A single-producer single-consumer ring of `RING` entries; all zeros is an empty ring.
#[repr(C, align(4096))]
pub struct Spsc {
    /// Entries pushed and popped since the start.
    head: Counter,
    tail: Counter,
    entries: [UnsafeCell<Entry>; RING],
}

// The producer writes only `head` and the free entries, the consumer only `tail`.
unsafe impl Sync for Spsc {}

impl Spsc {
    /// Entries the consumer may pop.
    pub fn len(&self) -> usize {
        (self.head.0.load(Ordering::Acquire) - self.tail.0.load(Ordering::Acquire)) as usize
    }

    /// Entries the producer may push.
    pub fn room(&self) -> usize {
        RING - self.len()
    }

    /// Producer: pushes as many of `items` as fit; returns how many.
    pub fn push(&self, items: &[Entry]) -> usize {
        let h = self.head.0.load(Ordering::Relaxed);
        let t = self.tail.0.load(Ordering::Acquire);
        let n = items.len().min(RING - (h - t) as usize);
        for (i, e) in items[..n].iter().enumerate() {
            unsafe { core::ptr::write_volatile(self.entries[(h as usize + i) % RING].get(), *e) };
        }
        if n > 0 {
            self.head.0.store(h + n as u64, Ordering::Release);
        }
        n
    }

    /// Consumer: pops up to `max` entries, handing each to `f` in order; returns how many.
    pub fn pop(&self, max: usize, mut f: impl FnMut(Entry)) -> usize {
        let t = self.tail.0.load(Ordering::Relaxed);
        let h = self.head.0.load(Ordering::Acquire);
        let n = ((h - t) as usize).min(max);
        for i in 0..n {
            f(unsafe { core::ptr::read_volatile(self.entries[(t as usize + i) % RING].get()) });
        }
        if n > 0 {
            self.tail.0.store(t + n as u64, Ordering::Release);
        }
        n
    }

    /// Consumer: drops every entry.
    pub fn clear(&self) {
        self.tail.0.store(self.head.0.load(Ordering::Acquire), Ordering::Release);
    }
}

/// What one application thread and its driver thread share; all zeros is the initial state.
#[repr(C, align(4096))]
pub struct Shared {
    /// Application to driver: frames to send.
    pub tx: Spsc,
    /// Driver to application: frames received.
    pub rx: Spsc,
    /// Application: received frames it is done with in this phase (modes `rx`, and every polling mode of `Copy`).
    released: Counter,
    /// Driver: frames of this phase the device reported sent.
    completed: Counter,
    /// Application: the phase command (`seq << 32 | path << 24 | batch << 16 | pairs << 8 | mode`, mode 0 = end of
    /// phase).
    cmd: Counter,
    /// Driver: the sequence number of the last command it applied.
    ack: Counter,
}

/// Bytes of a `Shared` block (a multiple of 4096).
pub const SHARED_BYTES: usize = core::mem::size_of::<Shared>();

/// The application's side of one pair.
pub struct App {
    sh: *const Shared,
    mode: Mode,
    batch: usize,
    slots: DmaRegion,
    slot_count: usize,
    slot_bytes: usize,
    frame_len: u16,
    path: Path,
    touch: Touch,
    /// `Copy`: the private Tx slots (`slot_count`) and the private buffers frames are copied out into (`MAX_BATCH`).
    priv_tx: Vec<u8>,
    priv_rx: Vec<u8>,
    /// Modes `tx` and `Copy` forwarding: frames pushed in this phase (each with the next sequence number).
    sent: u64,
    seq: u64,
    /// Polling modes: frames released in this phase.
    released: u64,
    /// Modes `fwd` and `maglev`: the source and destination MAC of forwarded frames.
    fwd_src: [u8; 6],
    fwd_dst: [u8; 6],
    cmd_seq: u64,
    ents: [Entry; MAX_BATCH],
    /// `Map`: the frames of the last step, which `commit` releases (`rx`) or pushes for transmission (`fwd`).
    pending: usize,
    /// The sequence numbers read in mode `rx` and the payload sums, summed, so that the reads stay.
    pub seq_sum: u64,
}

unsafe impl Send for App {}

impl App {
    /// The application side over the block at `sh` and the Tx slots of `slots` (`slot_count * SLOT_BYTES` bytes),
    /// which gets `frame` written into every slot; forwarded frames go from `fwd_src` to `fwd_dst`; zero copy, no touch.
    pub fn new(sh: *const Shared, slots: DmaRegion, slot_count: usize, frame: &UdpFrame, fwd_src: [u8; 6], fwd_dst: [u8; 6]) -> App {
        App::new_with(sh, slots, slot_count, SLOT_BYTES, frame, fwd_src, fwd_dst, Path::Zero, Touch::Off)
    }

    /// `new` with Tx slots of `slot_bytes` bytes, data path `path` and payload pass `touch`.
    #[allow(clippy::too_many_arguments)]
    pub fn new_with(
        sh: *const Shared, slots: DmaRegion, slot_count: usize, slot_bytes: usize, frame: &UdpFrame, fwd_src: [u8; 6], fwd_dst: [u8; 6],
        path: Path, touch: Touch,
    ) -> App {
        assert!(slots.len >= slot_count * slot_bytes && frame.len <= slot_bytes && slot_count > 0);
        let (priv_tx, priv_rx) = match path {
            Path::Copy => (alloc::vec![0u8; slot_count * slot_bytes], alloc::vec![0u8; MAX_BATCH * slot_bytes]),
            _ => (Vec::new(), Vec::new()),
        };
        let mut a = App {
            sh, mode: Mode::Idle, batch: 1, slots, slot_count, slot_bytes, frame_len: frame.len as u16, path, touch, priv_tx, priv_rx, sent: 0,
            seq: 0, released: 0, fwd_src, fwd_dst, cmd_seq: 0, ents: [Entry::default(); MAX_BATCH], pending: 0, seq_sum: 0,
        };
        for i in 0..slot_count {
            frame.write(unsafe { core::slice::from_raw_parts_mut(slots.va.add(i * slot_bytes), slot_bytes) });
            if path == Path::Copy {
                frame.write(&mut a.priv_tx[i * slot_bytes..(i + 1) * slot_bytes]);
            }
        }
        a.cmd_seq = unsafe { &*sh }.cmd.0.load(Ordering::Relaxed) >> 32;
        a
    }

    pub fn shared(&self) -> &Shared {
        unsafe { &*self.sh }
    }

    pub fn mode(&self) -> Mode {
        self.mode
    }

    pub fn path(&self) -> Path {
        self.path
    }

    /// Sets the payload pass of the next phases (between phases).
    pub fn set_touch(&mut self, touch: Touch) {
        self.touch = touch;
    }

    fn post(&mut self, mode: Mode, batch: usize, pairs: usize) -> u64 {
        self.cmd_seq += 1;
        let cmd = self.cmd_seq << 32 | self.path.code() << 24 | (batch as u64 & 0xff) << 16 | (pairs as u64 & 0xff) << 8 | mode.code();
        self.shared().cmd.0.store(cmd, Ordering::Release);
        self.cmd_seq
    }

    /// Posts the start of a phase of `mode` with up to `batch` frames per step, in which `pairs` pairs run; returns
    /// the command's sequence number. Steps only after `acked` (or, in the IPC shape, after the call that carries it).
    pub fn begin(&mut self, mode: Mode, batch: usize, pairs: usize) -> u64 {
        assert!(mode != Mode::Idle && (1..=MAX_BATCH).contains(&batch) && (1..256).contains(&pairs));
        (self.mode, self.batch, self.sent, self.released, self.pending) = (mode, batch, 0, 0, 0);
        self.shared().released.0.store(0, Ordering::Release);
        self.post(mode, batch, pairs)
    }

    /// Posts the end of the phase; once `acked`, `after_end` drops what the driver handed and nobody read. With `Map`
    /// the front end first takes back the frames still in the Rx ring (`drain_rx`) and gives their pages back.
    pub fn end(&mut self) -> u64 {
        self.mode = Mode::Idle;
        self.post(Mode::Idle, 1, 1)
    }

    pub fn acked(&self, seq: u64) -> bool {
        self.shared().ack.0.load(Ordering::Acquire) >= seq
    }

    pub fn after_end(&mut self) {
        self.shared().rx.clear();
    }

    /// Pops every frame left in the Rx ring into `pending` batches handed to `f` (for a `Map` front end to give their
    /// pages back before `end`); returns how many.
    pub fn drain_rx(&mut self, mut f: impl FnMut(&[Entry])) -> usize {
        let sh = unsafe { &*self.sh };
        let mut total = 0;
        loop {
            let ents = &mut self.ents;
            let mut n = 0;
            sh.rx.pop(MAX_BATCH, |e| {
                ents[n] = e;
                n += 1;
            });
            if n == 0 {
                return total;
            }
            f(&self.ents[..n]);
            total += n;
        }
    }

    /// One step of the phase (see the module comment); returns the frames it moved: pushed for transmission (`tx`),
    /// read and released (`rx`), or forwarded (`fwd`; `maglev`, which needs `m`). With `Map` the frames of a polling
    /// mode are `pending` until `commit`.
    pub fn step(&mut self, m: Option<&mut Maglev<'_>>) -> usize {
        match (self.mode, self.path) {
            (Mode::Idle, _) => 0,
            (Mode::Tx, _) => self.step_tx(),
            (Mode::Rx, _) => self.step_rx(),
            (Mode::Fwd, Path::Copy) => self.step_fwd_copy(None),
            (Mode::Maglev, Path::Copy) => self.step_fwd_copy(Some(m.expect("mode maglev needs the maglev state"))),
            (Mode::Fwd, _) => self.step_fwd(None),
            (Mode::Maglev, _) => self.step_fwd(Some(m.expect("mode maglev needs the maglev state"))),
        }
    }

    /// `Map`: the frames of the last step, whose pages the application holds until `commit`.
    pub fn pending(&self) -> &[Entry] {
        &self.ents[..self.pending]
    }

    /// `Map`: makes the last step's frames visible to the driver: releases them (`rx`) or pushes them for transmission
    /// (`fwd`, `maglev`). The front end gives their pages back first.
    pub fn commit(&mut self) {
        let n = core::mem::take(&mut self.pending);
        if n == 0 {
            return;
        }
        let sh = unsafe { &*self.sh };
        if self.mode == Mode::Rx {
            self.released += n as u64;
            sh.released.0.store(self.released, Ordering::Release);
        } else {
            let pushed = sh.tx.push(&self.ents[..n]);
            debug_assert_eq!(pushed, n);
        }
    }

    /// The payload pass over the frame at `p` of `len` bytes whose sequence number is `seq`.
    fn touch_frame(&mut self, p: *mut u8, len: usize, seq: u64) {
        match self.touch {
            Touch::Off => {}
            Touch::Read => self.seq_sum = self.seq_sum.wrapping_add(sum_bytes(p, len)),
            Touch::Write => fill_bytes(p, SEQ_OFFSET + 8, len, seq),
        }
    }

    fn step_tx(&mut self) -> usize {
        let sh = unsafe { &*self.sh };
        let done = sh.completed.0.load(Ordering::Acquire);
        let free = self.slot_count - (self.sent - done.min(self.sent)) as usize;
        let n = self.batch.min(free).min(sh.tx.room());
        let len = self.frame_len as usize;
        for i in 0..n {
            let slot = ((self.sent + i as u64) % self.slot_count as u64) as usize;
            let off = slot * self.slot_bytes;
            let shared = unsafe { self.slots.va.add(off) };
            // `Copy` builds the frame in its private slot, then copies it into the shared one.
            let work = if self.path == Path::Copy { unsafe { self.priv_tx.as_mut_ptr().add(off) } } else { shared };
            unsafe { (work.add(SEQ_OFFSET) as *mut u64).write_unaligned(self.seq) };
            if self.touch != Touch::Off {
                fill_bytes(work, SEQ_OFFSET + 8, len, self.seq);
            }
            if self.path == Path::Copy {
                unsafe { core::ptr::copy_nonoverlapping(work, shared, len) };
            }
            self.seq += 1;
            self.ents[i] = Entry { va: shared as u64, iova: self.slots.iova + off as u64, len: len as u32, _pad: 0 };
        }
        let pushed = sh.tx.push(&self.ents[..n]);
        debug_assert_eq!(pushed, n);
        self.sent += n as u64;
        n
    }

    fn step_rx(&mut self) -> usize {
        let sh = unsafe { &*self.sh };
        let mut got = [Entry::default(); MAX_BATCH];
        let mut n = 0;
        sh.rx.pop(self.batch, |e| {
            got[n] = e;
            n += 1;
        });
        for (i, e) in got[..n].iter().enumerate() {
            let len = if self.path == Path::Copy { (e.len as usize).min(self.slot_bytes) } else { e.len as usize };
            let p = match self.path {
                Path::Copy => {
                    let q = unsafe { self.priv_rx.as_mut_ptr().add(i * self.slot_bytes) };
                    unsafe { core::ptr::copy_nonoverlapping(e.va as *const u8, q, len) };
                    q
                }
                _ => e.va as *mut u8,
            };
            let seq = unsafe { (p.add(SEQ_OFFSET) as *const u64).read_unaligned() };
            self.seq_sum = self.seq_sum.wrapping_add(seq);
            self.touch_frame(p, len, seq);
        }
        if n > 0 {
            if self.path == Path::Map {
                self.ents[..n].copy_from_slice(&got[..n]);
                self.pending = n;
            } else {
                self.released += n as u64;
                sh.released.0.store(self.released, Ordering::Release);
            }
        }
        n
    }

    /// Forwarding in place (`Zero`, and `Map` up to `commit`).
    fn step_fwd(&mut self, mut m: Option<&mut Maglev<'_>>) -> usize {
        let sh = unsafe { &*self.sh };
        let (src, dst) = (self.fwd_src, self.fwd_dst);
        let mut got = [Entry::default(); MAX_BATCH];
        let mut n = 0;
        sh.rx.pop(self.batch.min(sh.tx.room()), |e| {
            got[n] = e;
            n += 1;
        });
        for e in &got[..n] {
            let frame = unsafe { core::slice::from_raw_parts_mut(e.va as *mut u8, e.len as usize) };
            self.work(frame, src, dst, m.as_deref_mut());
        }
        self.ents[..n].copy_from_slice(&got[..n]);
        if self.path == Path::Map {
            self.pending = n;
        } else {
            let pushed = sh.tx.push(&self.ents[..n]);
            debug_assert_eq!(pushed, n);
        }
        n
    }

    /// The per-frame work of forwarding on `frame`: the payload pass, maglev with `m`, the MAC rewrite.
    fn work(&mut self, frame: &mut [u8], src: [u8; 6], dst: [u8; 6], m: Option<&mut Maglev<'_>>) {
        let len = frame.len();
        let seq = if len >= SEQ_OFFSET + 8 { u64::from_le_bytes(frame[SEQ_OFFSET..SEQ_OFFSET + 8].try_into().unwrap()) } else { 0 };
        self.touch_frame(frame.as_mut_ptr(), len, seq);
        let keep = match m {
            Some(m) => m.process(frame) != NO_BACKEND,
            None => true,
        };
        if keep {
            frame[6..12].copy_from_slice(&src);
            frame[0..6].copy_from_slice(&dst);
        }
    }

    /// `Copy` forwarding: copy out, work on the private copy, copy into a free shared Tx slot; the Rx buffers are
    /// released at once.
    fn step_fwd_copy(&mut self, mut m: Option<&mut Maglev<'_>>) -> usize {
        let sh = unsafe { &*self.sh };
        let (src, dst) = (self.fwd_src, self.fwd_dst);
        let done = sh.completed.0.load(Ordering::Acquire);
        let free = self.slot_count - (self.sent - done.min(self.sent)) as usize;
        let mut got = [Entry::default(); MAX_BATCH];
        let mut n = 0;
        sh.rx.pop(self.batch.min(sh.tx.room()).min(free), |e| {
            got[n] = e;
            n += 1;
        });
        for (i, e) in got[..n].iter().enumerate() {
            let len = (e.len as usize).min(self.slot_bytes);
            let q = unsafe { self.priv_rx.as_mut_ptr().add(i * self.slot_bytes) };
            unsafe { core::ptr::copy_nonoverlapping(e.va as *const u8, q, len) };
            let frame = unsafe { core::slice::from_raw_parts_mut(q, len) };
            self.work(frame, src, dst, m.as_deref_mut());
            let slot = ((self.sent + i as u64) % self.slot_count as u64) as usize;
            let off = slot * self.slot_bytes;
            unsafe { core::ptr::copy_nonoverlapping(q, self.slots.va.add(off), len) };
            self.ents[i] = Entry { va: self.slots.va as u64 + off as u64, iova: self.slots.iova + off as u64, len: len as u32, _pad: 0 };
        }
        if n > 0 {
            self.released += n as u64;
            sh.released.0.store(self.released, Ordering::Release);
            let pushed = sh.tx.push(&self.ents[..n]);
            debug_assert_eq!(pushed, n);
            self.sent += n as u64;
        }
        n
    }
}

/// The driver's side of one pair: its Tx queue, the Rx queues it polls in the current phase, and the received
/// frames out with the application.
pub struct Driver<'p, P: Platform> {
    pub tx: TxQueue<'p, P>,
    /// The pair's index.
    k: usize,
    mode: Mode,
    path: Path,
    batch: usize,
    rxs: Vec<*mut RxQueue<'p, P>>,
    /// Per batch handed to the application: the count of frames handed in this phase after it, its Rx queue (index
    /// into `rxs`) and the position that gives it back.
    held: VecDeque<(u64, usize, usize)>,
    handed: u64,
    /// `tx.completed` counted from the start of the phase on (see `control`).
    base: u64,
    last_cmd: u64,
    next: usize,
    frames: [(u64, u16); MAX_BATCH],
    ents: [Entry; MAX_BATCH],
    /// `Map`: frames of the last step not pushed to the application yet (`commit`).
    pending: usize,
}

unsafe impl<P: Platform> Send for Driver<'_, P> {}

impl<'p, P: Platform> Driver<'p, P> {
    pub fn new(tx: TxQueue<'p, P>, k: usize) -> Self {
        Driver {
            tx, k, mode: Mode::Idle, path: Path::Zero, batch: 1, rxs: Vec::new(), held: VecDeque::with_capacity(1024), handed: 0, base: 0, last_cmd: 0,
            next: 0, frames: [(0, 0); MAX_BATCH], ents: [Entry::default(); MAX_BATCH], pending: 0,
        }
    }

    pub fn mode(&self) -> Mode {
        self.mode
    }

    pub fn path(&self) -> Path {
        self.path
    }

    /// Applies the block's phase command if it is new: ends the current phase (every frame the application holds
    /// goes back to its Rx queue, unsent entries are dropped), then starts the new one, in which this driver polls
    /// the queues k, k + c, .. of `queues` (every Rx queue of the device) for a phase of c pairs. Returns whether it
    /// applied one. The queues of a phase must be polled by no other driver.
    pub fn control(&mut self, sh: &Shared, queues: &[*mut RxQueue<'p, P>]) -> bool {
        self.control_with(sh, queues, || {})
    }

    /// `control` that runs `hook` once it found a new command and before it re-arms anything.
    pub fn control_with(&mut self, sh: &Shared, queues: &[*mut RxQueue<'p, P>], hook: impl FnOnce()) -> bool {
        let cmd = sh.cmd.0.load(Ordering::Acquire);
        if cmd == self.last_cmd {
            return false;
        }
        hook();
        self.last_cmd = cmd;
        for &rx in &self.rxs {
            let rx = unsafe { &mut *rx };
            let pos = rx.position();
            rx.give_back_to(pos);
        }
        self.rxs.clear();
        self.held.clear();
        sh.tx.clear();
        let (mode, pairs, batch, path) =
            (Mode::of_code(cmd & 0xff), ((cmd >> 8) & 0xff) as usize, ((cmd >> 16) & 0xff) as usize, Path::of_code((cmd >> 24) & 0xff));
        self.mode = mode;
        self.path = path;
        self.batch = batch.clamp(1, MAX_BATCH);
        if mode.polls() {
            self.rxs.extend((self.k..queues.len()).step_by(pairs.max(1)).map(|q| queues[q]));
        }
        self.handed = 0;
        self.next = 0;
        self.pending = 0;
        // Descriptors still queued from an earlier phase complete in whole batches with the first ones of this phase.
        self.tx.clean();
        self.base = self.tx.completed + self.tx.in_flight() as u64;
        sh.completed.0.store(0, Ordering::Release);
        sh.ack.0.store(cmd >> 32, Ordering::Release);
        true
    }

    /// One step of the phase (see the module comment): reclaims sent frames, re-arms released ones, queues up to
    /// `MAX_BATCH` frames from the Tx ring, and hands up to the phase's batch of received frames over; returns the
    /// frames queued for transmission and handed over.
    pub fn step(&mut self, sh: &Shared) -> (usize, usize) {
        self.step_with(sh, || {})
    }

    /// `step` that runs `hook` after it read what the application released and pushed and before it re-arms or
    /// queues anything: whatever the application gave back before that is visible to the hook. With `Map` the frames
    /// handed over are `pending` until `commit`.
    pub fn step_with(&mut self, sh: &Shared, hook: impl FnOnce()) -> (usize, usize) {
        if self.mode == Mode::Idle {
            return (0, 0);
        }
        self.tx.clean();
        let done = self.tx.completed.saturating_sub(self.base);
        sh.completed.0.store(done, Ordering::Release);
        let released = match (self.mode, self.path) {
            (Mode::Rx, _) | (_, Path::Copy) => sh.released.0.load(Ordering::Acquire),
            _ => done,
        };
        let queued = sh.tx.len();
        hook();
        while let Some(&(after, i, pos)) = self.held.front() {
            if after > released {
                break;
            }
            unsafe { &mut *self.rxs[i] }.give_back_to(pos);
            self.held.pop_front();
        }
        let mut sent = 0;
        if self.mode != Mode::Rx {
            let frames = &mut self.frames;
            let mut n = 0;
            sh.tx.pop(MAX_BATCH.min(self.tx.room()).min(queued), |e| {
                frames[n] = (e.iova, e.len as u16);
                n += 1;
            });
            if n > 0 {
                sent = self.tx.send_frames(&frames[..n]);
                debug_assert_eq!(sent, n);
            }
        }
        let mut handed = 0;
        let defer = self.path == Path::Map;
        if self.mode.polls() && !self.rxs.is_empty() {
            let q = self.rxs.len();
            for _ in 0..q {
                let want = (self.batch - handed).min(sh.rx.room().saturating_sub(if defer { handed } else { 0 }));
                if want == 0 {
                    break;
                }
                let i = self.next;
                self.next = if i + 1 == q { 0 } else { i + 1 };
                let rx = unsafe { &mut *self.rxs[i] };
                let ents = &mut self.ents;
                let first = if defer { handed } else { 0 };
                let mut n = 0;
                let took = rx.take(want, |f| {
                    ents[first + n] = Entry { va: f.va as u64, iova: f.iova, len: f.len as u32, _pad: 0 };
                    n += 1;
                });
                if took == 0 {
                    continue;
                }
                if !defer {
                    let pushed = sh.rx.push(&ents[..n]);
                    debug_assert_eq!(pushed, n);
                }
                self.handed += n as u64;
                self.held.push_back((self.handed, i, rx.position()));
                handed += n;
            }
        }
        if defer {
            self.pending = handed;
        }
        (sent, handed)
    }

    /// `Map`: the frames of the last step that the application does not see yet.
    pub fn pending(&self) -> &[Entry] {
        &self.ents[..self.pending]
    }

    /// `Map`: pushes the last step's frames to the application, once the front end gave it their pages.
    pub fn commit(&mut self, sh: &Shared) {
        let n = core::mem::take(&mut self.pending);
        if n > 0 {
            let pushed = sh.rx.push(&self.ents[..n]);
            debug_assert_eq!(pushed, n);
        }
    }

    /// The ring shape's loop body: `control`, `step`, and the Rx hold-off after a step that handed over fewer than the
    /// phase's batch (at most `RX_HOLDOFF_MIN`) frames in a mode that polls, as the IPC and linked shapes do after a
    /// step that brought fewer than asked for; returns the step's counts.
    pub fn run_once(&mut self, p: &P, sh: &Shared, queues: &[*mut RxQueue<'p, P>]) -> (usize, usize) {
        self.control(sh, queues);
        let (sent, handed) = self.step(sh);
        if self.mode.polls() && handed < self.batch.min(RX_HOLDOFF_MIN) {
            holdoff(p);
        }
        (sent, handed)
    }

    /// Whether the last `step` handed over so few frames that a polling loop should hold off.
    pub fn should_hold_off(&self, handed: usize) -> bool {
        self.mode.polls() && handed < self.batch.min(RX_HOLDOFF_MIN)
    }
}

/// Waits `RX_HOLDOFF_CYCLES` TSC cycles.
pub fn holdoff<P: Platform>(p: &P) {
    let until = p.tsc() + RX_HOLDOFF_CYCLES;
    while p.tsc() < until {
        core::hint::spin_loop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::maglev::{populate_lut, CACHE_ENTRIES, TABLE_SIZE};
    use crate::mock::{Mock, MOCK_MAC};
    use crate::packet::steering_mac;
    use crate::{Config, Device};
    use alloc::boxed::Box;

    fn frame(dst: [u8; 6], q: usize) -> UdpFrame {
        UdpFrame { dst_mac: dst, src_mac: MOCK_MAC, src_ip: [10, 0, 0, 1 + q as u8], dst_ip: [10, 0, 1, 1], src_port: 1024, dst_port: 5000, len: 60 }
    }

    fn shared() -> Box<Shared> {
        unsafe { Box::new_zeroed().assume_init() }
    }

    #[test]
    fn spsc_order_and_room() {
        let sh = shared();
        let e = |i: u64| Entry { va: i, iova: i, len: 1, _pad: 0 };
        let items: Vec<Entry> = (0..RING as u64 + 5).map(e).collect();
        assert_eq!(sh.tx.push(&items), RING);
        assert_eq!(sh.tx.room(), 0);
        let mut got = Vec::new();
        assert_eq!(sh.tx.pop(10, |x| got.push(x.va)), 10);
        assert_eq!(got, (0..10).collect::<Vec<_>>());
        assert_eq!(sh.tx.push(&items[RING..]), 5);
        sh.tx.clear();
        assert_eq!(sh.tx.len(), 0);
    }

    /// Pairs 0 and 1 on a model of 4 queues: tx (frames loop back into the queues nobody polls), then rx of
    /// frames a sender queue sends to queues 0..3, then fwd and maglev of frames looped back to the forwarder's queues.
    #[test]
    fn modes_over_the_model() {
        let m = Mock::new(true);
        let (nq, slots) = (4, 64);
        let mut dev = Device::new(&m, Config { queues: nq, tx_ring: 512, rx_ring: 128, tx_batch: 32, ..Default::default() }).unwrap();
        let mut txs = Vec::new();
        let mut rxs: Vec<Box<RxQueue<'_, Mock>>> = Vec::new();
        for (tx, rx) in dev.take_queues() {
            txs.push(tx);
            rxs.push(Box::new(rx));
        }
        let queues: Vec<*mut RxQueue<'_, Mock>> = rxs.iter_mut().map(|r| &mut **r as *mut _).collect();
        let mut sender = txs.pop().unwrap();
        let mut sender2 = txs.pop().unwrap();
        let blocks = [shared(), shared()];
        let mut lut = alloc::vec![0i8; TABLE_SIZE];
        populate_lut(&mut lut);
        let mut cache = alloc::vec![[0u64; 2]; CACHE_ENTRIES];
        let mut mg = Maglev::new(&lut, &mut cache);
        let mut pairs: Vec<(App, Driver<'_, Mock>)> = Vec::new();
        for (k, tx) in txs.into_iter().enumerate() {
            let region = m.dma_alloc(slots * SLOT_BYTES, 4096).unwrap();
            let app = App::new(&*blocks[k], region, slots, &frame(steering_mac(MOCK_MAC, k + 9), k), MOCK_MAC, steering_mac(MOCK_MAC, k));
            pairs.push((app, Driver::new(tx, k)));
        }
        // tx: to a steering MAC without a queue (the model drops such frames).
        let moved = run(&mut pairs, &queues, Mode::Tx, 32, 40, &mut mg);
        assert!(moved.iter().all(|&x| x >= 30 * 32), "{:?}", moved);
        assert!(pairs.iter().all(|(_, d)| d.tx.completed >= 30 * 32));
        // rx: 96 frames to each queue (fewer than an Rx ring holds); pair k polls queues k and k + 2.
        for q in 0..nq {
            let f = copy_of(&m, &frame(steering_mac(MOCK_MAC, q), q));
            for _ in 0..3 {
                let s = if q % 2 == 0 { &mut sender } else { &mut sender2 };
                assert_eq!(s.send_frames(&[f; 32]), 32);
            }
        }
        let moved = run(&mut pairs, &queues, Mode::Rx, 1, 300, &mut mg);
        assert_eq!(moved, alloc::vec![192, 192]);
        // fwd: frames to each pair's own queue k circulate: each forwarded frame goes back to queue k.
        for k in 0..2 {
            let f = copy_of(&m, &frame(steering_mac(MOCK_MAC, k), k));
            assert_eq!(sender.send_frames(&[f; 32]), 32);
        }
        let moved = run(&mut pairs, &queues, Mode::Fwd, 32, 200, &mut mg);
        assert!(moved.iter().all(|&x| x > 1000), "{:?}", moved);
        // maglev: the same circulation, now through `Maglev::process` (the frames left in the rings by fwd's end).
        for k in 0..2 {
            let f = copy_of(&m, &frame(steering_mac(MOCK_MAC, k), k));
            assert_eq!(sender.send_frames(&[f; 32]), 32);
        }
        let moved = run(&mut pairs, &queues, Mode::Maglev, 1, 200, &mut mg);
        assert!(moved.iter().all(|&x| x >= 150), "{:?}", moved);
        assert!(m.rxqs().values().all(|r| r.dropped == 0), "{:?}", m.rxqs());
    }

    fn run<'a>(pairs: &mut [(App, Driver<'a, Mock>)], queues: &[*mut RxQueue<'a, Mock>], mode: Mode, batch: usize, rounds: usize, mg: &mut Maglev<'_>) -> Vec<u64> {
        let mut moved = alloc::vec![0u64; pairs.len()];
        for (app, drv) in pairs.iter_mut() {
            let seq = app.begin(mode, batch, 2);
            assert!(drv.control(app.shared(), queues));
            assert!(app.acked(seq));
        }
        for _ in 0..rounds {
            for (k, (app, drv)) in pairs.iter_mut().enumerate() {
                moved[k] += app.step(Some(&mut *mg)) as u64;
                drv.step(app.shared());
            }
        }
        for (app, drv) in pairs.iter_mut() {
            let seq = app.end();
            assert!(drv.control(app.shared(), queues));
            assert!(app.acked(seq));
            app.after_end();
        }
        moved
    }

    /// One copy of `f` in model memory as (IOVA, length).
    fn copy_of(m: &Mock, f: &UdpFrame) -> (u64, u16) {
        let r = m.dma_alloc(2048, 128).unwrap();
        f.write(unsafe { core::slice::from_raw_parts_mut(r.va, 2048) });
        (r.iova, f.len as u16)
    }

    #[test]
    fn payload_helpers() {
        let mut buf = [0u8; 21];
        for (i, b) in buf.iter_mut().enumerate() {
            *b = i as u8 + 1;
        }
        let words = u64::from_le_bytes(buf[0..8].try_into().unwrap()).wrapping_add(u64::from_le_bytes(buf[8..16].try_into().unwrap()));
        let mut tail = [0u8; 8];
        tail[..5].copy_from_slice(&buf[16..21]);
        assert_eq!(sum_bytes(buf.as_ptr(), 21), words.wrapping_add(u64::from_le_bytes(tail)));
        fill_bytes(buf.as_mut_ptr(), 3, 21, 0x0101_0101_0101_0101 * 0xab);
        assert_eq!(&buf[..3], &[1, 2, 3]);
        assert!(buf[3..].iter().all(|&b| b == 0xab));
        let e = |va: u64| Entry { va, iova: va, len: 60, _pad: 0 };
        let mut runs = Vec::new();
        page_runs(&[e(0x10000), e(0x11000), e(0x12000), e(0x20000), e(0x21000), e(0x13000)], 1, |va, n| runs.push((va, n)));
        assert_eq!(runs, alloc::vec![(0x10000, 3), (0x20000, 2), (0x13000, 1)]);
        runs.clear();
        page_runs(&[e(0x10000), e(0x13000), e(0x16000)], 3, |va, n| runs.push((va, n)));
        assert_eq!(runs, alloc::vec![(0x10000, 9)]);
        runs.clear();
        page_runs(&[], 1, |va, n| runs.push((va, n)));
        assert!(runs.is_empty());
    }

    /// The copy and map paths, each with a payload pass, over the model as `modes_over_the_model`: tx, then rx of
    /// frames a sender queue sends, then fwd of frames that circulate. The map path's front end is simulated: the
    /// application and the driver commit right after each step, the driver's hook runs between.
    #[test]
    fn paths_over_the_model() {
        for (path, touch) in [(Path::Zero, Touch::Read), (Path::Copy, Touch::Read), (Path::Copy, Touch::Write), (Path::Map, Touch::Read), (Path::Map, Touch::Write)] {
            let m = Mock::new(true);
            let (nq, slots) = (4, 64);
            let mut dev = Device::new(&m, Config { queues: nq, tx_ring: 512, rx_ring: 128, tx_batch: 32, ..Default::default() }).unwrap();
            let mut txs = Vec::new();
            let mut rxs: Vec<Box<RxQueue<'_, Mock>>> = Vec::new();
            for (tx, rx) in dev.take_queues() {
                txs.push(tx);
                rxs.push(Box::new(rx));
            }
            let queues: Vec<*mut RxQueue<'_, Mock>> = rxs.iter_mut().map(|r| &mut **r as *mut _).collect();
            let mut sender = txs.pop().unwrap();
            let mut sender2 = txs.pop().unwrap();
            let blocks = [shared(), shared()];
            let mut lut = alloc::vec![0i8; TABLE_SIZE];
            populate_lut(&mut lut);
            let mut cache = alloc::vec![[0u64; 2]; CACHE_ENTRIES];
            let mut mg = Maglev::new(&lut, &mut cache);
            let mut pairs: Vec<(App, Driver<'_, Mock>)> = Vec::new();
            for (k, tx) in txs.into_iter().enumerate() {
                let region = m.dma_alloc(slots * SLOT_BYTES, 4096).unwrap();
                let f = frame(steering_mac(MOCK_MAC, k + 9), k);
                let app = App::new_with(&*blocks[k], region, slots, SLOT_BYTES, &f, MOCK_MAC, steering_mac(MOCK_MAC, k), path, touch);
                pairs.push((app, Driver::new(tx, k)));
            }
            let moved = run_path(&mut pairs, &queues, Mode::Tx, 32, 40, &mut mg);
            assert!(moved.iter().all(|&x| x >= 30 * 32), "{:?} {:?}", path, moved);
            for q in 0..nq {
                let f = copy_of(&m, &frame(steering_mac(MOCK_MAC, q), q));
                for _ in 0..3 {
                    let s = if q % 2 == 0 { &mut sender } else { &mut sender2 };
                    assert_eq!(s.send_frames(&[f; 32]), 32);
                }
            }
            let moved = run_path(&mut pairs, &queues, Mode::Rx, 1, 300, &mut mg);
            assert_eq!(moved, alloc::vec![192, 192], "{:?}", path);
            assert!(pairs.iter().all(|(a, _)| a.seq_sum != 0 || touch == Touch::Write));
            for k in 0..2 {
                let f = copy_of(&m, &frame(steering_mac(MOCK_MAC, k), k));
                assert_eq!(sender.send_frames(&[f; 32]), 32);
            }
            let moved = run_path(&mut pairs, &queues, Mode::Fwd, 32, 200, &mut mg);
            assert!(moved.iter().all(|&x| x > 1000), "{:?} {:?}", path, moved);
            for k in 0..2 {
                let f = copy_of(&m, &frame(steering_mac(MOCK_MAC, k), k));
                assert_eq!(sender.send_frames(&[f; 32]), 32);
            }
            let moved = run_path(&mut pairs, &queues, Mode::Maglev, 1, 200, &mut mg);
            assert!(moved.iter().all(|&x| x >= 150), "{:?} {:?}", path, moved);
            assert!(m.rxqs().values().all(|r| r.dropped == 0), "{:?}", m.rxqs());
        }
    }

    fn run_path<'a>(pairs: &mut [(App, Driver<'a, Mock>)], queues: &[*mut RxQueue<'a, Mock>], mode: Mode, batch: usize, rounds: usize, mg: &mut Maglev<'_>) -> Vec<u64> {
        let mut moved = alloc::vec![0u64; pairs.len()];
        for (app, drv) in pairs.iter_mut() {
            let seq = app.begin(mode, batch, 2);
            assert!(drv.control(app.shared(), queues));
            assert!(app.acked(seq));
            assert_eq!(drv.path(), app.path());
        }
        for _ in 0..rounds {
            for (k, (app, drv)) in pairs.iter_mut().enumerate() {
                moved[k] += app.step(Some(&mut *mg)) as u64;
                app.commit();
                let mut hooked = false;
                drv.step_with(app.shared(), || hooked = true);
                assert!(hooked || drv.mode() == Mode::Idle);
                assert!(app.path() == Path::Map || drv.pending().is_empty());
                drv.commit(app.shared());
            }
        }
        for (app, drv) in pairs.iter_mut() {
            app.drain_rx(|_| {});
            let seq = app.end();
            assert!(drv.control(app.shared(), queues));
            assert!(app.acked(seq));
            app.after_end();
        }
        moved
    }
}
