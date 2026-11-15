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
/// Bytes per Tx slot.
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
    /// Application: received frames it is done with in this phase (mode `rx`).
    released: Counter,
    /// Driver: frames of this phase the device reported sent.
    completed: Counter,
    /// Application: the phase command (`seq << 32 | batch << 16 | pairs << 8 | mode`, mode 0 = end of phase).
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
    frame_len: u16,
    /// Mode `tx`: frames pushed in this phase (each with the next sequence number).
    sent: u64,
    seq: u64,
    /// Mode `rx`: frames released in this phase.
    released: u64,
    /// Modes `fwd` and `maglev`: the source and destination MAC of forwarded frames.
    fwd_src: [u8; 6],
    fwd_dst: [u8; 6],
    cmd_seq: u64,
    ents: [Entry; MAX_BATCH],
    /// The sequence numbers read in mode `rx`, summed, so that the reads stay.
    pub seq_sum: u64,
}

unsafe impl Send for App {}

impl App {
    /// The application side over the block at `sh` and the Tx slots of `slots` (`slot_count * SLOT_BYTES` bytes),
    /// which gets `frame` written into every slot; forwarded frames go from `fwd_src` to `fwd_dst`.
    pub fn new(sh: *const Shared, slots: DmaRegion, slot_count: usize, frame: &UdpFrame, fwd_src: [u8; 6], fwd_dst: [u8; 6]) -> App {
        assert!(slots.len >= slot_count * SLOT_BYTES && frame.len <= SLOT_BYTES && slot_count > 0);
        for i in 0..slot_count {
            frame.write(unsafe { core::slice::from_raw_parts_mut(slots.va.add(i * SLOT_BYTES), SLOT_BYTES) });
        }
        let cmd_seq = unsafe { &*sh }.cmd.0.load(Ordering::Relaxed) >> 32;
        App {
            sh, mode: Mode::Idle, batch: 1, slots, slot_count, frame_len: frame.len as u16, sent: 0, seq: 0, released: 0, fwd_src, fwd_dst,
            cmd_seq, ents: [Entry::default(); MAX_BATCH], seq_sum: 0,
        }
    }

    pub fn shared(&self) -> &Shared {
        unsafe { &*self.sh }
    }

    pub fn mode(&self) -> Mode {
        self.mode
    }

    fn post(&mut self, mode: Mode, batch: usize, pairs: usize) -> u64 {
        self.cmd_seq += 1;
        let cmd = self.cmd_seq << 32 | (batch as u64) << 16 | (pairs as u64 & 0xff) << 8 | mode.code();
        self.shared().cmd.0.store(cmd, Ordering::Release);
        self.cmd_seq
    }

    /// Posts the start of a phase of `mode` with up to `batch` frames per step, in which `pairs` pairs run; returns
    /// the command's sequence number. Steps only after `acked` (or, in the IPC shape, after the call that carries it).
    pub fn begin(&mut self, mode: Mode, batch: usize, pairs: usize) -> u64 {
        assert!(mode != Mode::Idle && (1..=MAX_BATCH).contains(&batch) && (1..256).contains(&pairs));
        (self.mode, self.batch, self.sent, self.released) = (mode, batch, 0, 0);
        self.shared().released.0.store(0, Ordering::Release);
        self.post(mode, batch, pairs)
    }

    /// Posts the end of the phase; once `acked`, `after_end` drops what the driver handed and nobody read.
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

    /// One step of the phase (see the module comment); returns the frames it moved: pushed for transmission (`tx`),
    /// read and released (`rx`), or forwarded (`fwd`; `maglev`, which needs `m`).
    pub fn step(&mut self, m: Option<&mut Maglev<'_>>) -> usize {
        match self.mode {
            Mode::Idle => 0,
            Mode::Tx => self.step_tx(),
            Mode::Rx => self.step_rx(),
            Mode::Fwd => self.step_fwd(None),
            Mode::Maglev => self.step_fwd(Some(m.expect("mode maglev needs the maglev state"))),
        }
    }

    fn step_tx(&mut self) -> usize {
        let sh = unsafe { &*self.sh };
        let done = sh.completed.0.load(Ordering::Acquire);
        let free = self.slot_count - (self.sent - done.min(self.sent)) as usize;
        let n = self.batch.min(free).min(sh.tx.room());
        for i in 0..n {
            let slot = ((self.sent + i as u64) % self.slot_count as u64) as usize;
            let off = slot * SLOT_BYTES;
            unsafe { (self.slots.va.add(off + SEQ_OFFSET) as *mut u64).write_unaligned(self.seq) };
            self.seq += 1;
            self.ents[i] = Entry { va: self.slots.va as u64 + off as u64, iova: self.slots.iova + off as u64, len: self.frame_len as u32, _pad: 0 };
        }
        let pushed = sh.tx.push(&self.ents[..n]);
        debug_assert_eq!(pushed, n);
        self.sent += n as u64;
        n
    }

    fn step_rx(&mut self) -> usize {
        let sh = unsafe { &*self.sh };
        let mut sum = self.seq_sum;
        let n = sh.rx.pop(self.batch, |e| {
            sum = sum.wrapping_add(unsafe { ((e.va as usize + SEQ_OFFSET) as *const u64).read_unaligned() });
        });
        self.seq_sum = sum;
        if n > 0 {
            self.released += n as u64;
            sh.released.0.store(self.released, Ordering::Release);
        }
        n
    }

    fn step_fwd(&mut self, mut m: Option<&mut Maglev<'_>>) -> usize {
        let sh = unsafe { &*self.sh };
        let (src, dst) = (self.fwd_src, self.fwd_dst);
        let ents = &mut self.ents;
        let mut n = 0;
        sh.rx.pop(self.batch.min(sh.tx.room()), |e| {
            let frame = unsafe { core::slice::from_raw_parts_mut(e.va as *mut u8, e.len as usize) };
            let keep = match m.as_mut() {
                Some(m) => m.process(frame) != NO_BACKEND,
                None => true,
            };
            if keep {
                frame[6..12].copy_from_slice(&src);
                frame[0..6].copy_from_slice(&dst);
            }
            ents[n] = e;
            n += 1;
        });
        let pushed = sh.tx.push(&ents[..n]);
        debug_assert_eq!(pushed, n);
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
}

unsafe impl<P: Platform> Send for Driver<'_, P> {}

impl<'p, P: Platform> Driver<'p, P> {
    pub fn new(tx: TxQueue<'p, P>, k: usize) -> Self {
        Driver {
            tx, k, mode: Mode::Idle, batch: 1, rxs: Vec::new(), held: VecDeque::with_capacity(1024), handed: 0, base: 0, last_cmd: 0, next: 0,
            frames: [(0, 0); MAX_BATCH], ents: [Entry::default(); MAX_BATCH],
        }
    }

    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// Applies the block's phase command if it is new: ends the current phase (every frame the application holds
    /// goes back to its Rx queue, unsent entries are dropped), then starts the new one, in which this driver polls
    /// the queues k, k + c, .. of `queues` (every Rx queue of the device) for a phase of c pairs. Returns whether it
    /// applied one. The queues of a phase must be polled by no other driver.
    pub fn control(&mut self, sh: &Shared, queues: &[*mut RxQueue<'p, P>]) -> bool {
        let cmd = sh.cmd.0.load(Ordering::Acquire);
        if cmd == self.last_cmd {
            return false;
        }
        self.last_cmd = cmd;
        for &rx in &self.rxs {
            let rx = unsafe { &mut *rx };
            let pos = rx.position();
            rx.give_back_to(pos);
        }
        self.rxs.clear();
        self.held.clear();
        sh.tx.clear();
        let (mode, pairs, batch) = (Mode::of_code(cmd & 0xff), ((cmd >> 8) & 0xff) as usize, ((cmd >> 16) & 0xffff) as usize);
        self.mode = mode;
        self.batch = batch.clamp(1, MAX_BATCH);
        if mode.polls() {
            self.rxs.extend((self.k..queues.len()).step_by(pairs.max(1)).map(|q| queues[q]));
        }
        self.handed = 0;
        self.next = 0;
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
        if self.mode == Mode::Idle {
            return (0, 0);
        }
        self.tx.clean();
        let done = self.tx.completed.saturating_sub(self.base);
        sh.completed.0.store(done, Ordering::Release);
        let released = match self.mode {
            Mode::Rx => sh.released.0.load(Ordering::Acquire),
            _ => done,
        };
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
            sh.tx.pop(MAX_BATCH.min(self.tx.room()), |e| {
                frames[n] = (e.iova, e.len as u16);
                n += 1;
            });
            if n > 0 {
                sent = self.tx.send_frames(&frames[..n]);
                debug_assert_eq!(sent, n);
            }
        }
        let mut handed = 0;
        if self.mode.polls() && !self.rxs.is_empty() {
            let q = self.rxs.len();
            for _ in 0..q {
                let want = (self.batch - handed).min(sh.rx.room());
                if want == 0 {
                    break;
                }
                let i = self.next;
                self.next = if i + 1 == q { 0 } else { i + 1 };
                let rx = unsafe { &mut *self.rxs[i] };
                let ents = &mut self.ents;
                let mut n = 0;
                let took = rx.take(want, |f| {
                    ents[n] = Entry { va: f.va as u64, iova: f.iova, len: f.len as u32, _pad: 0 };
                    n += 1;
                });
                if took == 0 {
                    continue;
                }
                let pushed = sh.rx.push(&ents[..n]);
                debug_assert_eq!(pushed, n);
                self.handed += n as u64;
                self.held.push_back((self.handed, i, rx.position()));
                handed += n;
            }
        }
        (sent, handed)
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
}
