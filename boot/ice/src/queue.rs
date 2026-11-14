//! Tx and Rx queues in polling mode. Each is owned by one thread; it touches only its own ring, its own buffers and
//! its own tail register.

use crate::desc::{RxDesc, TxDesc, RX_STATUS0_DD, RX_STATUS0_EOF, RX_STATUS0_RXE};
use crate::regs;
use crate::ring::Ring;
use crate::{DmaRegion, Platform};
use core::ptr;
use core::sync::atomic::{fence, Ordering};

/// A Tx queue. Descriptors go out in batches of `batch` (a divisor of the ring size); the last descriptor of each
/// batch asks for a write-back, and a batch is reclaimed once that descriptor reads back as done.
pub struct TxQueue<'p, P: Platform> {
    p: &'p P,
    /// The PF queue index.
    pub index: usize,
    ring: Ring,
    descs: DmaRegion,
    batch: usize,
    next_to_use: usize,
    next_to_clean: usize,
    /// Frames the device reported sent.
    pub completed: u64,
}

impl<'p, P: Platform> TxQueue<'p, P> {
    pub(crate) fn new(p: &'p P, index: usize, descs: DmaRegion, size: usize, batch: usize) -> Self {
        assert!(size % batch == 0, "the batch must divide the ring size");
        TxQueue { p, index, ring: Ring::new(size), descs, batch, next_to_use: 0, next_to_clean: 0, completed: 0 }
    }

    pub fn ring_iova(&self) -> u64 {
        self.descs.iova
    }

    fn desc(&self, i: usize) -> *mut TxDesc {
        unsafe { (self.descs.va as *mut TxDesc).add(i) }
    }

    /// Reclaims every finished batch; returns the descriptors reclaimed.
    pub fn clean(&mut self) -> usize {
        let mut n = 0;
        while self.ring.distance(self.next_to_clean, self.next_to_use) >= self.batch {
            let last = self.ring.add(self.next_to_clean, self.batch - 1);
            let qw1 = unsafe { ptr::read_volatile(&(*self.desc(last)).cmd_type_offset_bsz) };
            if !TxDesc::is_done(qw1) {
                break;
            }
            self.next_to_clean = self.ring.add(self.next_to_clean, self.batch);
            n += self.batch;
        }
        self.completed += n as u64;
        n
    }

    /// Queues up to `batches` batches of the frame of `len` bytes at `iova` and rings the doorbell; returns the frames
    /// queued. Every descriptor points at the same buffer, which the device only reads.
    pub fn send_batches(&mut self, iova: u64, len: u16, batches: usize) -> usize {
        // The ring keeps one batch empty, so a full ring differs from an empty one.
        let free_batches = (self.ring.size() - self.ring.distance(self.next_to_clean, self.next_to_use)) / self.batch - 1;
        let k = batches.min(free_batches);
        if k == 0 {
            return 0;
        }
        for _ in 0..k {
            for j in 0..self.batch {
                let d = TxDesc::data(iova, len, j == self.batch - 1);
                unsafe { ptr::write_volatile(self.desc(self.next_to_use), d) };
                self.next_to_use = self.ring.add(self.next_to_use, 1);
            }
        }
        fence(Ordering::Release);
        self.p.write32(regs::qtx_comm_dbell(self.index), self.next_to_use as u32);
        k * self.batch
    }

    /// As `send_batches`, but descriptor i of the stream points at copy `(*cursor + i) % count` of `count` copies of the
    /// frame, `slot` bytes apart from `iova`; `cursor` advances past the descriptors queued. Reclaims with `clean`.
    pub fn send_batches_pool(&mut self, iova: u64, slot: usize, count: usize, len: u16, cursor: &mut usize, batches: usize) -> usize {
        let free_batches = (self.ring.size() - self.ring.distance(self.next_to_clean, self.next_to_use)) / self.batch - 1;
        let k = batches.min(free_batches);
        if k == 0 {
            return 0;
        }
        let mut c = *cursor;
        for _ in 0..k {
            for j in 0..self.batch {
                let d = TxDesc::data(iova + (c * slot) as u64, len, j == self.batch - 1);
                c = if c + 1 >= count { 0 } else { c + 1 };
                unsafe { ptr::write_volatile(self.desc(self.next_to_use), d) };
                self.next_to_use = self.ring.add(self.next_to_use, 1);
            }
        }
        *cursor = c;
        fence(Ordering::Release);
        self.p.write32(regs::qtx_comm_dbell(self.index), self.next_to_use as u32);
        k * self.batch
    }

    /// As `send_batches`, but descriptor i of the stream points at `frames[(*cursor + i) % frames.len()]`, and
    /// `cursor` advances past the descriptors queued: a sender that stands in for several Rx queues of a reflected
    /// stream. Reclaims with `clean`.
    pub fn send_batches_from(&mut self, frames: &[(u64, u16)], cursor: &mut usize, batches: usize) -> usize {
        let free_batches = (self.ring.size() - self.ring.distance(self.next_to_clean, self.next_to_use)) / self.batch - 1;
        let k = batches.min(free_batches);
        if k == 0 || frames.is_empty() {
            return 0;
        }
        for _ in 0..k {
            for j in 0..self.batch {
                let (iova, len) = frames[*cursor];
                *cursor = if *cursor + 1 == frames.len() { 0 } else { *cursor + 1 };
                unsafe { ptr::write_volatile(self.desc(self.next_to_use), TxDesc::data(iova, len, j == self.batch - 1)) };
                self.next_to_use = self.ring.add(self.next_to_use, 1);
            }
        }
        fence(Ordering::Release);
        self.p.write32(regs::qtx_comm_dbell(self.index), self.next_to_use as u32);
        k * self.batch
    }

    /// Queues one descriptor per frame of `frames` (IOVA, length), as many as the ring has room for, and rings the
    /// doorbell once; returns the frames queued. Only the last descriptor of each aligned batch of `batch` asks for a
    /// write-back (as DPDK's `tx_rs_thresh`), so a batch is reclaimed once its whole batch has been queued: a write-back
    /// per frame, 16-byte device writes into lines the CPU polls, held the whole port to about 11.5 Mpps on c6620
    /// (2026-11-14, 28 queues). A queue that sends this way reclaims with `clean_frames`.
    pub fn send_frames(&mut self, frames: &[(u64, u16)]) -> usize {
        let k = frames.len().min(self.ring.free(self.next_to_use, self.next_to_clean));
        if k == 0 {
            return 0;
        }
        for &(iova, len) in &frames[..k] {
            let rs = (self.next_to_use + 1) % self.batch == 0;
            unsafe { ptr::write_volatile(self.desc(self.next_to_use), TxDesc::data(iova, len, rs)) };
            self.next_to_use = self.ring.add(self.next_to_use, 1);
        }
        fence(Ordering::Release);
        self.p.write32(regs::qtx_comm_dbell(self.index), self.next_to_use as u32);
        k
    }

    /// Reclaims, in order, every whole batch `send_frames` queued that the device reported sent; returns the frames.
    pub fn clean_frames(&mut self) -> usize {
        self.clean()
    }

    /// Descriptors queued and not reclaimed yet.
    pub fn in_flight(&self) -> usize {
        self.ring.distance(self.next_to_clean, self.next_to_use)
    }
}

/// Counters of one Rx queue.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RxCounts {
    pub packets: u64,
    pub bytes: u64,
    /// Frames with the receive error bit or without end of frame (a frame larger than one buffer).
    pub errors: u64,
}

/// A received frame that `RxQueue::take` hands out, valid until the next `give_back`.
#[derive(Clone, Copy, Debug)]
pub struct RxFrame {
    pub va: *const u8,
    pub iova: u64,
    pub len: u16,
}

/// An Rx queue whose every descriptor keeps its own buffer: a received frame is counted and the descriptor re-armed
/// with the same buffer, at once (`poll`) or once its reader is done with the frame (`take`, then `give_back`).
pub struct RxQueue<'p, P: Platform> {
    p: &'p P,
    pub index: usize,
    ring: Ring,
    descs: DmaRegion,
    bufs: alloc::vec::Vec<DmaRegion>,
    next_to_clean: usize,
    /// The first descriptor taken and not given back yet; `next_to_clean` when none is held.
    next_to_arm: usize,
    /// The Rx tail `give_back` wrote last.
    tail: usize,
    pub counts: RxCounts,
}

impl<'p, P: Platform> RxQueue<'p, P> {
    /// A queue whose descriptor `i` uses `bufs[i]`. Arms every descriptor; the device gets them with `start`.
    pub(crate) fn new(p: &'p P, index: usize, descs: DmaRegion, bufs: alloc::vec::Vec<DmaRegion>) -> Self {
        let tail = bufs.len() - 1;
        let q = RxQueue { p, index, ring: Ring::new(bufs.len()), descs, bufs, next_to_clean: 0, next_to_arm: 0, tail, counts: RxCounts::default() };
        for i in 0..q.ring.size() {
            q.arm(i);
        }
        q
    }

    pub fn ring_iova(&self) -> u64 {
        self.descs.iova
    }

    pub fn size(&self) -> usize {
        self.ring.size()
    }

    fn desc(&self, i: usize) -> *mut RxDesc {
        unsafe { (self.descs.va as *mut RxDesc).add(i) }
    }

    fn arm(&self, i: usize) {
        unsafe { ptr::write_volatile(self.desc(i), RxDesc::read(self.bufs[i].iova)) };
    }

    /// Hands every descriptor but one to the device.
    pub(crate) fn start(&self) {
        fence(Ordering::Release);
        self.p.write32(regs::qrx_tail(self.index), self.ring.sub(0, 1) as u32);
    }

    /// Counts and re-arms up to `budget` received frames; returns how many there were. Not for a queue that holds
    /// frames `take` handed out.
    pub fn poll(&mut self, budget: usize) -> usize {
        debug_assert_eq!(self.next_to_arm, self.next_to_clean, "poll of an Rx queue holding taken frames");
        let mut n = 0;
        while n < budget {
            let d = self.desc(self.next_to_clean);
            let qw1 = unsafe { ptr::read_volatile(&(*d).qw[1]) };
            let status = RxDesc::status0(qw1);
            if status & RX_STATUS0_DD == 0 {
                break;
            }
            fence(Ordering::Acquire);
            let qw0 = unsafe { ptr::read_volatile(&(*d).qw[0]) };
            if status & RX_STATUS0_RXE != 0 || status & RX_STATUS0_EOF == 0 {
                self.counts.errors += 1;
            } else {
                self.counts.packets += 1;
                self.counts.bytes += RxDesc::pkt_len(qw0) as u64;
            }
            self.arm(self.next_to_clean);
            self.next_to_clean = self.ring.add(self.next_to_clean, 1);
            n += 1;
        }
        if n > 0 {
            // The re-armed descriptors go back to the device: it may fill up to the one before the next to clean. The
            // device ignores the low 3 bits of the Rx tail (the Linux driver bumps it in steps of 8), which only hands
            // it fewer descriptors than written, never more.
            fence(Ordering::Release);
            self.tail = self.ring.sub(self.next_to_clean, 1);
            self.p.write32(regs::qrx_tail(self.index), self.tail as u32);
        }
        self.next_to_arm = self.next_to_clean;
        n
    }

    /// Counts up to `budget` received frames and hands each good one to `f` without re-arming its descriptor, so
    /// that the device cannot overwrite it before `give_back`; returns the descriptors taken. The device fills no
    /// descriptor past the tail of the last `give_back`, so it never reaches the taken ones.
    pub fn take(&mut self, budget: usize, mut f: impl FnMut(RxFrame)) -> usize {
        let mut n = 0;
        while n < budget {
            let d = self.desc(self.next_to_clean);
            let qw1 = unsafe { ptr::read_volatile(&(*d).qw[1]) };
            let status = RxDesc::status0(qw1);
            if status & RX_STATUS0_DD == 0 {
                break;
            }
            fence(Ordering::Acquire);
            let qw0 = unsafe { ptr::read_volatile(&(*d).qw[0]) };
            if status & RX_STATUS0_RXE != 0 || status & RX_STATUS0_EOF == 0 {
                self.counts.errors += 1;
            } else {
                let (len, buf) = (RxDesc::pkt_len(qw0), &self.bufs[self.next_to_clean]);
                self.counts.packets += 1;
                self.counts.bytes += len as u64;
                f(RxFrame { va: buf.va, iova: buf.iova, len });
            }
            self.next_to_clean = self.ring.add(self.next_to_clean, 1);
            n += 1;
        }
        n
    }

    /// Re-arms every descriptor taken since the last call and hands them back to the device.
    pub fn give_back(&mut self) {
        if self.next_to_arm == self.next_to_clean {
            return;
        }
        while self.next_to_arm != self.next_to_clean {
            self.arm(self.next_to_arm);
            self.next_to_arm = self.ring.add(self.next_to_arm, 1);
        }
        // The device ignores the low 3 bits of the Rx tail (see `poll`): a write that leaves the rest unchanged hands it
        // nothing, so it is skipped (a request of one frame would otherwise write the tail per frame).
        let tail = self.ring.sub(self.next_to_clean, 1);
        if tail & !7 != self.tail & !7 {
            fence(Ordering::Release);
            self.p.write32(regs::qrx_tail(self.index), tail as u32);
            self.tail = tail;
        }
    }

    /// The next descriptor `take` looks at: `give_back_to` this position hands back every frame taken so far.
    pub fn position(&self) -> usize {
        self.next_to_clean
    }

    /// Re-arms the descriptors taken before position `end` (an earlier `position`, in take order) and hands them back
    /// to the device; frames taken after `end` stay the reader's.
    pub fn give_back_to(&mut self, end: usize) {
        debug_assert!(self.ring.distance(self.next_to_arm, end) <= self.ring.distance(self.next_to_arm, self.next_to_clean));
        if self.next_to_arm == end {
            return;
        }
        while self.next_to_arm != end {
            self.arm(self.next_to_arm);
            self.next_to_arm = self.ring.add(self.next_to_arm, 1);
        }
        let tail = self.ring.sub(end, 1);
        if tail & !7 != self.tail & !7 {
            fence(Ordering::Release);
            self.p.write32(regs::qrx_tail(self.index), tail as u32);
            self.tail = tail;
        }
    }

    /// The received frame at descriptor `i` as the device wrote it, for tests and debugging: (length, status, bytes).
    pub fn peek(&self, i: usize) -> (u16, u16, &[u8]) {
        let d = unsafe { ptr::read_volatile(self.desc(i)) };
        let len = RxDesc::pkt_len(d.qw[0]);
        let data = unsafe { core::slice::from_raw_parts(self.bufs[i].va, (len as usize).min(self.bufs[i].len)) };
        (len, RxDesc::status0(d.qw[1]), data)
    }
}
