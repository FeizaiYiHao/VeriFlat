//! The per-queue benchmark loop both front ends run: one thread per queue pair transmits one fixed UDP frame in
//! batches and counts what its Rx queue receives, for a fixed number of TSC cycles.

use crate::maglev::{Maglev, NO_BACKEND};
use crate::packet::UdpFrame;
use alloc::collections::VecDeque;
use crate::queue::{RxCounts, RxQueue, TxQueue};
use crate::{DmaRegion, Error, Platform, Result};

/// A frame in DMA memory that a Tx queue sends over and over, in `count` copies of `slot` bytes each that the queue
/// sends in turn: the device reads one buffer address over and over far more slowly than distinct ones (on a c6620
/// in dom0 with the IOMMU on, about 12 to 26 million frames per second from one buffer against line rate from eight).
#[derive(Clone, Copy, Debug)]
pub struct TxFrame {
    /// All copies; copy i at `buf.iova + i * slot`.
    pub buf: DmaRegion,
    pub len: u16,
    pub count: usize,
    /// Bytes per copy: `SLOT`, or the frame rounded up to 128 bytes for a jumbo frame. Feature `payload-path` only; the
    /// default build has `SLOT`.
    #[cfg(feature = "payload-path")]
    pub slot: usize,
}

impl TxFrame {
    pub const SLOT: usize = 2048;

    pub fn new(p: &impl Platform, frame: &UdpFrame) -> Result<TxFrame> {
        Self::pool(p, frame, 1)
    }

    /// `count` copies of `frame`.
    pub fn pool(p: &impl Platform, frame: &UdpFrame, count: usize) -> Result<TxFrame> {
        #[cfg(feature = "payload-path")]
        let slot = Self::SLOT.max(frame.len.next_multiple_of(128));
        #[cfg(not(feature = "payload-path"))]
        let slot = Self::SLOT;
        let buf = p.dma_alloc(count.max(1) * slot, 128).ok_or(Error::NoDmaMemory)?;
        #[cfg(feature = "payload-path")]
        let mut f = TxFrame { buf, len: 0, count: count.max(1), slot };
        #[cfg(not(feature = "payload-path"))]
        let mut f = TxFrame { buf, len: 0, count: count.max(1) };
        f.write(frame);
        Ok(f)
    }

    /// Bytes per copy.
    #[inline(always)]
    pub fn slot_bytes(&self) -> usize {
        #[cfg(feature = "payload-path")]
        return self.slot;
        #[cfg(not(feature = "payload-path"))]
        return Self::SLOT;
    }

    /// Writes `frame` into every copy (while no queue sends this frame).
    pub fn write(&mut self, frame: &UdpFrame) {
        for i in 0..self.count {
            frame.write(unsafe { core::slice::from_raw_parts_mut(self.buf.va.add(i * self.slot_bytes()), self.slot_bytes()) });
        }
        self.len = frame.len as u16;
    }

    /// Writes `frame` into copy i only (its length must be the one of every copy).
    pub fn write_copy(&mut self, i: usize, frame: &UdpFrame) {
        assert!(i < self.count && frame.len as u16 == self.len);
        frame.write(unsafe { core::slice::from_raw_parts_mut(self.buf.va.add(i * self.slot_bytes()), self.slot_bytes()) });
    }

    /// Copy i as (IOVA, length).
    pub fn copy(&self, i: usize) -> (u64, u16) {
        (self.buf.iova + (i * self.slot_bytes()) as u64, self.len)
    }
}

/// What one worker measured.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkerResult {
    /// Frames the device reported sent within the window.
    pub tx_packets: u64,
    pub rx: RxCounts,
    /// TSC cycles from the first to the last iteration.
    pub cycles: u64,
}

/// Tx batches queued per iteration and Rx descriptors polled per iteration.
const TX_BATCHES: usize = 4;
const RX_BUDGET: usize = 256;
const RX_HOLDOFF_MIN: usize = 32;
const RX_HOLDOFF_CYCLES: u64 = 4000;

/// Runs one queue pair for `cycles` TSC cycles: sends `frame` (if any) and counts received frames (if `rx`).
pub fn run_queue_pair<P: Platform>(
    p: &P,
    tx: &mut TxQueue<'_, P>,
    rx: &mut RxQueue<'_, P>,
    frame: Option<&TxFrame>,
    do_rx: bool,
    cycles: u64,
) -> WorkerResult {
    let (tx0, rx0) = (tx.completed, rx.counts);
    let start = p.tsc();
    let end = start + cycles;
    let (mut now, mut cursor) = (start, 0);
    while now < end {
        if let Some(f) = frame {
            tx.clean();
            tx.send_batches_pool(f.buf.iova, f.slot_bytes(), f.count, f.len, &mut cursor, TX_BATCHES);
        }
        if do_rx {
            let got = rx.poll(RX_BUDGET);
            // An Rx-only queue that found few frames waits RX_HOLDOFF_CYCLES before it looks again: polling the
            // descriptor line the device is writing back slows the device's write-back and with it the whole port
            // (c6620, Linux, turbo off: one Rx-only queue took 23.6 Mpps without the wait, 92 with 4000 cycles).
            if frame.is_none() && got < RX_HOLDOFF_MIN {
                let until = p.tsc() + RX_HOLDOFF_CYCLES;
                while p.tsc() < until {
                    core::hint::spin_loop();
                }
            }
        }
        now = p.tsc();
    }
    tx.clean();
    WorkerResult {
        tx_packets: tx.completed - tx0,
        rx: RxCounts { packets: rx.counts.packets - rx0.packets, bytes: rx.counts.bytes - rx0.bytes, errors: rx.counts.errors - rx0.errors },
        cycles: now - start,
    }
}

/// Runs a Tx-only sender for `cycles` TSC cycles that sends `frames` round robin (see `TxQueue::send_batches_from`).
pub fn run_sender<P: Platform>(p: &P, tx: &mut TxQueue<'_, P>, frames: &[(u64, u16)], cycles: u64) -> WorkerResult {
    let tx0 = tx.completed;
    let start = p.tsc();
    let end = start + cycles;
    let (mut now, mut cursor) = (start, 0);
    while now < end {
        tx.clean();
        tx.send_batches_from(frames, &mut cursor, TX_BATCHES);
        now = p.tsc();
    }
    tx.clean();
    WorkerResult { tx_packets: tx.completed - tx0, rx: RxCounts::default(), cycles: now - start }
}

/// Frames a forwarding worker takes from one Rx queue at a time.
const FWD_BATCH: usize = 32;

/// Runs a forwarding worker for `cycles` TSC cycles, the loop of Atmosphere's maglev benchmark: it takes the frames
/// its Rx queues `rxs` received (in turn, up to `FWD_BATCH` from each), and for each computes its backend with
/// `Maglev::process`, rewrites its source MAC to `src` and its destination MAC to `dst` when it has one, and
/// transmits it from its Rx buffer on `tx` (zero copy, as the original). An Rx buffer goes back to its queue once the
/// device reported the frame sent; at the end every taken buffer goes back (a frame still queued may then be sent
/// with bytes of a newer frame, which only the receiver sees). Result: frames the device reported sent, frames taken.
pub fn run_forwarder<P: Platform>(
    p: &P,
    tx: &mut TxQueue<'_, P>,
    rxs: &mut [&mut RxQueue<'_, P>],
    m: &mut Maglev<'_>,
    src: [u8; 6],
    dst: [u8; 6],
    cycles: u64,
) -> WorkerResult {
    tx.clean();
    let tx0 = tx.completed;
    let rx0: alloc::vec::Vec<RxCounts> = rxs.iter().map(|r| r.counts).collect();
    // Frames queued on `tx` since the start of the run as the device will count them, and per forwarded batch the
    // count that frees it with the Rx queue and position to hand back to.
    let mut queued = tx.completed + tx.in_flight() as u64;
    let mut held: VecDeque<(u64, usize, usize)> = VecDeque::with_capacity(rxs.len() * 64);
    let mut frames = [(0u64, 0u16); FWD_BATCH];
    let start = p.tsc();
    let end = start + cycles;
    let mut now = start;
    while now < end {
        let mut pass = 0;
        for i in 0..rxs.len() {
            tx.clean();
            while let Some(&(done, q, pos)) = held.front() {
                if tx.completed < done {
                    break;
                }
                rxs[q].give_back_to(pos);
                held.pop_front();
            }
            let mut n = 0;
            rxs[i].take(FWD_BATCH, |f| {
                let frame = unsafe { core::slice::from_raw_parts_mut(f.va as *mut u8, f.len as usize) };
                if m.process(frame) != NO_BACKEND {
                    frame[6..12].copy_from_slice(&src);
                    frame[0..6].copy_from_slice(&dst);
                }
                frames[n] = (f.iova, f.len);
                n += 1;
            });
            if n == 0 {
                continue;
            }
            pass += n;
            let mut sent = 0;
            while sent < n {
                sent += tx.send_frames(&frames[sent..n]);
                if sent < n {
                    tx.clean();
                }
            }
            queued += n as u64;
            held.push_back((queued, i, rxs[i].position()));
        }
        // As an Rx-only queue (`run_queue_pair`): after a pass over its queues that found few frames the worker waits
        // before it polls again. Without it, 28 workers polling their rings at about 4 Mpps each overflowed the
        // device's Rx packet buffer (c6620, Linux: 63 Mpps forwarded at 28 workers against 115 at 8).
        if pass < RX_HOLDOFF_MIN {
            let until = p.tsc() + RX_HOLDOFF_CYCLES;
            while p.tsc() < until {
                core::hint::spin_loop();
            }
        }
        now = p.tsc();
    }
    tx.clean();
    for r in rxs.iter_mut() {
        let pos = r.position();
        r.give_back_to(pos);
    }
    let mut rx = RxCounts::default();
    for (r, c0) in rxs.iter().zip(&rx0) {
        rx.packets += r.counts.packets - c0.packets;
        rx.bytes += r.counts.bytes - c0.bytes;
        rx.errors += r.counts.errors - c0.errors;
    }
    WorkerResult { tx_packets: tx.completed - tx0, rx, cycles: now - start }
}

/// Packets per second of `packets` over `cycles` at `tsc_hz`.
pub fn rate(packets: u64, cycles: u64, tsc_hz: u64) -> u64 {
    if cycles == 0 {
        return 0;
    }
    (packets as u128 * tsc_hz as u128 / cycles as u128) as u64
}

/// Line rate in packets per second of frames of `frame_len` bytes (CRC included) at `mbps`: each frame also takes
/// 8 bytes of preamble and 12 of inter-frame gap.
pub fn line_rate_pps(frame_len: u64, mbps: u64) -> u64 {
    mbps * 1_000_000 / ((frame_len + 20) * 8)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rates() {
        assert_eq!(rate(1_000_000, 2_000_000_000, 2_000_000_000), 1_000_000);
        assert_eq!(rate(5, 0, 1), 0);
        assert_eq!(line_rate_pps(64, 100_000), 148_809_523);
        assert_eq!(line_rate_pps(64, 25_000), 37_202_380);
    }
}
