//! The batch exchange of the cross-process benchmark: an application hands a batch of frames to the driver thread
//! that owns a queue pair and gets back the frames that queue received, through a `Mailbox` and packet buffers both
//! sides see. The driver side (`DriverQueue::serve`) runs once per request, called directly when the driver is linked
//! into the application or once per IPC round trip when it is a process of its own; the application side
//! (`AppQueue::prepare` before, `AppQueue::finish` after) is the same either way, so the two front ends differ only in
//! how a request reaches the driver.
//!
//! Zero copy both ways: the application writes each frame into a Tx slot of its pair's slot array and the driver
//! hands the slot's address to the device; the driver hands out received frames in place, in Rx buffers the
//! application can read, and re-arms their descriptors only at the next request, when the application is done with
//! them. Tx slots are used in ring order and a slot is free again once the device reported its frame sent.

use crate::packet::{UdpFrame, HEADERS};
use crate::queue::{RxQueue, TxQueue};
use crate::{DmaRegion, Platform};

/// Most frames per request and per reply.
pub const MAX_BATCH: usize = 32;
/// Bytes per Tx slot: the largest frame fits.
pub const SLOT_BYTES: usize = 2048;
/// Where a frame carries its sequence number (the first payload bytes after the UDP header).
pub const SEQ_OFFSET: usize = HEADERS;

/// A received frame in a reply: its address (VA, which the front ends keep equal to the IOVA) and length.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct RxEntry {
    pub addr: u64,
    pub len: u32,
    pub _pad: u32,
}

/// The request and reply of one queue pair, on a page of its own.
#[repr(C, align(4096))]
pub struct Mailbox {
    /// Request: the slot of the first frame (the others follow in ring order), how many frames, their lengths, and
    /// how many received frames the application takes at most.
    pub tx_first: u32,
    pub tx_count: u32,
    pub rx_budget: u32,
    pub tx_len: [u16; MAX_BATCH],
    /// Reply: the received frames, valid until the next request, and the frames the device reported sent so far.
    pub rx_count: u32,
    pub tx_completed: u64,
    pub rx: [RxEntry; MAX_BATCH],
}

const _: () = assert!(core::mem::size_of::<Mailbox>() == 4096);

/// The driver's side of one queue pair: its queues and the application's Tx slot array.
pub struct DriverQueue<'p, P: Platform> {
    pub tx: TxQueue<'p, P>,
    pub rx: RxQueue<'p, P>,
    slots: u64,
    slot_count: usize,
    frames: [(u64, u16); MAX_BATCH],
    completed: u64,
}

impl<'p, P: Platform> DriverQueue<'p, P> {
    /// A driver queue over Tx slots `[slots_iova, slots_iova + slot_count * SLOT_BYTES)`. The Tx ring must hold
    /// more descriptors than there are slots, so every request fits.
    pub fn new(tx: TxQueue<'p, P>, rx: RxQueue<'p, P>, slots_iova: u64, slot_count: usize, tx_ring: usize) -> Self {
        assert!(slot_count < tx_ring, "the Tx ring must hold more descriptors than there are Tx slots");
        DriverQueue { tx, rx, slots: slots_iova, slot_count, frames: [(0, 0); MAX_BATCH], completed: 0 }
    }

    /// Serves one request in `mb`: re-arms the frames of the last reply, reclaims sent frames, queues the request's
    /// frames, and replies with up to `rx_budget` received frames; returns how many.
    pub fn serve(&mut self, mb: &mut Mailbox) -> usize {
        self.rx.give_back();
        self.completed += self.tx.clean_frames() as u64;
        let n = (mb.tx_count as usize).min(MAX_BATCH);
        let first = mb.tx_first as usize;
        for i in 0..n {
            let slot = (first + i) % self.slot_count;
            self.frames[i] = (self.slots + (slot * SLOT_BYTES) as u64, mb.tx_len[i]);
        }
        let sent = self.tx.send_frames(&self.frames[..n]);
        debug_assert_eq!(sent, n);
        let mut count = 0;
        let rx = &mut mb.rx;
        self.rx.take((mb.rx_budget as usize).min(MAX_BATCH), |f| {
            rx[count] = RxEntry { addr: f.va as u64, len: f.len as u32, _pad: 0 };
            count += 1;
        });
        mb.rx_count = count as u32;
        mb.tx_completed = self.completed;
        count
    }
}

/// What `AppQueue::finish` found wrong in a reply when it checks the frames (loopback runs).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BadFrame {
    pub expected_seq: u64,
    pub seq: u64,
    pub len: u32,
}

/// The application's side of one queue pair: the mailbox, the Tx slots, and the counters.
pub struct AppQueue {
    mb: *mut Mailbox,
    slots: *mut u8,
    slot_count: usize,
    frame_len: u16,
    /// Frames handed to the driver and frames it reported sent, since the start.
    pub sent: u64,
    pub completed: u64,
    /// Frames received, and the sequence number the next received frame must carry when `check` is set.
    pub received: u64,
    expect_seq: u64,
    check: bool,
}

unsafe impl Send for AppQueue {}

impl AppQueue {
    /// An application queue over `mb` and the Tx slots of `slots` (`slot_count * SLOT_BYTES` bytes), which gets
    /// `frame` written into every slot. With `check`, every received frame must be the next frame this queue sent
    /// (a loopback to the same queue).
    pub fn new(mb: *mut Mailbox, slots: DmaRegion, slot_count: usize, frame: &UdpFrame, check: bool) -> AppQueue {
        assert!(slots.len >= slot_count * SLOT_BYTES && frame.len <= SLOT_BYTES);
        for i in 0..slot_count {
            frame.write(unsafe { core::slice::from_raw_parts_mut(slots.va.add(i * SLOT_BYTES), SLOT_BYTES) });
        }
        AppQueue { mb, slots: slots.va, slot_count, frame_len: frame.len as u16, sent: 0, completed: 0, received: 0, expect_seq: 0, check }
    }

    /// Writes up to `batch` frames, as many as there are free slots, each with its sequence number, into the
    /// request; returns how many.
    pub fn prepare(&mut self, batch: usize) -> usize {
        let free = self.slot_count - (self.sent - self.completed) as usize;
        let n = batch.min(MAX_BATCH).min(free);
        let mb = unsafe { &mut *self.mb };
        let first = (self.sent % self.slot_count as u64) as usize;
        for i in 0..n {
            let slot = (first + i) % self.slot_count;
            let seq = self.sent + i as u64;
            unsafe { (self.slots.add(slot * SLOT_BYTES + SEQ_OFFSET) as *mut u64).write_unaligned(seq) };
            mb.tx_len[i] = self.frame_len;
        }
        mb.tx_first = first as u32;
        mb.tx_count = n as u32;
        mb.rx_budget = batch.min(MAX_BATCH) as u32;
        self.sent += n as u64;
        n
    }

    /// Reads the reply: reads the sequence number of every received frame (and checks it with `check`) and notes
    /// the frames the device sent; returns the frames received.
    pub fn finish(&mut self) -> Result<usize, BadFrame> {
        let mb = unsafe { &*self.mb };
        self.completed = mb.tx_completed;
        let n = (mb.rx_count as usize).min(MAX_BATCH);
        for e in &mb.rx[..n] {
            let seq = unsafe { ((e.addr as usize + SEQ_OFFSET) as *const u64).read_unaligned() };
            if self.check {
                if seq != self.expect_seq || e.len != self.frame_len as u32 {
                    return Err(BadFrame { expected_seq: self.expect_seq, seq, len: e.len });
                }
                self.expect_seq += 1;
            }
        }
        self.received += n as u64;
        Ok(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mock::{Mock, MOCK_MAC};
    use crate::packet::steering_mac;
    use crate::{Config, Device};

    #[test]
    fn linked_exchange_over_the_model() {
        let m = Mock::new(true);
        let (n, slots, tx_ring) = (3, 64, 128);
        let mut dev = Device::new(&m, Config { queues: n, tx_ring, rx_ring: 64, tx_batch: 32, ..Default::default() }).unwrap();
        let mut pairs: Vec<(Box<Mailbox>, AppQueue, DriverQueue<'_, Mock>)> = Vec::new();
        for (q, (tx, rx)) in dev.take_queues().into_iter().enumerate() {
            let region = m.dma_alloc(slots * SLOT_BYTES, 4096).unwrap();
            let frame = UdpFrame {
                dst_mac: steering_mac(MOCK_MAC, q),
                src_mac: MOCK_MAC,
                src_ip: [10, 0, 0, 1],
                dst_ip: [10, 0, 1, 1],
                src_port: 1024,
                dst_port: 5000,
                len: 60,
            };
            let mut mb = Box::new(Mailbox { tx_first: 0, tx_count: 0, rx_budget: 0, tx_len: [0; MAX_BATCH], rx_count: 0, tx_completed: 0, rx: [RxEntry::default(); MAX_BATCH] });
            let app = AppQueue::new(&mut *mb, region, slots, &frame, true);
            pairs.push((mb, app, DriverQueue::new(tx, rx, region.iova, slots, tx_ring)));
        }
        for round in 0..200 {
            for (_, app, drv) in pairs.iter_mut() {
                let batch = if round % 2 == 0 { 1 } else { 32 };
                let sent = app.prepare(batch);
                assert!(sent > 0);
                let mb = unsafe { &mut *app.mb };
                assert_eq!(drv.serve(mb), sent.min(batch));
                assert_eq!(app.finish(), Ok(sent));
            }
        }
        for (_, app, _) in &pairs {
            assert_eq!(app.received, 100 * 33);
            assert_eq!(app.sent, 100 * 33);
            // Write-backs come per aligned batch of 32 and are reclaimed at the next request: up to 63 frames behind.
            assert!(app.completed >= app.sent - 63);
        }
        assert!(m.rxqs().values().all(|r| r.dropped == 0));
    }
}
