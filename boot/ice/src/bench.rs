//! The per-queue benchmark loop both front ends run: one thread per queue pair transmits one fixed UDP frame in
//! batches and counts what its Rx queue receives, for a fixed number of TSC cycles.

use crate::packet::UdpFrame;
use crate::queue::{RxCounts, RxQueue, TxQueue};
use crate::{DmaRegion, Error, Platform, Result};

/// A frame in DMA memory that a Tx queue sends over and over.
#[derive(Clone, Copy, Debug)]
pub struct TxFrame {
    pub buf: DmaRegion,
    pub len: u16,
}

impl TxFrame {
    pub fn new(p: &impl Platform, frame: &UdpFrame) -> Result<TxFrame> {
        let buf = p.dma_alloc(2048, 128).ok_or(Error::NoDmaMemory)?;
        frame.write(unsafe { core::slice::from_raw_parts_mut(buf.va, buf.len) });
        Ok(TxFrame { buf, len: frame.len as u16 })
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
    let mut now = start;
    while now < end {
        if let Some(f) = frame {
            tx.clean();
            tx.send_batches(f.buf.iova, f.len, TX_BATCHES);
        }
        if do_rx {
            rx.poll(RX_BUDGET);
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
