//! Port of Atmosphere's `nvme_driver/src/queue.rs`. The per-slot bookkeeping arrays are vectors on the
//! heap instead of inline arrays, so an `NvmeDevice` fits a thread stack; the unused random-block
//! generator and raw-address slots are left out; `complete` reports the command ID and `is_submittable` keeps one slot free (see there).

use super::device::num_lbas;
use super::dma::{allocate_dma, Dma, NvmeCommand, NvmeCompletion};
use super::BlockReq;
use alloc::vec;
use alloc::vec::Vec;
use core::arch::asm;

pub(crate) struct NvmeCommandQueue {
    pub data: Dma<[NvmeCommand; QUEUE_DEPTH]>,
    pub i: usize,
    pub raw_requests_vec: Vec<Option<Vec<u8>>>,
    pub breq_requests: Vec<Option<BlockReq>>,
    pub req_slot: Vec<bool>,
    block: u64,
}

impl NvmeCommandQueue {
    pub fn new() -> Result<NvmeCommandQueue, i32> {
        let module = Self {
            data: allocate_dma()?,
            i: 0,
            raw_requests_vec: (0..QUEUE_DEPTH).map(|_| None).collect(),
            breq_requests: vec![None; QUEUE_DEPTH],
            req_slot: vec![false; QUEUE_DEPTH],
            block: 0,
        };
        Ok(module)
    }

    pub fn submit(&mut self, entry: NvmeCommand) -> usize {
        self.data[self.i] = entry;
        self.data[self.i].cid = self.i as u16;
        self.i = (self.i + 1) % self.data.len();
        self.i
    }

    /// Atmosphere checks only the slot at the tail. A queue of N entries holds at most N - 1 commands:
    /// with all N slots taken the tail would wrap onto the head and the controller would see an empty
    /// queue, so this also keeps the next slot free.
    pub fn is_submittable(&self) -> bool {
        !self.req_slot[self.i] && !self.req_slot[(self.i + 1) % self.req_slot.len()]
    }

    pub fn submit_request_breq(&mut self, entry: NvmeCommand, breq: BlockReq) -> Option<usize> {
        let cur_idx = self.i;
        if !self.req_slot[cur_idx] {
            self.data[cur_idx] = entry;
            self.data[cur_idx].cid = cur_idx as u16;
            self.data[cur_idx].cdw10 %= num_lbas() as u32;

            self.breq_requests[cur_idx] = Some(breq);

            self.req_slot[cur_idx] = true;
            self.i = (cur_idx + 1) % self.data.len();
            Some(self.i)
        } else {
            None
        }
    }

    pub fn submit_request_raw_vec(&mut self, entry: NvmeCommand, data: Vec<u8>) -> Option<usize> {
        let cur_idx = self.i;
        if !self.req_slot[cur_idx] {
            self.data[cur_idx] = entry;
            self.data[cur_idx].cid = cur_idx as u16;

            self.raw_requests_vec[cur_idx] = Some(data);
            self.data[cur_idx].cdw10 = self.block as u32;

            self.block = (self.block + 8) % num_lbas();

            self.req_slot[cur_idx] = true;
            self.i = (cur_idx + 1) % self.data.len();
            Some(self.i)
        } else {
            None
        }
    }
}

pub const QUEUE_DEPTH: usize = 1024;

pub(crate) struct NvmeCompletionQueue {
    pub data: Dma<[NvmeCompletion; QUEUE_DEPTH]>,
    pub i: usize,
    pub phase: bool,
    pub queue_len: usize,
}

impl NvmeCompletionQueue {
    pub fn new() -> Result<Self, i32> {
        Ok(Self { data: allocate_dma()?, i: 0, phase: true, queue_len: QUEUE_DEPTH })
    }

    pub(crate) fn complete(&mut self) -> Option<(usize, NvmeCompletion, usize)> {
        let entry = unsafe { core::ptr::read_volatile(self.data.as_ptr().add(self.i)) };
        if ((entry.status & 1) == 1) == self.phase {
            // Atmosphere returns the completion slot `self.i` here and takes it for the submission slot,
            // which holds only while the device completes in order; QEMU's NVMe can complete out of
            // order, so this returns the command ID, which `submit_*` set to the submission slot.
            let cq_entry = entry.cid as usize;
            self.i = (self.i + 1) % self.queue_len;
            if self.i == 0 {
                self.phase = !self.phase;
            }
            Some((self.i, entry, cq_entry))
        } else {
            None
        }
    }

    pub fn complete_spin(&mut self) -> (usize, NvmeCompletion, usize) {
        loop {
            if let Some(some) = self.complete() {
                return some;
            } else {
                unsafe {
                    asm!("pause");
                }
            }
        }
    }
}
