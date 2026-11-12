//! Port of Atmosphere's `nvme_driver/src/device.rs`. Changes: `sys_mresolve(x).0` is `x` (IOVA = VA);
//! the IOMMU "reload" hack in `identify_controller` is gone (the process attaches the function before
//! `init`); heapless strings are plain `str` slices; `x86::fence::sfence` is `_mm_sfence`; the ring
//! path checks completion status like the raw path; `shutdown` disables the controller at the end of a
//! configuration; the BlockReq-over-VecDeque paths and `poll_raw`, which the benchmark does not use, are
//! left out.

use super::cmd as nvme_cmd;
use super::dma::{allocate_dma, Dma, NvmeCommand, NvmeCompletion};
use super::pci::PciBarAddr;
use super::println;
use super::queue::{NvmeCommandQueue, NvmeCompletionQueue};
use super::regs::NvmeArrayRegs;
use super::regs::{NvmeRegs32, NvmeRegs64};
use super::ring_buffer::*;
use super::time::sys_ns_loopsleep;
use super::{BlockOp, BlockReq};
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::sync::atomic::{AtomicU64, Ordering};
use core::{fmt, ptr};

const ONE_MS_IN_NS: u64 = 1000_000;
const NVME_CC_ENABLE: u32 = 0x1;
const NVME_CSTS_RDY: u32 = 0x1;

/// Atmosphere's `static mut NUM_LBAS`. It lives in dom0's image, which the driver process shares, so the
/// client reads the value the driver process found.
static NUM_LBAS: AtomicU64 = AtomicU64::new(0);

#[inline(always)]
pub fn num_lbas() -> u64 {
    NUM_LBAS.load(Ordering::Relaxed)
}

/// Not in Atmosphere: log2 of namespace 1's LBA size, as `identify_ns` read it. The linked and ring paths
/// assume 512 bytes (8 LBAs per 4 KiB request); `parallel` uses this.
static LBA_SHIFT: AtomicU64 = AtomicU64::new(9);

pub fn lba_shift() -> u32 {
    LBA_SHIFT.load(Ordering::Relaxed) as u32
}

#[allow(dead_code)]
struct NvmeNamespace {
    pub id: u32,
    pub blocks: u64,
    pub block_size: u64,
}

pub struct NvmeStats {
    completed: u64,
    submitted: u64,
}

impl NvmeStats {
    pub fn get_stats(&self) -> (u64, u64) {
        (self.submitted, self.completed)
    }
    pub fn reset_stats(&mut self) {
        self.submitted = 0;
        self.completed = 0;
    }
}

impl fmt::Display for NvmeStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "submitted {} completed {}", self.submitted, self.completed)
    }
}

pub struct NvmeDevice {
    submission_queues: [NvmeCommandQueue; 2],
    completion_queues: [NvmeCompletionQueue; 2],
    bar: PciBarAddr,
    namespaces: Vec<NvmeNamespace>,
    dstrd: u16,
    pub stats: NvmeStats,
}

/// The printable prefix of a NUL-padded identify string.
fn id_str(bytes: &[u8]) -> &str {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    core::str::from_utf8(&bytes[..end]).unwrap_or("?").trim()
}

impl NvmeDevice {
    /// Resets and initializes an Nvme device.
    pub fn init(&mut self) {
        println!("Bar region base {:X}", self.bar.get_base());
        println!("Capabilities 0x{:X}", self.read_reg64(NvmeRegs64::CAP));
        println!("Version 0x{:X}", self.read_reg32(NvmeRegs32::VS));
        println!("Controller Configuration 0x{:X}", self.read_reg32(NvmeRegs32::CC));
        println!("Contoller Status 0x{:X}", self.read_reg32(NvmeRegs32::CSTS));

        // 7.6.1 Initialization (Nvme spec 1.4-2019.06.10)
        // Reset the controller
        self.reset_controller();

        // Configure admin queue
        self.configure_admin_queue();

        // Set entry sizes
        self.set_entry_sizes();

        // set enable bit
        self.write_flag32(NvmeRegs32::CC, 1);

        println!("Waiting for controller to become ready");
        // Wait for controller to become ready
        self.wait_set_reg32(NvmeRegs32::CSTS, NVME_CSTS_RDY, 7500);
        println!("Controller is ready!");

        self.identify_controller();

        self.identify_ns_list();

        self.identify_ns(1);

        self.create_io_queues();

        log::info!("Nvme Initialized!");
    }

    /// Not in Atmosphere: `init` without I/O queue pair 1, for `parallel`, which has to set the number of
    /// queues before it creates any (`set_number_of_queues`, `create_io_queue_pair`).
    pub fn init_admin_only(&mut self) {
        self.reset_controller();
        self.configure_admin_queue();
        self.set_entry_sizes();
        self.write_flag32(NvmeRegs32::CC, 1);
        self.wait_set_reg32(NvmeRegs32::CSTS, NVME_CSTS_RDY, 7500);
        self.identify_controller();
        self.identify_ns_list();
        self.identify_ns(1);
    }

    /// Not in Atmosphere: submits one admin command, spins for its completion, and returns it, or the status
    /// field when the command failed. Only the thread that owns this `NvmeDevice` issues admin commands.
    pub fn admin(&mut self, entry: NvmeCommand) -> Result<NvmeCompletion, u16> {
        let tail = self.submission_queues[0].submit(entry);
        self.submission_queue_tail(0, tail as u16);
        let (head, entry, _) = self.completion_queues[0].complete_spin();
        self.completion_queue_head(0, head as u16);
        if entry.status >> 1 != 0 {
            return Err(entry.status >> 1);
        }
        Ok(entry)
    }

    /// Not in Atmosphere: Set Features Number of Queues asking for `n` I/O submission and `n` I/O completion
    /// queues; returns how many of each the controller allocated, which may be more or fewer than `n`.
    pub fn set_number_of_queues(&mut self, n: u16) -> Result<(u16, u16), u16> {
        let cid = self.submission_queues[0].i as u16;
        let dw0 = self.admin(nvme_cmd::set_features_number_of_queues(cid, n - 1, n - 1))?.command_specific();
        Ok(((dw0 & 0xffff) as u16 + 1, (dw0 >> 16) as u16 + 1))
    }

    /// Not in Atmosphere: creates I/O completion queue `qid` of `len` entries at `cq`, polled (no interrupts),
    /// and I/O submission queue `qid` of `len` entries at `sq` that completes into it.
    pub fn create_io_queue_pair(&mut self, qid: u16, cq: usize, sq: usize, len: u16) -> Result<(), u16> {
        let cid = self.submission_queues[0].i as u16;
        self.admin(nvme_cmd::create_io_completion_queue(cid, qid, cq, len - 1))?;
        let cid = self.submission_queues[0].i as u16;
        self.admin(nvme_cmd::create_io_submission_queue(cid, qid, sq, len - 1, qid))?;
        Ok(())
    }

    /// Not in Atmosphere: the submission queue tail doorbell (`cq` false) or the completion queue head doorbell
    /// (`cq` true) of queue `qid`.
    pub fn doorbell(&self, qid: u16, cq: bool) -> *mut u32 {
        (self.bar.get_base() + 0x1000 + (4u64 << self.dstrd) * (2 * qid as u64 + cq as u64)) as *mut u32
    }

    /// Not in Atmosphere: CAP.MQES + 1, the most entries an I/O queue of this controller may have.
    pub fn max_queue_entries(&self) -> usize {
        (self.read_reg64(NvmeRegs64::CAP) & 0xffff) as usize + 1
    }

    pub fn new(bar: PciBarAddr) -> NvmeDevice {
        NvmeDevice {
            bar,
            submission_queues: [NvmeCommandQueue::new().unwrap(), NvmeCommandQueue::new().unwrap()],
            completion_queues: [NvmeCompletionQueue::new().unwrap(), NvmeCompletionQueue::new().unwrap()],
            namespaces: Vec::new(),
            dstrd: unsafe { ((ptr::read_volatile((bar.get_base() + NvmeRegs64::CAP as u64) as *const u64) >> 32) & 0b1111) as u16 },
            stats: NvmeStats { submitted: 0, completed: 0 },
        }
    }

    #[inline(always)]
    pub fn read_reg32(&self, reg: NvmeRegs32) -> u32 {
        unsafe { ptr::read_volatile((self.bar.get_base() + reg as u64) as *const u32) }
    }

    fn wait_set_reg32(&self, reg: NvmeRegs32, value: u32, delay_in_ms: u64) {
        loop {
            let current = self.read_reg32(reg);
            if (current & value) == 1 {
                break;
            }
            sys_ns_loopsleep(ONE_MS_IN_NS * delay_in_ms);
        }
    }

    fn wait_clear_reg32(&self, reg: NvmeRegs32, value: u32) {
        loop {
            let current = self.read_reg32(reg);
            if (current & value) == 0 {
                break;
            }
            sys_ns_loopsleep(ONE_MS_IN_NS * 100);
        }
    }

    fn write_flag32(&self, register: NvmeRegs32, flags: u32) {
        self.write_reg32(register, self.read_reg32(register) | flags);
    }

    fn clear_flag32(&self, reg: NvmeRegs32, flags: u32) {
        self.write_reg32(reg, self.read_reg32(reg) & !flags);
    }

    #[inline(always)]
    pub fn read_reg64(&self, reg: NvmeRegs64) -> u64 {
        unsafe { ptr::read_volatile((self.bar.get_base() + reg as u64) as *const u64) }
    }

    #[inline(always)]
    pub fn write_reg32(&self, reg: NvmeRegs32, val: u32) {
        unsafe { ptr::write_volatile((self.bar.get_base() + reg as u64) as *mut u32, val) }
    }

    #[inline(always)]
    pub fn write_reg64(&self, reg: NvmeRegs64, val: u64) {
        unsafe { ptr::write_volatile((self.bar.get_base() + reg as u64) as *mut u64, val) }
    }

    fn set_entry_sizes(&self) {
        self.write_reg32(
            NvmeRegs32::CC,
            self.read_reg32(NvmeRegs32::CC)
                | (4 << 20) // Sizeof(NvmeCompletion) in power of two
                | (6 << 16), // Sizeof(NvmeCommand) in power of two
        );
        println!("finish set_entry_sizes");
    }

    fn write_reg_idx(&self, reg: NvmeArrayRegs, qid: u16, val: u32) {
        match reg {
            NvmeArrayRegs::SQyTDBL => unsafe {
                ptr::write_volatile((self.bar.get_base() + 0x1000 + ((4 << self.dstrd) * (2 * qid)) as u64) as *mut u32, val);
            },

            NvmeArrayRegs::CQyHDBL => unsafe {
                ptr::write_volatile((self.bar.get_base() + 0x1000 + ((4 << self.dstrd) * (2 * qid + 1)) as u64) as *mut u32, val);
            },
        }
    }

    pub fn create_io_queues(&mut self) {
        for io_qid in 1..self.completion_queues.len() {
            let (ptr, len) = {
                let queue = &self.completion_queues[io_qid];
                (queue.data.physical(), queue.queue_len)
            };

            println!(
                "  - Attempting to create I/O completion queue {} with virt 0x{:08x} phys 0x{:08x} | len {}",
                io_qid,
                &*self.completion_queues[io_qid].data as *const _ as u64,
                ptr,
                len * core::mem::size_of::<NvmeCompletion>(),
            );
            {
                let qid = 0;
                let queue = &mut self.submission_queues[qid];
                let cid = queue.i as u16;
                let entry = nvme_cmd::create_io_completion_queue(cid, io_qid as u16, ptr, (len - 1) as u16);
                let tail = queue.submit(entry);
                self.submission_queue_tail(qid as u16, tail as u16);
            }

            {
                let qid = 0;
                let queue = &mut self.completion_queues[qid];
                let (head, _entry, _) = queue.complete_spin();
                self.completion_queue_head(qid as u16, head as u16);
            }
        }

        for io_qid in 1..self.submission_queues.len() {
            let (ptr, len) = {
                let queue = &self.submission_queues[io_qid];
                (queue.data.physical(), queue.data.len())
            };

            println!(
                "  - Attempting to create I/O submission queue {} with virt 0x{:08x} phys 0x{:08x} | len {} | entry_size {} | Q Depth {}",
                io_qid,
                &*self.submission_queues[io_qid].data as *const _ as u64,
                ptr,
                len,
                core::mem::size_of::<NvmeCommand>(),
                super::queue::QUEUE_DEPTH
            );
            {
                let qid = 0;
                let queue = &mut self.submission_queues[qid];
                let cid = queue.i as u16;
                //TODO: Get completion queue ID through smarter mechanism
                let entry = nvme_cmd::create_io_submission_queue(cid, io_qid as u16, ptr, (len - 1) as u16, io_qid as u16);
                let tail = queue.submit(entry);
                self.submission_queue_tail(qid as u16, tail as u16);
            }

            {
                let qid = 0;
                let queue = &mut self.completion_queues[qid];
                let (head, _entry, _) = queue.complete_spin();
                self.completion_queue_head(qid as u16, head as u16);
            }
        }
    }

    fn submission_queue_tail(&mut self, qid: u16, tail: u16) {
        self.write_reg_idx(NvmeArrayRegs::SQyTDBL, qid, tail as u32);
    }

    fn completion_queue_head(&mut self, qid: u16, head: u16) {
        self.write_reg_idx(NvmeArrayRegs::CQyHDBL, qid, head as u32);
    }

    fn reset_controller(&self) {
        println!("Resetting...");
        self.clear_flag32(NvmeRegs32::CC, NVME_CC_ENABLE);

        println!("Waiting for reset to be acked");
        self.wait_clear_reg32(NvmeRegs32::CSTS, NVME_CSTS_RDY);
    }

    /// Not in Atmosphere: disables the controller, which drops its queues, so no DMA follows the
    /// configuration that used it.
    pub fn shutdown(&self) {
        self.clear_flag32(NvmeRegs32::CC, NVME_CC_ENABLE);
        self.wait_clear_reg32(NvmeRegs32::CSTS, NVME_CSTS_RDY);
    }

    pub fn configure_admin_queue(&self) {
        let acq = &self.completion_queues[0];
        let asq = &self.submission_queues[0];

        self.write_reg32(NvmeRegs32::AQA, ((acq.queue_len as u32 - 1) << 16) | (asq.data.len() as u32 - 1));
        println!("asq.data.virt {:08x} phys {:08x} size {}", &*asq.data as *const _ as *const u64 as u64, asq.data.physical() as u64, asq.data.len());
        println!("acq.data.virt {:08x} phys {:08x} size {}", &*acq.data as *const _ as *const u64 as u64, acq.data.physical() as u64, acq.queue_len);

        self.write_reg64(NvmeRegs64::ASQ, asq.data.physical() as u64);
        self.write_reg64(NvmeRegs64::ACQ, acq.data.physical() as u64);
        println!("finish configure_admin_queue");
    }

    pub fn identify_controller(&mut self) {
        println!("allocating dma!");
        let data: Dma<[u8; 4096]> = allocate_dma().unwrap();

        println!("  - Attempting to identify controller with data {:x}", data.physical());
        {
            let qid = 0;
            let queue = &mut self.submission_queues[qid];
            let cid = queue.i as u16;
            let entry = nvme_cmd::identify_controller(cid, data.physical());
            let tail = queue.submit(entry);
            self.submission_queue_tail(qid as u16, tail as u16);
        }

        println!("  - Waiting to identify controller");
        {
            let qid = 0;
            let queue = &mut self.completion_queues[qid];
            let (head, _entry, _) = queue.complete_spin();
            self.completion_queue_head(qid as u16, head as u16);
        }

        println!("  - Dumping identify controller");
        println!("  - Model: {} Serial: {} Firmware: {}", id_str(&data[24..64]), id_str(&data[4..24]), id_str(&data[64..72]));
    }

    pub fn identify_ns_list(&mut self) {
        let mut nsids = Vec::new();
        {
            let data: Dma<[u32; 1024]> = allocate_dma().unwrap();

            println!("  - Attempting to retrieve namespace ID list");
            {
                let qid = 0;
                let queue = &mut self.submission_queues[qid];
                let cid = queue.i as u16;
                let entry = nvme_cmd::identify_namespace_list(cid, data.physical(), 1);
                let tail = queue.submit(entry);
                self.submission_queue_tail(qid as u16, tail as u16);
            }

            println!("  - Waiting to retrieve namespace ID list");
            {
                let qid = 0;
                let queue = &mut self.completion_queues[qid];
                let (head, _entry, _) = queue.complete_spin();
                self.completion_queue_head(qid as u16, head as u16);
            }

            println!("  - Dumping namespace ID list");
            for &nsid in data.iter() {
                if nsid != 0 {
                    nsids.push(nsid);
                }
            }
        }
        println!("nsids len {}", nsids.len());
        for nsid in nsids {
            println!("nsid: {:x}", nsid);
        }
    }

    pub fn identify_ns(&mut self, nsid: u32) {
        let data: Dma<[u8; 4096]> = allocate_dma().unwrap();

        println!("  - Attempting to identify namespace {}", nsid);
        {
            let qid = 0;
            let queue = &mut self.submission_queues[qid];
            let cid = queue.i as u16;
            let entry = nvme_cmd::identify_namespace(cid, data.physical(), nsid);
            let tail = queue.submit(entry);
            self.submission_queue_tail(qid as u16, tail as u16);
        }

        {
            let qid = 0;
            let queue = &mut self.completion_queues[qid];
            let (head, _entry, _) = queue.complete_spin();
            self.completion_queue_head(qid as u16, head as u16);
        }

        unsafe {
            let size = *(data.as_ptr().offset(0) as *const u64);
            let capacity = *(data.as_ptr().offset(8) as *const u64);
            println!("    - ID: {} Size: {} Capacity: {}", nsid, size * 512, capacity * 512);

            if capacity > 0 {
                NUM_LBAS.store(capacity, Ordering::Relaxed);
            }
            // Not in Atmosphere: the LBA data size of the format in use. FLBAS bits 3:0 pick the LBA format
            // descriptor at byte 128 + 4 * index, whose LBADS (bits 23:16) is log2 of the size.
            let lbads = data[128 + 4 * (data[26] & 0xf) as usize + 2] as u64;
            LBA_SHIFT.store(lbads.max(9), Ordering::Relaxed);

            //TODO: Read block size
            self.namespaces.push(NvmeNamespace { id: nsid, blocks: size, block_size: 512 });
        }
    }

    pub fn submit_and_poll_raw(&mut self, submit: &mut VecDeque<Vec<u8>>, collect: &mut VecDeque<Vec<u8>>, write: bool, _is_random: bool) -> usize {
        let mut sub_count = 0;
        let mut reap_count = 0;
        let mut cur_tail = 0;
        let mut cur_head = 0;
        let batch_sz = 32;
        let qid = 1;

        while let Some(breq) = submit.pop_front() {
            let (ptr0, ptr1) = (breq.as_ptr() as u64, 0);
            let queue = &mut self.submission_queues[qid];

            let num_blocks = 8;
            let entry = if write {
                nvme_cmd::io_write(qid as u16, 1, 0, (num_blocks - 1) as u16, ptr0, ptr1)
            } else {
                nvme_cmd::io_read(qid as u16, 1, 0, (num_blocks - 1) as u16, ptr0, ptr1)
            };

            if queue.is_submittable() {
                if let Some(tail) = queue.submit_request_raw_vec(entry, breq) {
                    cur_tail = tail;
                    sub_count += 1;

                    let queue = &mut self.completion_queues[qid];
                    if let Some((head, entry, cq_idx)) = queue.complete() {
                        assert_eq!({ entry.status } >> 1, 0);
                        let sq = &mut self.submission_queues[qid];
                        if sq.req_slot[cq_idx] {
                            if let Some(req) = sq.raw_requests_vec[cq_idx].take() {
                                collect.push_front(req);
                            }
                            sq.req_slot[cq_idx] = false;
                            reap_count += 1;
                        } else {
                            println!("submit_and_poll_raw: Weird! slot finished, but not found!");
                        }
                        cur_head = head;
                        self.stats.completed += 1;
                    }

                    self.stats.submitted += 1;
                }
            } else {
                submit.push_front(breq);
                break;
            }
        }

        if sub_count > 0 {
            self.submission_queue_tail(qid as u16, cur_tail as u16);
            unsafe { core::arch::x86_64::_mm_sfence() };
            core::hint::black_box(cur_tail);
        }

        {
            for _ in 0..batch_sz {
                let queue = &mut self.completion_queues[qid];
                if let Some((head, entry, cq_idx)) = queue.complete() {
                    if entry.status >> 1 > 0 {
                        log::info!("head {} entry {:?} cq_idx {}", head, entry, cq_idx);
                        assert_eq!({ entry.status } >> 1, 0);
                    }
                    let sq = &mut self.submission_queues[qid];
                    if sq.req_slot[cq_idx] {
                        if let Some(req) = sq.raw_requests_vec[cq_idx].take() {
                            collect.push_front(req);
                        }
                        sq.req_slot[cq_idx] = false;
                        reap_count += 1;
                    }
                    cur_head = head;
                    self.stats.completed += 1;
                } else {
                    break;
                }
            }
            if reap_count > 0 {
                self.completion_queue_head(qid as u16, cur_head as u16);
                unsafe { core::arch::x86_64::_mm_sfence() };
            }
        }

        sub_count
    }

    pub fn submit_and_poll_breq_with_ringbuffer(
        &mut self, submit: &mut RingBuffer<GenericRingBufferNode<BlockReq>, SIZE_OF_QUEUE>,
        collect: &mut RingBuffer<GenericRingBufferNode<BlockReq>, SIZE_OF_QUEUE>,
    ) -> usize {
        let mut sub_count = 0;
        let mut reap_count = 0;
        let mut cur_tail = 0;
        let mut cur_head = 0;
        let batch_sz = 32;
        let qid = 1;

        while let Some(breq) = submit.try_read() {
            let buf_addr = breq.data;
            let (ptr0, ptr1) = (buf_addr as u64, 0);
            let queue = &mut self.submission_queues[qid];

            let num_blocks = breq.num_blocks;
            let entry = if breq.op == BlockOp::Write {
                nvme_cmd::io_write(qid as u16, 1, breq.block, num_blocks - 1, ptr0, ptr1)
            } else {
                nvme_cmd::io_read(qid as u16, 1, breq.block, num_blocks - 1, ptr0, ptr1)
            };

            if queue.is_submittable() {
                if let Some(tail) = queue.submit_request_breq(entry, breq) {
                    cur_tail = tail;
                    sub_count += 1;
                    self.stats.submitted += 1;
                    submit.try_free();
                }
            } else {
                break;
            }

            if sub_count >= batch_sz {
                break;
            }
        }

        if sub_count > 0 {
            self.submission_queue_tail(qid as u16, cur_tail as u16);
        }

        {
            loop {
                let queue = &mut self.completion_queues[qid];

                if collect.is_full() || reap_count >= batch_sz {
                    break;
                }

                if let Some((head, entry, cq_idx)) = queue.complete() {
                    assert_eq!({ entry.status } >> 1, 0);
                    let sq = &mut self.submission_queues[qid];
                    if sq.req_slot[cq_idx] {
                        if let Some(req) = sq.breq_requests[cq_idx].take() {
                            while !collect.try_push(&req) {}
                        }
                        sq.req_slot[cq_idx] = false;
                        reap_count += 1;
                    } else {
                        println!("Anomaly: req_slot[{}] blkreq_rrefs[{}] can't collect", cq_idx, cq_idx);
                    }
                    cur_head = head;
                    self.stats.completed += 1;
                } else {
                    break;
                }
            }
            if reap_count > 0 {
                self.completion_queue_head(qid as u16, cur_head as u16);
            }
        }
        sub_count
    }
}
