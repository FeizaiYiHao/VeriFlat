//! Not in Atmosphere: the multi-queue NVMe benchmark `parallel_nvme`, one worker per CPU, each with its own I/O
//! queue pair, as the parallel call timing has one call pair per CPU (`VERIFLAT_PARALLEL=nvme` of a no-timer dom0).
//!
//! dom0's first thread resets the controller, sends Set Features Number of Queues before any I/O queue exists, and
//! creates I/O queue pair k + 1 for worker k: its own submission and completion rings, `MAX_BATCH` 4 KiB data
//! buffers and doorbells, all from dom0's heap (IOVA = VA) before any worker runs. Worker 0 is dom0's first thread
//! on CPU 0, worker k >= 1 the client of parallel call pair k on CPU k, threads of dom0 that share its page table
//! (BAR0 window, heap) and IOMMU table. A worker touches only its own pair, so the fast path takes no lock; the
//! admin queue belongs to dom0's first thread alone, which issues every admin command (`NvmeDevice::admin`) before
//! it releases a worker and after the last worker is done. Polling only: the completion queues have interrupts off.
//!
//! Worker count = min(CPUs, i.e. parallel call pairs, at most `MAX_PAIRS` = 28 in a build whose only parallel timing
//! is `nvme`, else 24 because pair k uses dom0 endpoint descriptor 8 + k; the I/O queue pairs the controller
//! allocates; `MAX_QUEUES`).
//!
//! `VERIFLAT_NVME_WORKERS=1,2,4,8,16,28` of the dom0 build replaces the alone-then-all phases by a sweep over worker
//! counts: per (op, batch), for each listed count m (at most `MAX_SWEEP` counts; counts above the worker count are
//! skipped with a line), workers 0..m run at once for `WINDOW_MS` and one `parallel_nvme sweep` line gives their
//! total IOPS, so one boot measures every count. Worker k reads and writes 4 KiB
//! requests sequentially within its own 1/n of namespace 1's LBAs. Batch b means at most b requests in flight on
//! the worker's queue: each round reaps every posted completion, refills up to b, and writes each doorbell at
//! most once. Per (op, batch), each worker runs alone for `WINDOW_MS` while the others spin, then all at once
//! until one shared deadline. The function is the one `pci::selected_nvme` picks (`VERIFLAT_NVME_BDF`, required on
//! bare metal, else under a hypervisor `VERIFLAT_NVME_INDEX`); other NVMe functions stay untouched.

use super::cmd as nvme_cmd;
use super::device::{blocks_per_4k, lba_shift, num_lbas, NvmeDevice};
use super::dma::{allocate_dma, Dma, NvmeCommand, NvmeCompletion};
use super::pci::{find_nvme_index, selected_nvme};
use super::queue::QUEUE_DEPTH;
use super::time::{rdtsc, tsc_hz, tsc_rate};
use crate::{check, current_cpu, hundredths, Hundredths, MAX_PAIRS, PAIRS, PHASE_NVME_FIRST};
use alloc::vec::Vec;
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use vsys::*;

/// The most I/O queue pairs, and so workers, this build creates.
pub(super) const MAX_QUEUES: usize = MAX_PAIRS;
/// The largest batch, and so the data buffers per queue pair.
pub(super) const MAX_BATCH: usize = 32;
/// The runs: (write, batch).
pub(super) const RUNS: [(bool, usize); 4] = [(false, 1), (false, 32), (true, 1), (true, 32)];
/// The most worker counts of a sweep (`VERIFLAT_NVME_WORKERS`).
pub(super) const MAX_SWEEP: usize = 8;
/// The phases worker k >= 1 is released into: run c alone is `PHASE_NVME_FIRST + 2 * c`, all at once the next; sweep
/// point i of run c is `PHASE_NVME_FIRST + 2 * RUNS.len() + c * MAX_SWEEP + i`, so consecutive points differ.
pub const PHASES: usize = 2 * RUNS.len() + RUNS.len() * MAX_SWEEP;
/// The worker counts of the sweep from `VERIFLAT_NVME_WORKERS` (comma-separated decimals), and how many there are;
/// none without it.
pub(super) const SWEEP: ([usize; MAX_SWEEP], usize) = match option_env!("VERIFLAT_NVME_WORKERS") {
    Some(s) => parse_list(s),
    None => ([0; MAX_SWEEP], 0),
};

const fn parse_list(s: &str) -> ([usize; MAX_SWEEP], usize) {
    let b = s.as_bytes();
    let (mut out, mut len, mut i, mut v, mut digits) = ([0; MAX_SWEEP], 0, 0, 0, 0);
    while i <= b.len() {
        if i == b.len() || b[i] == b',' {
            assert!(digits > 0 && v > 0 && len < MAX_SWEEP, "VERIFLAT_NVME_WORKERS must be at most 8 positive decimals separated by commas");
            out[len] = v;
            len += 1;
            (v, digits) = (0, 0);
        } else {
            assert!(b[i].is_ascii_digit(), "VERIFLAT_NVME_WORKERS must be at most 8 positive decimals separated by commas");
            v = v * 10 + (b[i] - b'0') as usize;
            digits += 1;
        }
        i += 1;
    }
    (out, len)
}

/// The run (index into `RUNS`) of a phase of this benchmark.
fn run_of(phase: usize) -> usize {
    let off = phase - PHASE_NVME_FIRST;
    if off < 2 * RUNS.len() { off / 2 } else { (off - 2 * RUNS.len()) / MAX_SWEEP }
}
/// The timed window of each phase in ms, from `VERIFLAT_NVME_PARALLEL_MS` of the dom0 build (default 1000).
pub(super) const WINDOW_MS: u64 = match option_env!("VERIFLAT_NVME_PARALLEL_MS") {
    Some(s) => parse_decimal(s),
    None => 1000,
};

const fn parse_decimal(s: &str) -> u64 {
    let b = s.as_bytes();
    let mut i = 0;
    let mut v = 0;
    while i < b.len() {
        assert!(b[i].is_ascii_digit(), "VERIFLAT_NVME_PARALLEL_MS must be a decimal number");
        v = v * 10 + (b[i] - b'0') as u64;
        i += 1;
    }
    v
}

/// I/O queue pair `qid` and the state of the one worker that uses it.
struct QueuePair {
    sq: Dma<[NvmeCommand; QUEUE_DEPTH]>,
    cq: Dma<[NvmeCompletion; QUEUE_DEPTH]>,
    /// Entries of each ring (at most `QUEUE_DEPTH`), the submission tail, the completion head and phase.
    len: usize,
    tail: usize,
    head: usize,
    phase: bool,
    sq_doorbell: *mut u32,
    cq_doorbell: *mut u32,
    /// Data buffer i serves the request with command ID i.
    bufs: Vec<Dma<[u8; 4096]>>,
    /// The worker's LBA range and the next LBA it requests.
    first_lba: u64,
    lbas: u64,
    next_lba: u64,
}

/// Queue pair of worker k; only dom0's first thread writes a slot, while no worker runs.
static mut QUEUES: [Option<QueuePair>; MAX_QUEUES] = [const { None }; MAX_QUEUES];

/// What worker k measured in its last finished phase, alone on its cache lines: completions, the TSC at its start
/// and end, and the IPC calls it made (`parallel_xproc`; 0 here).
#[repr(C, align(64))]
pub(super) struct Measured {
    pub(super) completed: AtomicU64,
    pub(super) begin: AtomicU64,
    pub(super) end: AtomicU64,
    pub(super) calls: AtomicU64,
}

impl Measured {
    pub(super) const fn new() -> Self {
        Measured { completed: AtomicU64::new(0), begin: AtomicU64::new(0), end: AtomicU64::new(0), calls: AtomicU64::new(0) }
    }

    pub(super) fn record(&self, completed: u64, begin: u64, end: u64, calls: u64) {
        self.completed.store(completed, Ordering::SeqCst);
        self.begin.store(begin, Ordering::SeqCst);
        self.end.store(end, Ordering::SeqCst);
        self.calls.store(calls, Ordering::SeqCst);
    }
}

static MEASURED: [Measured; MAX_QUEUES] = [const { Measured::new() }; MAX_QUEUES];
static HEAP_READY: AtomicBool = AtomicBool::new(false);
static WORKERS: AtomicUsize = AtomicUsize::new(0);

fn fail(what: core::fmt::Arguments) -> ! {
    log::error!("parallel_nvme: {}", what);
    unsafe { sys_debug_exit(1) };
}

/// Runs the benchmark over the first `n` parallel call pairs on the NVMe function `pci::selected_nvme` picks, or logs
/// that it skips it.
pub fn run(n: usize) {
    let Some(f) = selected_nvme("parallel_nvme") else {
        return;
    };
    let Some((hz, source)) = tsc_rate() else {
        fail(format_args!("no CPUID source gives the TSC rate; build dom0 with VERIFLAT_TSC_MHZ set to it"));
    };
    let others = find_nvme_index(1).is_some();
    log::info!(
        "parallel_nvme: NVMe function {:02x}:{:02x}.{} (vendor {:04x} device {:04x}, BAR0 {:#x}){}, TSC {} MHz from {}",
        f.bus, f.dev, f.fun, f.vendor, f.device, f.bar_phys,
        if others { "; other NVMe functions stay untouched" } else { "" }, hz / 1_000_000, source
    );
    if !HEAP_READY.swap(true, Ordering::SeqCst) {
        crate::slab_alloc::init();
    }
    check("parallel_nvme pci_attach_dma", unsafe { sys_pci_attach_dma(f.bus, f.dev, f.fun) });
    let mut dev = NvmeDevice::new(f.bar());
    dev.init_admin_only();
    let Some(blocks) = blocks_per_4k() else {
        dev.shutdown();
        log::info!("parallel_nvme skipped: namespace 1's LBA size {} bytes does not divide the 4 KiB request", 1u64 << lba_shift());
        return;
    };
    let blocks = blocks as u64;

    // Set Features Number of Queues, then one I/O queue pair per worker.
    let want = n.min(MAX_QUEUES);
    let (nsqa, ncqa) = dev.set_number_of_queues(want as u16).unwrap_or_else(|s| fail(format_args!("Set Features Number of Queues: status {:#x}", s)));
    let workers = want.min(nsqa as usize).min(ncqa as usize);
    let len = QUEUE_DEPTH.min(dev.max_queue_entries());
    let per = num_lbas() / workers as u64 / blocks * blocks;
    if per < blocks {
        fail(format_args!("{} LBAs do not give each of {} workers a 4 KiB request", num_lbas(), workers));
    }
    for k in 0..workers {
        let qid = k as u16 + 1;
        let pair = QueuePair {
            sq: allocate_dma().unwrap(), cq: allocate_dma().unwrap(), len, tail: 0, head: 0, phase: true,
            sq_doorbell: dev.doorbell(qid, false), cq_doorbell: dev.doorbell(qid, true),
            bufs: (0..MAX_BATCH).map(|_| allocate_dma().unwrap()).collect(), first_lba: k as u64 * per, lbas: per,
            next_lba: k as u64 * per,
        };
        if let Err(s) = dev.create_io_queue_pair(qid, pair.cq.physical(), pair.sq.physical(), len as u16) {
            fail(format_args!("creating I/O queue pair {}: status {:#x}", qid, s));
        }
        unsafe { (*(&raw mut QUEUES))[k] = Some(pair) };
    }
    WORKERS.store(workers, Ordering::SeqCst);
    log::info!(
        "parallel_nvme: {} workers (CPUs {}, controller allocated {} SQ / {} CQ, cap {}), {} entries per queue, {} LBAs of {} bytes per worker, {} ms per phase",
        workers, n, nsqa, ncqa, MAX_QUEUES, len, per, 1u64 << lba_shift(), WINDOW_MS
    );

    for (c, &(is_write, batch)) in RUNS.iter().enumerate() {
        if !super::pci::op_selected(is_write) {
            continue;
        }
        if SWEEP.1 == 0 {
            time_run("parallel_nvme", PHASE_NVME_FIRST, &MEASURED, |phase| worker(0, phase), workers, c, is_write, batch);
            continue;
        }
        for (i, &m) in SWEEP.0[..SWEEP.1].iter().enumerate() {
            if m > workers {
                log::info!("parallel_nvme sweep op={} batch={} n={} skipped: only {} workers", if is_write { "write" } else { "read" }, batch, m, workers);
                continue;
            }
            time_sweep_point(PHASE_NVME_FIRST + 2 * RUNS.len() + c * MAX_SWEEP + i, m, is_write, batch);
        }
    }

    // Disabling the controller deletes every queue, so no DMA reaches the buffers freed after it.
    dev.shutdown();
    for k in 0..workers {
        unsafe { (*(&raw mut QUEUES))[k] = None };
    }
    WORKERS.store(0, Ordering::SeqCst);
    log::info!("parallel_nvme passed");
}

/// Spins until worker `k` finished `phase`, for at most the window and 20 s more.
fn wait_done(prefix: &str, k: usize, phase: usize) {
    let limit = rdtsc() + (WINDOW_MS / 1000 + 20) * tsc_hz();
    while PAIRS[k].done.load(Ordering::SeqCst) != phase {
        if rdtsc() > limit {
            log::error!("{}: worker {} did not finish phase {}", prefix, k, phase);
            unsafe { sys_debug_exit(1) };
        }
        core::hint::spin_loop();
    }
}

/// Runs worker k in `phase` until `deadline`: worker 0 here with `run0`, worker k >= 1 by releasing the client of
/// pair k.
fn run_worker(k: usize, phase: usize, deadline: u64, run0: &dyn Fn(usize)) {
    PAIRS[k].deadline.store(deadline, Ordering::SeqCst);
    if k == 0 {
        run0(phase);
    } else {
        PAIRS[k].go.store(phase, Ordering::SeqCst);
    }
}

fn iops(completed: u64, cycles: u64) -> u64 {
    (completed as u128 * tsc_hz() as u128 / cycles.max(1) as u128) as u64
}

/// Times run `c` (phases `first_phase + 2 * c` alone and the next at once) with each worker alone, then all at once,
/// and logs with `prefix` a line per worker and a summary from what the workers recorded in `measured`; worker 0 runs
/// here with `run0`. The summary of a benchmark whose workers make IPC calls (`parallel_xproc`) also gives the calls
/// of the concurrent phase and its completions per call.
pub(super) fn time_run(
    prefix: &str, first_phase: usize, measured: &[Measured], run0: impl Fn(usize), workers: usize, c: usize, is_write: bool, batch: usize,
) {
    let (alone_phase, conc_phase) = (first_phase + 2 * c, first_phase + 2 * c + 1);
    let window = WINDOW_MS * tsc_hz() / 1000;
    let mut alone = [0u64; MAX_QUEUES];
    for k in 0..workers {
        run_worker(k, alone_phase, rdtsc() + window, &run0);
        wait_done(prefix, k, alone_phase);
        let m = &measured[k];
        alone[k] = iops(m.completed.load(Ordering::SeqCst), m.end.load(Ordering::SeqCst) - m.begin.load(Ordering::SeqCst));
    }
    // One deadline for all workers, published with each release; worker 0 runs last, here.
    let deadline = rdtsc() + window;
    for k in (0..workers).rev() {
        run_worker(k, conc_phase, deadline, &run0);
    }
    for k in 0..workers {
        wait_done(prefix, k, conc_phase);
    }

    let op = if is_write { "write" } else { "read" };
    let (mut min_begin, mut max_begin, mut min_end, mut max_end, mut total, mut calls) = (u64::MAX, 0, u64::MAX, 0, 0, 0);
    let mut ratios = [0u64; MAX_QUEUES];
    let mut sum_alone = 0;
    for k in 0..workers {
        let m = &measured[k];
        let (completed, begin, end) = (m.completed.load(Ordering::SeqCst), m.begin.load(Ordering::SeqCst), m.end.load(Ordering::SeqCst));
        (min_begin, max_begin, min_end, max_end) = (min_begin.min(begin), max_begin.max(begin), min_end.min(end), max_end.max(end));
        total += completed;
        calls += m.calls.load(Ordering::SeqCst);
        sum_alone += alone[k];
        let conc = iops(completed, end - begin);
        ratios[k] = hundredths(conc, alone[k].max(1));
        log::info!("{} cpu={} op={} batch={} alone={} conc={} ratio={}", prefix, k, op, batch, alone[k], conc, Hundredths(ratios[k]));
    }
    // Total IOPS of the concurrent phase: every completion over the span from the first begin to the last end.
    let total_iops = iops(total, max_end - min_begin);
    let overlap = if max_begin < min_end { hundredths(min_end - max_begin, max_end - min_begin) } else { 0 };
    let ratios = &mut ratios[..workers];
    ratios.sort_unstable();
    let alone = &mut alone[..workers];
    alone.sort_unstable();
    let median_alone = (alone[(workers - 1) / 2] + alone[workers / 2]) / 2;
    log::info!(
        "{} summary op={} batch={} n={} total_conc={} sum_alone={} median_alone={} scaling={} min_ratio={} median_ratio={} overlap={}",
        prefix, op, batch, workers, total_iops, sum_alone, median_alone, Hundredths(hundredths(total_iops, median_alone.max(1))), Hundredths(ratios[0]),
        Hundredths((ratios[(workers - 1) / 2] + ratios[workers / 2]) / 2), Hundredths(overlap)
    );
    if calls > 0 {
        log::info!("{} calls op={} batch={} n={} calls={} per_call={}", prefix, op, batch, workers, calls, Hundredths(hundredths(total, calls)));
    }
}

/// Runs workers 0..m at once in `phase` until one shared deadline `WINDOW_MS` away and logs their total IOPS over the
/// span from the first begin to the last end, the slowest and fastest worker's IOPS and the share of the span in
/// which all of them ran.
fn time_sweep_point(phase: usize, m: usize, is_write: bool, batch: usize) {
    time_sweep("parallel_nvme", phase, m, is_write, batch, &MEASURED, &|phase| worker(0, phase));
}

/// One sweep point of a benchmark with prefix `prefix`: workers 0..m run `phase` at once until one deadline (worker
/// 0 here with `run0`), then one line gives the total IOPS over the span from the first begin to the last end, the
/// slowest and fastest worker's own IOPS, the IPC round trips (`calls`, 0 without IPC), and `cycles_per_req`, the
/// worker CPU time per completed request (span x m / completions), from what the workers recorded in `measured`.
pub(super) fn time_sweep(prefix: &str, phase: usize, m: usize, is_write: bool, batch: usize, measured: &[Measured], run0: &dyn Fn(usize)) {
    let deadline = rdtsc() + WINDOW_MS * tsc_hz() / 1000;
    for k in (0..m).rev() {
        run_worker(k, phase, deadline, run0);
    }
    for k in 0..m {
        wait_done(prefix, k, phase);
    }
    let (mut min_begin, mut max_begin, mut min_end, mut max_end, mut total, mut calls) = (u64::MAX, 0, u64::MAX, 0, 0, 0);
    let (mut slowest, mut fastest) = (u64::MAX, 0);
    for k in 0..m {
        let r = &measured[k];
        let (completed, begin, end) = (r.completed.load(Ordering::SeqCst), r.begin.load(Ordering::SeqCst), r.end.load(Ordering::SeqCst));
        (min_begin, max_begin, min_end, max_end) = (min_begin.min(begin), max_begin.max(begin), min_end.min(end), max_end.max(end));
        total += completed;
        calls += r.calls.load(Ordering::SeqCst);
        let own = iops(completed, end - begin);
        (slowest, fastest) = (slowest.min(own), fastest.max(own));
    }
    let overlap = if max_begin < min_end { hundredths(min_end - max_begin, max_end - min_begin) } else { 0 };
    let span = max_end - min_begin;
    log::info!(
        "{} sweep op={} batch={} n={} total_iops={} per_worker_min={} per_worker_max={} completed={} calls={} cycles_per_req={} overlap={}",
        prefix, if is_write { "write" } else { "read" }, batch, m, iops(total, span), slowest, fastest, total, calls,
        span as u128 * m as u128 / total.max(1) as u128, Hundredths(overlap)
    );
}

/// Takes every posted completion of worker `k`'s queue pair `q`, returns its command ID (= data buffer) to
/// `free`, writes the completion head doorbell once if it took any, and returns how many it took.
#[inline(always)]
fn reap(k: usize, q: &mut QueuePair, free: &mut [u16; MAX_BATCH], nfree: &mut usize, in_flight: &mut usize) -> u64 {
    let mut reaped = 0;
    loop {
        let entry = unsafe { core::ptr::read_volatile(q.cq.as_ptr().add(q.head)) };
        if ((entry.status & 1) == 1) != q.phase {
            break;
        }
        if entry.status >> 1 != 0 {
            fail(format_args!("worker {}: command {} failed with status {:#x}", k, { entry.cid }, { entry.status } >> 1));
        }
        free[*nfree] = entry.cid;
        *nfree += 1;
        *in_flight -= 1;
        reaped += 1;
        q.head += 1;
        if q.head == q.len {
            q.head = 0;
            q.phase = !q.phase;
        }
    }
    if reaped > 0 {
        unsafe { core::ptr::write_volatile(q.cq_doorbell, q.head as u32) };
    }
    reaped
}

/// Worker `k` in `phase`, on CPU k: sequential 4 KiB requests on its own queue pair with at most `batch` in
/// flight until the deadline of pair k, counting the completions reaped by then; then reaps the rest, so the
/// next phase starts with an empty queue, records the result, and marks the phase done.
pub fn worker(k: usize, phase: usize) {
    let pair = &PAIRS[k];
    let (is_write, batch) = RUNS[run_of(phase)];
    let deadline = pair.deadline.load(Ordering::SeqCst);
    let Some(q) = (unsafe { (*(&raw mut QUEUES))[k].as_mut() }) else {
        fail(format_args!("worker {} has no queue pair", k));
    };
    if current_cpu() != k {
        fail(format_args!("worker {} runs on CPU {}", k, current_cpu()));
    }
    let qid = k as u16 + 1;
    let blocks = 4096u64 >> lba_shift();
    let mut free = [0u16; MAX_BATCH];
    for (i, slot) in free.iter_mut().enumerate() {
        *slot = i as u16;
    }
    let (mut nfree, mut in_flight, mut completed) = (MAX_BATCH, 0, 0u64);

    let begin = rdtsc();
    let end = loop {
        completed += reap(k, q, &mut free, &mut nfree, &mut in_flight);
        let mut submitted = false;
        while in_flight < batch {
            nfree -= 1;
            let slot = free[nfree];
            let buf = q.bufs[slot as usize].physical() as u64;
            let mut cmd = if is_write {
                nvme_cmd::io_write(slot, 1, q.next_lba, blocks as u16 - 1, buf, 0)
            } else {
                nvme_cmd::io_read(slot, 1, q.next_lba, blocks as u16 - 1, buf, 0)
            };
            cmd.cid = slot;
            unsafe { core::ptr::write_volatile(q.sq.as_mut_ptr().add(q.tail), cmd) };
            q.tail = (q.tail + 1) % q.len;
            q.next_lba += blocks;
            if q.next_lba >= q.first_lba + q.lbas {
                q.next_lba = q.first_lba;
            }
            in_flight += 1;
            submitted = true;
        }
        if submitted {
            unsafe { core::ptr::write_volatile(q.sq_doorbell, q.tail as u32) };
        }
        let now = rdtsc();
        if now >= deadline {
            break now;
        }
    };
    let drain_limit = rdtsc() + 10 * tsc_hz();
    while in_flight > 0 {
        reap(k, q, &mut free, &mut nfree, &mut in_flight);
        if rdtsc() > drain_limit {
            fail(format_args!("worker {} (queue {}): {} requests still pending after the phase", k, qid, in_flight));
        }
    }
    MEASURED[k].record(completed, begin, end, 0);
    pair.done.store(phase, Ordering::SeqCst);
}
