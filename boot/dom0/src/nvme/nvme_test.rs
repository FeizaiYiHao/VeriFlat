//! Port of Atmosphere's `nvme_driver/src/nvme_test.rs` (`run_blocktest_raw_with_delay`, the statically
//! linked configuration). Changes: the run time is TSC cycles at `tsc_hz` instead of a fixed 2.4 GHz;
//! b2histogram is replaced by the minimum, median, and maximum of the cycles of the calls that submitted
//! or reaped a request (`Samples`); the
//! run ends by polling until every submitted request completed, so the next run starts with an empty
//! queue; the result is one `nvme ...` line (`report`).

use super::device::NvmeDevice;
use super::println;
use super::time::{rdtsc, sys_ns_loopsleep, tsc_hz};
use alloc::collections::VecDeque;
use alloc::vec::Vec;

/// Cycle samples kept for the median: the first `CAP`, then a ring over the latest.
pub struct Samples {
    v: Vec<u64>,
    n: u64,
}

impl Samples {
    const CAP: usize = 1 << 16;

    pub fn new() -> Samples {
        Samples { v: Vec::with_capacity(Self::CAP), n: 0 }
    }

    #[inline(always)]
    pub fn record(&mut self, cycles: u64) {
        if self.v.len() < Self::CAP {
            self.v.push(cycles);
        } else {
            self.v[(self.n % Self::CAP as u64) as usize] = cycles;
        }
        self.n += 1;
    }

    /// `(count, min, median, max)`.
    pub fn summary(&mut self) -> (u64, u64, u64, u64) {
        if self.v.is_empty() {
            return (0, 0, 0, 0);
        }
        self.v.sort_unstable();
        (self.n, self.v[0], self.v[self.v.len() / 2], self.v[self.v.len() - 1])
    }
}

/// Logs the result line of one run: `nvme <config> <read|write> batch=<b>: <iops> IOPS, <n> completed in
/// <ms> ms, <what> median <c> min <c> max <c> TSC cycles over <rounds> rounds`.
pub fn report(config: &str, is_write: bool, batch_sz: u64, completed: u64, elapsed: u64, what: &str, samples: &mut Samples) {
    let hz = tsc_hz();
    let iops = (completed as u128 * hz as u128 / elapsed.max(1) as u128) as u64;
    let ms = (elapsed as u128 * 1000 / hz as u128) as u64;
    let (rounds, min, median, max) = samples.summary();
    log::info!(
        "nvme {} {} batch={}: {} IOPS, {} completed in {} ms, {} median {} min {} max {} TSC cycles over {} rounds",
        config, if is_write { "write" } else { "read" }, batch_sz, iops, completed, ms, what, median, min, max, rounds
    );
}

pub fn run_blocktest_raw_with_delay(dev: &mut NvmeDevice, runtime: u64, batch_sz: u64, is_write: bool, is_random: bool, delay: u64) {
    let req: Vec<u8> = if is_write { alloc::vec![0xabu8; 4096] } else { alloc::vec![0u8; 4096] };

    dev.stats.reset_stats();
    let mut submit: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz as usize);
    let mut collect: VecDeque<Vec<u8>> = VecDeque::new();

    for _i in 0..batch_sz {
        submit.push_back(req.clone());
    }

    let mut count = 0;
    let mut alloc_count = 0;
    let mut samples = Samples::new();

    println!("======== Starting {}{} test (delay {})  ==========", if is_random { "rand" } else { "" }, if is_write { "write" } else { "read" }, delay);

    let tsc_start = rdtsc();
    let tsc_end = tsc_start + runtime * tsc_hz();

    loop {
        count += 1;
        let before = dev.stats.get_stats();
        let submit_start = rdtsc();
        dev.submit_and_poll_raw(&mut submit, &mut collect, is_write, is_random);
        let cycles = rdtsc() - submit_start;
        // Not in Atmosphere: only calls that submitted or reaped a request count, since a full queue
        // makes most calls return at once.
        if dev.stats.get_stats() != before {
            samples.record(cycles);
        }

        submit.append(&mut collect);

        if submit.is_empty() {
            alloc_count += 1;
            for _i in 0..batch_sz {
                submit.push_back(req.clone());
            }
        }

        if rdtsc() > tsc_end {
            break;
        }
        if delay > 0 {
            sys_ns_loopsleep(delay);
        }
    }

    let elapsed = rdtsc() - tsc_start;
    let (sub, comp) = dev.stats.get_stats();

    // Not in Atmosphere, which polls once with `poll_raw`: reap until every request completed, so the
    // next run starts with an empty queue.
    let drain_start = rdtsc();
    let mut nothing = VecDeque::new();
    while dev.stats.get_stats().1 < sub {
        dev.submit_and_poll_raw(&mut nothing, &mut collect, is_write, is_random);
        if rdtsc() - drain_start > 10 * tsc_hz() {
            log::error!("nvme: {} of {} requests still pending after the run", sub - dev.stats.get_stats().1, sub);
            unsafe { vsys::sys_debug_exit(1) };
        }
    }
    println!("nvme linked: {} rounds, {} submitted, {} buffer batches allocated", count, sub, alloc_count);
    report("linked", is_write, batch_sz, comp, elapsed, "submit_and_poll", &mut samples);
}
