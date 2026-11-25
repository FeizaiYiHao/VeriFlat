//! Linux user-space front end of the `ice` driver core, for bringing the E810 up on the real machine before running
//! the same core in VeriFlat's dom0. Like ixy, it drives the PF without a kernel driver: BAR0 through sysfs
//! `resource0`, DMA memory from 2 MiB hugepages whose physical addresses come from `/proc/self/pagemap`. The device
//! therefore uses physical addresses, which needs the IOMMU off or in passthrough mode (`intel_iommu=off` or
//! `iommu=pt` on the kernel command line). Run as root with the PF unbound from `ice`; see `boot/bench/README.md`.

use ice::bench::{line_rate_pps, rate, run_forwarder, run_queue_pair, run_sender, TxFrame, WorkerResult};
use ice::maglev::{populate_lut, Maglev, CACHE_ENTRIES, ENTRY_BYTES, TABLE_SIZE};
use ice::packet::{steering_mac, UdpFrame};
use ice::{Config, Device, DmaRegion, Mac, Platform, RxSteering};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::unix::fs::FileExt;
use std::os::unix::io::AsRawFd;
use std::process::exit;
use std::sync::{Barrier, Mutex};
use std::time::{Duration, Instant};

const HUGE_PAGE: usize = 2 << 20;
const MAP_HUGE_2MB: i32 = 21 << libc::MAP_HUGE_SHIFT;

struct Logger;

impl log::Log for Logger {
    fn enabled(&self, m: &log::Metadata) -> bool {
        m.level() <= log::max_level()
    }
    fn log(&self, r: &log::Record) {
        if self.enabled(r.metadata()) {
            eprintln!("[{:5}] {}", r.level(), r.args());
        }
    }
    fn flush(&self) {}
}

/// Bump allocator over 2 MiB hugepages: a region never crosses a hugepage, so it is physically contiguous.
struct HugeAlloc {
    page_va: usize,
    page_pa: u64,
    used: usize,
    pagemap: File,
}

struct LinuxPlatform {
    bar: *mut u8,
    bar_len: usize,
    dma: Mutex<HugeAlloc>,
}

// BAR0 is device memory shared by the threads, each touching its own queue's registers.
unsafe impl Sync for LinuxPlatform {}

fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

impl HugeAlloc {
    fn virt_to_phys(&self, va: usize) -> Option<u64> {
        let mut entry = [0u8; 8];
        self.pagemap.read_exact_at(&mut entry, (va / 4096 * 8) as u64).ok()?;
        let e = u64::from_le_bytes(entry);
        let pfn = e & ((1 << 55) - 1);
        (e >> 63 == 1 && pfn != 0).then(|| pfn * 4096 + (va % 4096) as u64)
    }

    fn new_page(&mut self) -> Option<()> {
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_HUGETLB | MAP_HUGE_2MB | libc::MAP_POPULATE | libc::MAP_LOCKED;
        let va = unsafe { libc::mmap(std::ptr::null_mut(), HUGE_PAGE, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0) };
        if va == libc::MAP_FAILED {
            log::error!("mmap of a 2 MiB hugepage failed: {} (reserve some: echo 512 > /proc/sys/vm/nr_hugepages)", std::io::Error::last_os_error());
            return None;
        }
        // Touch it so that it is backed, then find its physical address.
        unsafe { std::ptr::write_volatile(va as *mut u8, 0) };
        let Some(pa) = self.virt_to_phys(va as usize) else {
            log::error!("no physical address in /proc/self/pagemap: run as root");
            return None;
        };
        self.page_va = va as usize;
        self.page_pa = pa;
        self.used = 0;
        Some(())
    }
}

impl Platform for LinuxPlatform {
    fn read32(&self, offset: usize) -> u32 {
        assert!(offset + 4 <= self.bar_len);
        unsafe { std::ptr::read_volatile(self.bar.add(offset) as *const u32) }
    }

    fn write32(&self, offset: usize, value: u32) {
        assert!(offset + 4 <= self.bar_len);
        unsafe { std::ptr::write_volatile(self.bar.add(offset) as *mut u32, value) }
    }

    fn dma_alloc(&self, len: usize, align: usize) -> Option<DmaRegion> {
        if len > HUGE_PAGE {
            return None;
        }
        let mut a = self.dma.lock().unwrap();
        let mut start = (a.used + align - 1) & !(align - 1);
        if a.page_va == 0 || start + len > HUGE_PAGE {
            a.new_page()?;
            start = 0;
        }
        a.used = start + len;
        Some(DmaRegion { va: (a.page_va + start) as *mut u8, iova: a.page_pa + start as u64, len })
    }

    fn delay_us(&self, us: u64) {
        if us >= 1000 {
            std::thread::sleep(Duration::from_micros(us));
        } else {
            let t = Instant::now();
            while t.elapsed() < Duration::from_micros(us) {
                std::hint::spin_loop();
            }
        }
    }

    fn tsc(&self) -> u64 {
        rdtsc()
    }
}

struct Args {
    bdf: String,
    queues: usize,
    cpus: Vec<usize>,
    senders: Vec<usize>,
    tx_ring: usize,
    tx_batch: usize,
    interval: bool,
    pool: usize,
    secs: u64,
    frame: usize,
    tx: bool,
    rx: bool,
    dst: Option<[u8; 6]>,
    peer: Option<[u8; 6]>,
    peer_queues: Option<usize>,
    steering: RxSteering,
    link_timeout: u64,
    fwd: bool,
    fwd_dst: Option<[u8; 6]>,
    fwd_workers: Option<usize>,
    gen_peer: Option<[u8; 6]>,
    gen_peer_queues: usize,
}

const USAGE: &str = "usage: ice-linux <pci address, e.g. 0000:17:00.0> [options]
  --queues N         queue pairs, one thread each (default: 1)
  --cpus LIST        CPUs of the threads, e.g. 0-7 or 2,4,6 (default: 0..N)
  --secs S           seconds of traffic (default: 5)
  --frame BYTES      frame size with CRC, 64..9000 (default: 64); above 1518 the port is set to jumbo frames (9728)
                     and every Rx buffer holds a whole frame
  --mode tx|rx|both  what each queue does (default: both)
  --dst MAC          destination of every frame (default: broadcast)
  --peer MAC         the peer runs this program too: queue q sends to the peer's queue q (its steering MAC)
  --peer-queues N    queues of the peer, if it has fewer than this side
  --steer mac|promisc  Rx rules: per-queue steering MACs (default) or every frame to the VSI
  --link-timeout S   seconds to wait for the link (default: 15)
 --pool N          copies of each queue's frame, sent in turn (default 64; 1 = one buffer)
  --interval 1      print the port counters' rates once a second
  --tx-ring N / --tx-batch N  Tx descriptors per ring (1024) and per write-back batch (32)
  --senders LIST     CPUs of extra Tx-only threads, each on a queue of its own, sending the N measured
                     queues' frames round robin: a reflector returns them spread over the N queues
  --mode fwd         forward (Atmosphere's maglev benchmark, ice::bench::run_forwarder): --fwd-workers W threads
                     (default N), thread k forwarding what queues k, k+W, .. receive on Tx queue k to --fwd-dst MAC
  --gen-peer MAC     generator (with --mode tx): copy i of queue q goes to the peer's steering MAC of queue
                     (q + i) % --gen-peer-queues (default 28), each copy a flow of its own (source IP and port)";

fn parse_cpus(s: &str) -> Option<Vec<usize>> {
    let mut v = Vec::new();
    for part in s.split(',') {
        match part.split_once('-') {
            Some((a, b)) => v.extend(a.parse::<usize>().ok()?..=b.parse::<usize>().ok()?),
            None => v.push(part.parse().ok()?),
        }
    }
    Some(v)
}

fn parse_args() -> Args {
    let mut it = std::env::args().skip(1);
    let fail = |msg: &str| -> ! {
        eprintln!("{}\n{}", msg, USAGE);
        exit(2)
    };
    let bdf = it.next().unwrap_or_else(|| fail("missing PCI address"));
    let mut a = Args {
        bdf,
        queues: 1,
        cpus: Vec::new(),
        secs: 5,
        frame: 64,
        tx: true,
        rx: true,
        dst: None,
        peer: None,
        peer_queues: None,
        steering: RxSteering::PerQueueMac,
        link_timeout: 15,
        senders: Vec::new(),
        tx_ring: 1024,
        tx_batch: 32,
        interval: false,
        pool: 64,
        fwd: false,
        fwd_dst: None,
        fwd_workers: None,
        gen_peer: None,
        gen_peer_queues: 28,
    };
    while let Some(opt) = it.next() {
        let val = it.next().unwrap_or_else(|| fail(&format!("{} needs a value", opt)));
        let num = || val.parse::<u64>().unwrap_or_else(|_| fail(&format!("bad number for {}", opt)));
        match opt.as_str() {
            "--queues" => a.queues = num() as usize,
            "--pool" => a.pool = (num() as usize).clamp(1, 1024),
            "--interval" => a.interval = val == "1",
            "--tx-ring" => a.tx_ring = num() as usize,
            "--tx-batch" => a.tx_batch = num() as usize,
            "--senders" => a.senders = parse_cpus(&val).unwrap_or_else(|| fail("bad CPU list")),
            "--cpus" => a.cpus = parse_cpus(&val).unwrap_or_else(|| fail("bad CPU list")),
            "--secs" => a.secs = num(),
            "--frame" => a.frame = num() as usize,
            "--mode" => (a.tx, a.rx) = match val.as_str() {
                "tx" => (true, false),
                "rx" => (false, true),
                "both" => (true, true),
                "fwd" => {
                    a.fwd = true;
                    (false, false)
                }
                _ => fail("--mode is tx, rx, both or fwd"),
            },
            "--fwd-dst" => a.fwd_dst = Some(ice::parse_mac(&val).unwrap_or_else(|| fail("bad MAC"))),
            "--fwd-workers" => a.fwd_workers = Some(num() as usize),
            "--gen-peer" => a.gen_peer = Some(ice::parse_mac(&val).unwrap_or_else(|| fail("bad MAC"))),
            "--gen-peer-queues" => a.gen_peer_queues = (num() as usize).max(1),
            "--dst" => a.dst = Some(ice::parse_mac(&val).unwrap_or_else(|| fail("bad MAC"))),
            "--peer" => a.peer = Some(ice::parse_mac(&val).unwrap_or_else(|| fail("bad MAC"))),
            "--peer-queues" => a.peer_queues = Some(num() as usize),
            "--steer" => a.steering = match val.as_str() {
                "mac" => RxSteering::PerQueueMac,
                "promisc" => RxSteering::Promiscuous,
                _ => fail("--steer is mac or promisc"),
            },
            "--link-timeout" => a.link_timeout = num(),
            _ => fail(&format!("unknown option {}", opt)),
        }
    }
    if a.cpus.is_empty() {
        a.cpus = (0..a.queues).collect();
    }
    if a.cpus.len() < a.queues {
        fail("fewer CPUs than queues");
    }
    if !(64..=9000).contains(&a.frame) {
        fail("--frame is 64..9000");
    }
    a
}

fn read_hex(path: &str) -> u16 {
    let s = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("{}: {}", path, e);
        exit(1)
    });
    u16::from_str_radix(s.trim().trim_start_matches("0x"), 16).unwrap_or(0)
}

/// Checks that the function is an unbound E810 PF, enables memory decoding and bus mastering, and maps BAR0.
fn open_device(bdf: &str) -> LinuxPlatform {
    let dir = format!("/sys/bus/pci/devices/{}", bdf);
    let (vendor, device) = (read_hex(&format!("{}/vendor", dir)), read_hex(&format!("{}/device", dir)));
    if !ice::is_e810(vendor, device) {
        eprintln!("{} is {:04x}:{:04x}, not an E810 PF", bdf, vendor, device);
        exit(1);
    }
    if let Ok(driver) = fs::read_link(format!("{}/driver", dir)) {
        eprintln!(
            "{} is bound to {}; unbind it first: echo {} | sudo tee {}/driver/unbind",
            bdf,
            driver.file_name().unwrap_or_default().to_string_lossy(),
            bdf,
            dir
        );
        exit(1);
    }
    let mut config = OpenOptions::new().read(true).write(true).open(format!("{}/config", dir)).unwrap_or_else(|e| {
        eprintln!("{}/config: {} (run as root)", dir, e);
        exit(1)
    });
    let mut cmd = [0u8; 2];
    config.seek(SeekFrom::Start(4)).and_then(|_| config.read_exact(&mut cmd)).expect("read PCI command");
    let cmd = u16::from_le_bytes(cmd) | 0x6;
    config.seek(SeekFrom::Start(4)).and_then(|_| config.write_all(&cmd.to_le_bytes())).expect("write PCI command");
    let res = OpenOptions::new().read(true).write(true).open(format!("{}/resource0", dir)).unwrap_or_else(|e| {
        eprintln!("{}/resource0: {}", dir, e);
        exit(1)
    });
    let bar_len = res.metadata().map(|m| m.len() as usize).unwrap_or(0);
    let bar = unsafe { libc::mmap(std::ptr::null_mut(), bar_len, libc::PROT_READ | libc::PROT_WRITE, libc::MAP_SHARED, res.as_raw_fd(), 0) };
    if bar == libc::MAP_FAILED {
        eprintln!("mmap of resource0 failed: {}", std::io::Error::last_os_error());
        exit(1);
    }
    log::info!("{} {:04x}:{:04x}, BAR0 {} MiB mapped", bdf, vendor, device, bar_len >> 20);
    let pagemap = File::open("/proc/self/pagemap").expect("/proc/self/pagemap");
    LinuxPlatform { bar: bar as *mut u8, bar_len, dma: Mutex::new(HugeAlloc { page_va: 0, page_pa: 0, used: 0, pagemap }) }
}

fn pin_to(cpu: usize) {
    unsafe {
        let mut set: libc::cpu_set_t = std::mem::zeroed();
        libc::CPU_SET(cpu, &mut set);
        if libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), &set) != 0 {
            log::warn!("cannot pin to CPU {}: {}", cpu, std::io::Error::last_os_error());
        }
    }
}

fn tsc_hz() -> u64 {
    let (t0, c0) = (Instant::now(), rdtsc());
    std::thread::sleep(Duration::from_millis(200));
    let (dt, dc) = (t0.elapsed(), rdtsc() - c0);
    (dc as u128 * 1_000_000_000 / dt.as_nanos()) as u64
}

fn main() {
    log::set_logger(&Logger).unwrap();
    log::set_max_level(log::LevelFilter::Info);
    let args = parse_args();
    let p = open_device(&args.bdf);
    let hz = tsc_hz();
    let jumbo = args.frame > 1518;
    let config = Config {
        queues: args.queues + args.senders.len(), steering: args.steering, tx_ring: args.tx_ring, tx_batch: args.tx_batch,
        rx_buf: if jumbo { args.frame.next_multiple_of(128) } else { 2048 }, max_frame: if jumbo { ice::packet::JUMBO_MAX_FRAME } else { 0 },
        ..Default::default()
    };
    let mut dev = Device::new(&p, config).unwrap_or_else(|e| {
        log::error!("bring-up failed: {}", e);
        exit(1)
    });
    let link = dev.bring_link_up(args.link_timeout * 1000).unwrap_or_else(|e| {
        log::error!("link: {}", e);
        exit(1)
    });
    if link.up {
        log::info!("link up at {} Mb/s, max frame {}", link.speed_mbps, link.max_frame);
    } else {
        log::warn!("link still down after {} s: frames will not reach the wire", args.link_timeout);
    }
    let mac = dev.info.mac;
    let n = args.queues;
    let frames: Vec<TxFrame> = (0..n + args.senders.len())
        .map(|i| {
            let q = i;
            let dst = match (args.dst, args.peer) {
                (Some(d), _) => d,
                (None, Some(peer)) => steering_mac(peer, q % args.peer_queues.unwrap_or(args.queues)),
                (None, None) => [0xff; 6],
            };
            let f = UdpFrame {
                dst_mac: dst,
                // With per-queue steering, queue q sends from its own steering MAC, so a peer that swaps the
                // MACs (a reflector) returns queue q's frames to queue q.
                src_mac: if args.steering == RxSteering::PerQueueMac { steering_mac(mac, q) } else { mac },
                src_ip: [10, 10, 0, 1 + q as u8],
                dst_ip: [10, 10, 1, 1 + q as u8],
                src_port: 1024 + q as u16,
                dst_port: 5000 + q as u16,
                len: args.frame - 4,
            };
            let mut pool = TxFrame::pool(&p, &f, args.pool).expect("DMA memory for the frames");
            if let Some(peer) = args.gen_peer {
                // Generator: copy i to the peer's queue (q + i) % gen_peer_queues, each a flow of its own.
                for c in 0..args.pool {
                    let dst = steering_mac(peer, (q + c) % args.gen_peer_queues);
                    let ip = [10, 1 + q as u8, (c >> 8) as u8, c as u8];
                    pool.write_copy(c, &UdpFrame { dst_mac: dst, src_mac: mac, src_ip: ip, src_port: 1024 + c as u16, ..f });
                }
            }
            pool
        })
        .collect();
    log::info!(
        "{} queue pairs on CPUs {:?}, {} s, {}-byte frames, tx {} rx {}, first destination {}",
        args.queues, &args.cpus[..args.queues], args.secs, args.frame, args.tx, args.rx, Mac(frames_dst(&frames[0]))
    );
    let mut queues = dev.take_queues();
    let before = dev.port_stats();
    if args.fwd {
        forward(&p, &dev, &mut queues, &args, mac, hz, link.speed_mbps as u64, &before);
        drop(queues);
        if let Err(e) = dev.shutdown() {
            log::warn!("PF reset at exit: {}", e);
        }
        return;
    }
    // Senders send the measured queues' frames (each from its queue's steering MAC) round robin.
    let sender_list: Vec<(u64, u16)> = (0..args.pool).flat_map(|i| frames[..n].iter().map(move |f| f.copy(i))).collect();
    let sender_frames = &sender_list[..];
    let all_cpus: Vec<usize> = args.cpus[..n].iter().chain(&args.senders).copied().collect();
    let barrier = Barrier::new(all_cpus.len());
    let cycles = args.secs * hz;
    let results: Vec<WorkerResult> = std::thread::scope(|s| {
        let handles: Vec<_> = queues
            .iter_mut()
            .zip(&frames)
            .zip(&all_cpus)
            .enumerate()
            .map(|(i, (((tx, rx), frame), &cpu))| {
                let (p, barrier, args) = (&p, &barrier, &args);
                s.spawn(move || {
                    pin_to(cpu);
                    barrier.wait();
                    if i < n {
                        run_queue_pair(p, tx, rx, args.tx.then_some(frame), args.rx, cycles)
                    } else {
                        run_sender(p, tx, sender_frames, cycles)
                    }
                })
            })
            .collect();
        // Port counters once a second while the workers run, so that a rate change within the window shows.
        if args.interval {
            let (mut last, mut t) = (dev.port_stats(), Instant::now());
            while !handles.iter().all(|h| h.is_finished()) {
                std::thread::sleep(Duration::from_millis(1000));
                let (now, dt) = (dev.port_stats(), t.elapsed().as_secs_f64());
                let d = now.since(&last);
                println!(
                    "interval: tx {:.2} Mpps, rx {:.2} Mpps, rx no-desc {:.2} Mpps, xoff rx {} pfc {}",
                    (d.tx_unicast + d.tx_multicast + d.tx_broadcast) as f64 / dt / 1e6,
                    (d.rx_unicast + d.rx_multicast + d.rx_broadcast) as f64 / dt / 1e6,
                    d.rx_no_desc as f64 / dt / 1e6,
                    d.rx_xoff,
                    d.rx_pfc_xoff
                );
                let (lfc, pfc) = dev.xoff_all_ports();
                println!("interval: xoff counters, all ports: link {} priority {}", lfc, pfc);
                (last, t) = (now, Instant::now());
            }
        }
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let stats = dev.port_stats().since(&before);
    if !args.senders.is_empty() {
        let tx: u64 = results[n..].iter().map(|r| rate(r.tx_packets, r.cycles, hz)).sum();
        println!("senders: {} threads on CPUs {:?}, tx {} pps (not in the totals below)", args.senders.len(), args.senders, tx);
    }
    report(&results[..n], hz, args.frame as u64, link.speed_mbps as u64);
    println!(
        "port: rx {} unicast {} multicast {} broadcast {} bytes, tx {} unicast {} multicast {} broadcast {} bytes, {} CRC errors, flow control rx xoff {} xon {} pfc xoff {} tx xoff {}, rx drops no-desc {} buffer {}",
        stats.rx_unicast, stats.rx_multicast, stats.rx_broadcast, stats.rx_bytes, stats.tx_unicast, stats.tx_multicast, stats.tx_broadcast,
        stats.tx_bytes, stats.crc_errors, stats.rx_xoff, stats.rx_xon, stats.rx_pfc_xoff, stats.tx_xoff, stats.rx_no_desc, stats.rx_buf_drops
    );
    drop(queues);
    if let Err(e) = dev.shutdown() {
        log::warn!("PF reset at exit: {}", e);
    }
}

/// Mode fwd: W forwarding threads over the N queue pairs, thread k on CPU `cpus[k]` forwarding what queues
/// k, k + W, .. receive on Tx queue k (the generator spreads its frames over all N steering MACs).
#[allow(clippy::too_many_arguments)]
fn forward(
    p: &LinuxPlatform,
    dev: &Device<'_, LinuxPlatform>,
    queues: &mut [(ice::TxQueue<'_, LinuxPlatform>, ice::RxQueue<'_, LinuxPlatform>)],
    args: &Args,
    mac: [u8; 6],
    hz: u64,
    mbps: u64,
    before: &ice::PortStats,
) {
    let n = args.queues;
    let w = args.fwd_workers.unwrap_or(n).clamp(1, n);
    let dst = args.fwd_dst.unwrap_or_else(|| {
        eprintln!("--mode fwd needs --fwd-dst");
        exit(2)
    });
    let lut_mem = p.dma_alloc(TABLE_SIZE, 64).expect("lookup table");
    let lut = unsafe { std::slice::from_raw_parts_mut(lut_mem.va as *mut i8, TABLE_SIZE) };
    populate_lut(lut);
    let lut: &[i8] = lut;
    let caches: Vec<&mut [[u64; 2]]> = (0..w)
        .map(|_| {
            let c = p.dma_alloc(CACHE_ENTRIES * ENTRY_BYTES, 4096).expect("flow cache");
            unsafe { std::slice::from_raw_parts_mut(c.va as *mut [u64; 2], CACHE_ENTRIES) }
        })
        .collect();
    log::info!("fwd: {} workers on CPUs {:?} over {} queues, to {}", w, &args.cpus[..w], n, Mac(dst));
    let (txs, rxs): (Vec<_>, Vec<_>) = queues.iter_mut().map(|(t, r)| (t, r)).unzip();
    let mut rx_sets: Vec<Vec<&mut ice::RxQueue<'_, LinuxPlatform>>> = (0..w).map(|_| Vec::new()).collect();
    for (j, r) in rxs.into_iter().enumerate() {
        rx_sets[j % w].push(r);
    }
    let barrier = Barrier::new(w);
    let cycles = args.secs * hz;
    let results: Vec<WorkerResult> = std::thread::scope(|s| {
        let handles: Vec<_> = txs
            .into_iter()
            .zip(rx_sets)
            .zip(caches)
            .zip(&args.cpus)
            .map(|(((tx, mut rset), cache), &cpu)| {
                let barrier = &barrier;
                s.spawn(move || {
                    pin_to(cpu);
                    let mut m = Maglev::new(lut, cache);
                    barrier.wait();
                    run_forwarder(p, tx, &mut rset, &mut m, mac, dst, cycles)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let stats = dev.port_stats().since(before);
    report(&results, hz, args.frame as u64, mbps);
    let tx: u64 = results.iter().map(|r| rate(r.tx_packets, r.cycles, hz)).sum();
    println!("fwd: {} workers, {} pps forwarded, {} TSC cycles per forwarded frame per worker", w, tx, if tx > 0 { hz * w as u64 / tx } else { 0 });
    println!(
        "port: rx {} unicast {} multicast {} broadcast {} bytes, tx {} unicast {} multicast {} broadcast {} bytes, {} CRC errors, flow control rx xoff {} xon {} pfc xoff {} tx xoff {}, rx drops no-desc {} buffer {}",
        stats.rx_unicast, stats.rx_multicast, stats.rx_broadcast, stats.rx_bytes, stats.tx_unicast, stats.tx_multicast, stats.tx_broadcast,
        stats.tx_bytes, stats.crc_errors, stats.rx_xoff, stats.rx_xon, stats.rx_pfc_xoff, stats.tx_xoff, stats.rx_no_desc, stats.rx_buf_drops
    );
}

fn frames_dst(f: &TxFrame) -> [u8; 6] {
    unsafe { std::slice::from_raw_parts(f.buf.va, 6) }.try_into().unwrap()
}

fn report(results: &[WorkerResult], hz: u64, frame: u64, mbps: u64) {
    let (mut tx, mut rx) = (0, 0);
    for (q, r) in results.iter().enumerate() {
        let (tpps, rpps) = (rate(r.tx_packets, r.cycles, hz), rate(r.rx.packets, r.cycles, hz));
        tx += tpps;
        rx += rpps;
        println!("queue {:2}: tx {:>11} pps, rx {:>11} pps, rx errors {}", q, tpps, rpps, r.rx.errors);
    }
    let line = if mbps != 0 { line_rate_pps(frame, mbps) } else { 0 };
    println!("total: tx {} pps, rx {} pps over {} queues; line rate of {}-byte frames at {} Mb/s is {} pps", tx, rx, results.len(), frame, mbps, line);
}
