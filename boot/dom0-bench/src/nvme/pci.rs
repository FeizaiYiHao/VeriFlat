//! NVMe discovery over `sys_pci_info` and the BAR address type (Atmosphere's `pcid::utils::PciBarAddr`).

use vsys::{sys_pci_info, PCI_BAR_WINDOW_BASE};

/// PCI class and subclass of an NVMe controller (mass storage, non-volatile memory).
const CLASS_STORAGE: usize = 0x01;
const SUBCLASS_NVME: usize = 0x08;

#[derive(Clone, Copy, Debug)]
pub struct PciBarAddr {
    base: u64,
    #[allow(dead_code)]
    size: usize,
}

impl PciBarAddr {
    pub fn new(base: u64, size: usize) -> PciBarAddr {
        PciBarAddr { base, size }
    }

    pub fn get_base(&self) -> u64 {
        self.base
    }
}

/// An NVMe function the loader recorded.
#[derive(Clone, Copy, Debug)]
pub struct NvmeFunction {
    pub bus: usize,
    pub dev: usize,
    pub fun: usize,
    pub vendor: usize,
    pub device: usize,
    /// BAR0 physical base and page count.
    pub bar_phys: usize,
    pub bar_pages: usize,
}

impl NvmeFunction {
    /// Where every process of the benchmark maps BAR0: dom0's loader window, and the same address
    /// in the driver process that receives the pages.
    pub fn bar_va(&self) -> usize {
        PCI_BAR_WINDOW_BASE + self.bar_phys
    }

    pub fn bar(&self) -> PciBarAddr {
        PciBarAddr::new(self.bar_va() as u64, self.bar_pages * 4096)
    }
}

/// `VERIFLAT_NVME_BDF=<bus>:<dev>.<fn>` (hexadecimal, as lspci prints it) of the dom0 build: the one NVMe function every
/// NVMe test and benchmark of dom0 may drive. Required on bare metal (`selected_nvme`).
const NVME_BDF: Option<(usize, usize, usize)> = match option_env!("VERIFLAT_NVME_BDF") {
    Some(s) => Some(parse_bdf(s)),
    None => None,
};

/// `VERIFLAT_NVME_INDEX` of the dom0 build (default 0): under a hypervisor without `VERIFLAT_NVME_BDF`, the recorded
/// NVMe function number in B/D/F order every NVMe test and benchmark drives. Ignored on bare metal.
pub const NVME_INDEX: usize = match option_env!("VERIFLAT_NVME_INDEX") {
    Some(s) => parse_decimal(s),
    None => 0,
};

/// `VERIFLAT_NVME_ASSUME_BARE_METAL=1` of the dom0 build: take the bare-metal branch of `selected_nvme` under a
/// hypervisor too, to exercise it under QEMU.
const ASSUME_BARE_METAL: bool = match option_env!("VERIFLAT_NVME_ASSUME_BARE_METAL") {
    Some(s) => s.len() == 1 && s.as_bytes()[0] == b'1',
    None => false,
};

/// `VERIFLAT_NVME_OPS=read|write` of the dom0 build: the NVMe benchmarks run only their read or only their write
/// points (unset: both, reads first), so a read boot can follow a discard without earlier write points changing what
/// the reads find on the disk.
const NVME_OPS: u8 = match option_env!("VERIFLAT_NVME_OPS") {
    None => 0,
    Some(s) => match s.as_bytes() {
        b"read" => 1,
        b"write" => 2,
        _ => panic!("VERIFLAT_NVME_OPS must be read or write"),
    },
};

/// Whether the NVMe benchmarks run their points of this kind (`VERIFLAT_NVME_OPS`).
pub const fn op_selected(is_write: bool) -> bool {
    NVME_OPS == 0 || (NVME_OPS == 2) == is_write
}

const fn hex_digit(c: u8) -> usize {
    match c {
        b'0'..=b'9' => (c - b'0') as usize,
        b'a'..=b'f' => (c - b'a' + 10) as usize,
        b'A'..=b'F' => (c - b'A' + 10) as usize,
        _ => panic!("VERIFLAT_NVME_BDF must look like 3b:00.0 (hexadecimal bus:dev.fn)"),
    }
}

/// Parses `bb:dd.f`, hexadecimal, an optional `0000:` segment prefix dropped (segment 0 is the only one recorded).
const fn parse_bdf(s: &str) -> (usize, usize, usize) {
    let b = s.as_bytes();
    let start = if b.len() == 12 && b[4] == b':' { 5 } else { 0 };
    assert!(b.len() - start == 7 && b[start + 2] == b':' && b[start + 5] == b'.', "VERIFLAT_NVME_BDF must look like 3b:00.0 (hexadecimal bus:dev.fn)");
    let bus = hex_digit(b[start]) * 16 + hex_digit(b[start + 1]);
    let dev = hex_digit(b[start + 3]) * 16 + hex_digit(b[start + 4]);
    let fun = hex_digit(b[start + 6]);
    assert!(dev < 32 && fun < 8, "VERIFLAT_NVME_BDF: device must be below 0x20 and function below 8");
    (bus, dev, fun)
}

const fn parse_decimal(s: &str) -> usize {
    let b = s.as_bytes();
    let (mut i, mut v) = (0, 0);
    while i < b.len() {
        assert!(b[i].is_ascii_digit(), "VERIFLAT_NVME_INDEX must be a decimal number");
        v = v * 10 + (b[i] - b'0') as usize;
        i += 1;
    }
    v
}

/// Whether dom0 runs under a hypervisor: CPUID.01H:ECX[31], unless the build assumes bare metal.
pub fn under_hypervisor() -> bool {
    !ASSUME_BARE_METAL && core::arch::x86_64::__cpuid(1).ecx & (1 << 31) != 0
}

/// Why `choose_nvme` picked no function.
pub enum NoNvme {
    /// The loader recorded no NVMe function at all.
    NoneRecorded,
    /// Bare metal and no `VERIFLAT_NVME_BDF`.
    NotNamed,
    /// `VERIFLAT_NVME_BDF` names a function the loader did not record as NVMe.
    NamedNotRecorded,
    /// Under a hypervisor, no recorded NVMe function `NVME_INDEX`.
    NoIndex,
}

/// The NVMe function every NVMe test and benchmark of dom0 drives (`client::run`, `parallel::run`,
/// `parallel_xproc`), without logging: the function `VERIFLAT_NVME_BDF` names if it is set; otherwise, under a
/// hypervisor, recorded NVMe function `NVME_INDEX`; otherwise none, so that on bare metal no drive is reset, read or
/// written unless the build names it. Only reads the loader's record (`sys_pci_info`); touches no device.
pub fn choose_nvme() -> Result<NvmeFunction, NoNvme> {
    if find_nvme_index(0).is_none() {
        return Err(NoNvme::NoneRecorded);
    }
    if let Some((bus, dev, fun)) = NVME_BDF {
        let mut i = 0;
        while let Some(f) = find_nvme_index(i) {
            if (f.bus, f.dev, f.fun) == (bus, dev, fun) {
                return Ok(f);
            }
            i += 1;
        }
        return Err(NoNvme::NamedNotRecorded);
    }
    if !under_hypervisor() {
        return Err(NoNvme::NotNamed);
    }
    find_nvme_index(NVME_INDEX).ok_or(NoNvme::NoIndex)
}

/// A fixed-size line buffer for one log line, so that the skip line needs no heap.
struct Line {
    bytes: [u8; 1024],
    len: usize,
}

impl core::fmt::Write for Line {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let n = s.len().min(self.bytes.len() - self.len);
        self.bytes[self.len..self.len + n].copy_from_slice(&s.as_bytes()[..n]);
        self.len += n;
        Ok(())
    }
}

/// `choose_nvme`, logging one line that says why `who` is skipped when it picks no function; that line lists every
/// recorded NVMe function as bus:dev.fn vendor:device (model and serial would need an Identify command, which this
/// avoids: nothing touches a drive before it is chosen).
pub fn selected_nvme(who: &str) -> Option<NvmeFunction> {
    use core::fmt::Write;
    let reason = match choose_nvme() {
        Ok(f) => return Some(f),
        Err(NoNvme::NoneRecorded) => {
            log::info!("{} skipped: no NVMe function recorded", who);
            return None;
        }
        Err(NoNvme::NotNamed) => "bare metal and no NVMe function named; build dom0 with VERIFLAT_NVME_BDF=<bus:dev.fn> to pick one",
        Err(NoNvme::NamedNotRecorded) => "VERIFLAT_NVME_BDF names no recorded NVMe function",
        Err(NoNvme::NoIndex) => "VERIFLAT_NVME_INDEX names no recorded NVMe function",
    };
    let mut line = Line { bytes: [0; 1024], len: 0 };
    let _ = write!(line, "{} skipped: {}", who, reason);
    if let Some((bus, dev, fun)) = NVME_BDF {
        let _ = write!(line, " (VERIFLAT_NVME_BDF={:02x}:{:02x}.{})", bus, dev, fun);
    }
    let _ = write!(line, "; recorded NVMe functions:");
    let mut i = 0;
    while let Some(f) = find_nvme_index(i) {
        let _ = write!(line, " {:02x}:{:02x}.{} {:04x}:{:04x}", f.bus, f.dev, f.fun, f.vendor, f.device);
        i += 1;
    }
    log::info!("{}", core::str::from_utf8(&line.bytes[..line.len]).unwrap_or("?"));
    None
}

/// The recorded NVMe function `index` in B/D/F order (0 is `find_nvme`'s).
pub fn find_nvme_index(mut index: usize) -> Option<NvmeFunction> {
    for bus in 0..256 {
        for dev in 0..32 {
            for fun in 0..8 {
                let (rax, base, pages) = unsafe { sys_pci_info(bus, dev, fun) };
                if rax < 0 {
                    continue;
                }
                let id = rax as usize;
                if (id >> 48) & 0xff == CLASS_STORAGE && (id >> 40) & 0xff == SUBCLASS_NVME {
                    if index > 0 {
                        index -= 1;
                        continue;
                    }
                    return Some(NvmeFunction { bus, dev, fun, vendor: (id >> 16) & 0xffff, device: id & 0xffff, bar_phys: base, bar_pages: pages });
                }
            }
        }
    }
    None
}
