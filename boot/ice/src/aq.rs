//! The control queue ("admin queue") between the PF driver and the device firmware (E810 datasheet: control
//! queues, and the admin command descriptions). The admin transmit queue (ATQ) carries the driver's commands, the admin
//! receive queue (ARQ) the firmware's events. A command is one 32-byte descriptor and, for indirect commands, a buffer
//! the descriptor points to. The driver sends one command at a time and polls the ATQ head until the firmware passed
//! the descriptor, then reads the write-back from the same descriptor.

use crate::regs::*;
use crate::{DmaRegion, Error, Platform, Result};
use core::ptr;
use core::sync::atomic::{fence, Ordering};

/// A control queue descriptor. `params` holds the command-specific 16 bytes; indirect commands keep the buffer address
/// in `params[8..16]` (high dword, then low dword).
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AqDesc {
    pub flags: u16,
    pub opcode: u16,
    pub datalen: u16,
    pub retval: u16,
    pub cookie_high: u32,
    pub cookie_low: u32,
    pub params: [u8; 16],
}

const _: () = assert!(core::mem::size_of::<AqDesc>() == 32);

/// Descriptor flags.
pub mod flags {
    /// Set by the firmware: done.
    pub const DD: u16 = 1 << 0;
    /// Set by the firmware: completed.
    pub const CMP: u16 = 1 << 1;
    /// Set by the firmware: error.
    pub const ERR: u16 = 1 << 2;
    /// The buffer is larger than 512 bytes.
    pub const LB: u16 = 1 << 9;
    /// The buffer carries data to the firmware.
    pub const RD: u16 = 1 << 10;
    /// A buffer is attached.
    pub const BUF: u16 = 1 << 12;
    /// No interrupt on completion.
    pub const SI: u16 = 1 << 13;
}

/// Buffers above this size need `flags::LB`.
pub const LARGE_BUF: usize = 512;

/// Opcodes the driver uses.
pub mod opc {
    pub const GET_VER: u16 = 0x0001;
    pub const LIST_FUNC_CAPS: u16 = 0x000A;
    pub const MANAGE_MAC_READ: u16 = 0x0107;
    pub const CLEAR_PXE_MODE: u16 = 0x0110;
    pub const GET_SW_CFG: u16 = 0x0200;
    pub const ADD_VSI: u16 = 0x0210;
    pub const ADD_SW_RULES: u16 = 0x02A0;
    pub const CLEAR_PF_CFG: u16 = 0x02A4;
    pub const GET_DFLT_TOPO: u16 = 0x0400;
    pub const ADD_SCHED_ELEMS: u16 = 0x0401;
    pub const DELETE_SCHED_ELEMS: u16 = 0x040F;
    pub const QUERY_SCHED_RES: u16 = 0x0412;
    pub const SET_MAC_CFG: u16 = 0x0603;
    pub const RESTART_AN: u16 = 0x0605;
    pub const GET_LINK_STATUS: u16 = 0x0607;
    pub const SET_RSS_KEY: u16 = 0x0B02;
    pub const SET_RSS_LUT: u16 = 0x0B03;
    pub const ADD_TXQS: u16 = 0x0C30;
}

/// The name of a firmware return value (`retval`).
pub fn retval_name(retval: u16) -> &'static str {
    match retval {
        0 => "OK",
        1 => "EPERM",
        2 => "ENOENT",
        3 => "ESRCH",
        4 => "EINTR",
        5 => "EIO",
        6 => "ENXIO",
        7 => "E2BIG",
        8 => "EAGAIN",
        9 => "ENOMEM",
        10 => "EACCES",
        11 => "EFAULT",
        12 => "EBUSY",
        13 => "EEXIST",
        14 => "EINVAL",
        15 => "ENOTTY",
        16 => "ENOSPC",
        17 => "ENOSYS",
        18 => "ERANGE",
        19 => "EFLUSHED",
        20 => "BAD_ADDR",
        21 => "EMODE",
        22 => "EFBIG",
        _ => "unknown",
    }
}

impl AqDesc {
    /// A command without buffer, as the Linux driver fills it (`SI`: no completion interrupt).
    pub fn new(opcode: u16) -> AqDesc {
        AqDesc { flags: flags::SI, opcode, ..Default::default() }
    }

    pub fn set_u8(&mut self, offset: usize, v: u8) {
        self.params[offset] = v;
    }

    pub fn set_u16(&mut self, offset: usize, v: u16) {
        self.params[offset..offset + 2].copy_from_slice(&v.to_le_bytes());
    }

    pub fn set_u32(&mut self, offset: usize, v: u32) {
        self.params[offset..offset + 4].copy_from_slice(&v.to_le_bytes());
    }

    pub fn u8_at(&self, offset: usize) -> u8 {
        self.params[offset]
    }

    pub fn u16_at(&self, offset: usize) -> u16 {
        u16::from_le_bytes([self.params[offset], self.params[offset + 1]])
    }

    pub fn u32_at(&self, offset: usize) -> u32 {
        u32::from_le_bytes(self.params[offset..offset + 4].try_into().unwrap())
    }

    /// Points the descriptor at a buffer of `len` bytes at `iova`.
    pub fn attach_buffer(&mut self, iova: u64, len: usize) {
        self.flags |= flags::BUF;
        if len > LARGE_BUF {
            self.flags |= flags::LB;
        }
        self.datalen = len as u16;
        self.set_u32(8, (iova >> 32) as u32);
        self.set_u32(12, iova as u32);
    }

    pub fn buffer_iova(&self) -> u64 {
        ((self.u32_at(8) as u64) << 32) | self.u32_at(12) as u64
    }
}

/// Entries of the ATQ and ARQ, and the size of each buffer.
pub const ATQ_LEN: usize = 32;
pub const ARQ_LEN: usize = 16;
pub const AQ_BUF: usize = 4096;
/// How long a command may take, in microseconds, and the polling step.
const ATQ_TIMEOUT_US: u64 = 3_000_000;
const POLL_US: u64 = 10;

/// The admin transmit and receive queues of the PF.
pub struct ControlQueue {
    atq: DmaRegion,
    arq: DmaRegion,
    /// The one ATQ buffer (commands go one at a time) and the ARQ buffers, `AQ_BUF` each.
    atq_buf: DmaRegion,
    arq_bufs: DmaRegion,
    atq_next: usize,
    arq_next: usize,
}

fn alloc(p: &impl Platform, len: usize, align: usize) -> Result<DmaRegion> {
    p.dma_alloc(len, align).ok_or(Error::NoDmaMemory)
}

impl ControlQueue {
    /// Turns both queues off, as the Linux driver's `ice_shutdown_ctrlq` does.
    pub fn disable(p: &impl Platform) {
        for r in [PF_FW_ATQH, PF_FW_ATQT, PF_FW_ATQLEN, PF_FW_ATQBAL, PF_FW_ATQBAH, PF_FW_ARQH, PF_FW_ARQT, PF_FW_ARQLEN, PF_FW_ARQBAL, PF_FW_ARQBAH] {
            p.write32(r, 0);
        }
    }

    /// Allocates both queues and programs them into the device, which must have just left a PF reset.
    pub fn init(p: &impl Platform) -> Result<ControlQueue> {
        let atq = alloc(p, ATQ_LEN * 32, 4096)?;
        let arq = alloc(p, ARQ_LEN * 32, 4096)?;
        let atq_buf = alloc(p, AQ_BUF, 4096)?;
        let arq_bufs = alloc(p, ARQ_LEN * AQ_BUF, 4096)?;
        let mut cq = ControlQueue { atq, arq, atq_buf, arq_bufs, atq_next: 0, arq_next: 0 };
        for i in 0..ARQ_LEN {
            cq.post_arq(i);
        }
        fence(Ordering::SeqCst);
        // The same order as the Linux driver: head and tail, length with enable, then the base address.
        for (bal, bah, len, h, t, ring, n) in [
            (PF_FW_ATQBAL, PF_FW_ATQBAH, PF_FW_ATQLEN, PF_FW_ATQH, PF_FW_ATQT, cq.atq, ATQ_LEN),
            (PF_FW_ARQBAL, PF_FW_ARQBAH, PF_FW_ARQLEN, PF_FW_ARQH, PF_FW_ARQT, cq.arq, ARQ_LEN),
        ] {
            p.write32(h, 0);
            p.write32(t, 0);
            p.write32(len, n as u32 | PF_FW_QLEN_ENABLE);
            p.write32(bal, ring.iova as u32);
            p.write32(bah, (ring.iova >> 32) as u32);
            if p.read32(bal) != ring.iova as u32 {
                return Err(Error::Device("control queue base address did not stick"));
            }
        }
        // Every ARQ descriptor belongs to the firmware.
        p.write32(PF_FW_ARQT, (ARQ_LEN - 1) as u32);
        Ok(cq)
    }

    fn atq_desc(&self, i: usize) -> *mut AqDesc {
        unsafe { (self.atq.va as *mut AqDesc).add(i) }
    }

    fn arq_desc(&self, i: usize) -> *mut AqDesc {
        unsafe { (self.arq.va as *mut AqDesc).add(i) }
    }

    fn post_arq(&mut self, i: usize) {
        let mut d = AqDesc { flags: 0, ..Default::default() };
        d.attach_buffer(self.arq_bufs.iova + (i * AQ_BUF) as u64, AQ_BUF);
        unsafe { ptr::write_volatile(self.arq_desc(i), d) };
    }

    /// Sends `desc` with `buf` (if any) and waits for the firmware. On return `desc` holds the write-back and `buf`
    /// what the firmware wrote into the buffer. Fails on a timeout or a nonzero return value.
    pub fn send(&mut self, p: &impl Platform, desc: &mut AqDesc, buf: Option<&mut [u8]>) -> Result<()> {
        let opcode = desc.opcode;
        let i = self.atq_next;
        let mut buf = buf;
        if let Some(b) = buf.as_deref() {
            assert!(b.len() <= AQ_BUF, "admin queue buffer larger than 4 KiB");
            unsafe { ptr::copy_nonoverlapping(b.as_ptr(), self.atq_buf.va, b.len()) };
            desc.attach_buffer(self.atq_buf.iova, b.len());
        }
        unsafe { ptr::write_volatile(self.atq_desc(i), *desc) };
        fence(Ordering::SeqCst);
        self.atq_next = (i + 1) % ATQ_LEN;
        p.write32(PF_FW_ATQT, self.atq_next as u32);
        let mut waited = 0;
        while p.read32(PF_FW_ATQH) & PF_FW_QH_M != self.atq_next as u32 {
            if waited >= ATQ_TIMEOUT_US {
                let len = p.read32(PF_FW_ATQLEN);
                log::error!(
                    "ice: admin command {:#06x} timed out: ATQH {} ATQT {} ATQLEN {:#x}{}{}{}",
                    opcode,
                    p.read32(PF_FW_ATQH),
                    self.atq_next,
                    len,
                    if len & PF_FW_QLEN_VFE != 0 { " VFE" } else { "" },
                    if len & PF_FW_QLEN_OVFL != 0 { " OVFL" } else { "" },
                    if len & PF_FW_QLEN_CRIT != 0 { " CRIT" } else { "" },
                );
                return Err(Error::Timeout("an admin queue command"));
            }
            p.delay_us(POLL_US);
            waited += POLL_US;
        }
        fence(Ordering::SeqCst);
        *desc = unsafe { ptr::read_volatile(self.atq_desc(i)) };
        if let Some(b) = buf.as_deref_mut() {
            unsafe { ptr::copy_nonoverlapping(self.atq_buf.va, b.as_mut_ptr(), b.len()) };
        }
        if desc.flags & flags::DD == 0 {
            log::warn!("ice: admin command {:#06x}: head passed the descriptor but DD is clear (flags {:#06x})", opcode, desc.flags);
        }
        if desc.retval != 0 {
            return Err(Error::Aq { opcode, retval: desc.retval });
        }
        Ok(())
    }

    /// Takes every event the firmware posted to the ARQ and gives the descriptors back; returns how many there were.
    pub fn drain_events(&mut self, p: &impl Platform) -> usize {
        let head = (p.read32(PF_FW_ARQH) & PF_FW_QH_M) as usize;
        let mut n = 0;
        while self.arq_next != head {
            let d = unsafe { ptr::read_volatile(self.arq_desc(self.arq_next)) };
            log::debug!("ice: firmware event {:#06x} retval {} datalen {}", d.opcode, d.retval, d.datalen);
            self.post_arq(self.arq_next);
            p.write32(PF_FW_ARQT, self.arq_next as u32);
            self.arq_next = (self.arq_next + 1) % ARQ_LEN;
            n += 1;
        }
        n
    }
}

/// Command layouts: the byte offsets of fields in `AqDesc::params` and of response buffers.
pub mod cmd {
    /// Get Version (0x0001) response: firmware build, branch/major/minor/patch, API branch/major/minor/patch.
    pub const VER_FW_BUILD: usize = 4;
    pub const VER_FW_MAJOR: usize = 9;
    pub const VER_FW_MINOR: usize = 10;
    pub const VER_FW_PATCH: usize = 11;
    pub const VER_API_MAJOR: usize = 13;
    pub const VER_API_MINOR: usize = 14;
    pub const VER_API_PATCH: usize = 15;

    /// List Function Capabilities (0x000A): element count written back at 4; 32-byte elements of `cap` (u16 at 0),
    /// `number` (u32 at 4), `logical_id` (u32 at 8), `phys_id` (u32 at 12).
    pub const CAPS_COUNT: usize = 4;
    pub const CAPS_ELEM: usize = 32;
    pub const CAP_VSI: u16 = 0x0017;
    pub const CAP_RSS: u16 = 0x0040;
    pub const CAP_RXQS: u16 = 0x0041;
    pub const CAP_TXQS: u16 = 0x0042;
    pub const CAP_MSIX: u16 = 0x0043;

    /// Manage MAC Read (0x0107): `flags` (u16 at 0, LAN address valid = bit 4), `num_addr` (u8 at 4); 8-byte
    /// response entries `lport`, `addr_type` (0 = LAN), `mac[6]`.
    pub const MAC_READ_FLAGS: usize = 0;
    pub const MAC_READ_LAN_VALID: u16 = 1 << 4;
    pub const MAC_READ_NUM_ADDR: usize = 4;
    pub const MAC_READ_ENTRY: usize = 8;

    /// Clear PXE Mode (0x0110): `rx_cnt` at 0, value 2.
    pub const CLEAR_PXE_RX_CNT: u8 = 0x2;

    /// Get Switch Configuration (0x0200): next element at 2, element count at 4; 6-byte response elements
    /// `vsi_port_num` (u16: number in 9:0, type in 15:14: 0 physical port, 1 virtual port, 2 VSI), `swid` (u16),
    /// `pf_vf_num` (u16).
    pub const SW_CFG_ELEMENT: usize = 2;
    pub const SW_CFG_NUM_ELEMS: usize = 4;
    pub const SW_CFG_ELEM: usize = 6;
    pub const SW_CFG_TYPE_S: u16 = 14;
    pub const SW_CFG_TYPE_PHYS_PORT: u16 = 0;
    pub const SW_CFG_TYPE_VIRT_PORT: u16 = 1;
    pub const SW_CFG_BUF: usize = 2048;

    /// Add VSI (0x0210): `vsi_num` (u16 at 0), `cmd_flags` (u16 at 2), `vf_id` (u8 at 4), `vsi_flags` (u16 at 6, type
    /// PF = 2); response `vsi_num` at 0 (bits 9:0), `vsi_used` at 4, `vsi_free` at 6. The buffer is the 128-byte VSI
    /// properties block.
    pub const VSI_FLAGS: usize = 6;
    pub const VSI_TYPE_PF: u16 = 2;
    pub const VSI_NUM_M: u16 = 0x3FF;
    pub const VSI_USED: usize = 4;
    pub const VSI_FREE: usize = 6;

    /// Add Switch Rules (0x02A0): rule count at 0.
    pub const SW_RULES_NUM: usize = 0;

    /// Scheduler commands (0x0401, 0x040F): `num_elem_req` (u16 at 0), `num_elem_resp` (u16 at 2). Get Default
    /// Topology (0x0400): `port_num` (u8 at 0), `num_branches` (u8 at 1, written back).
    pub const SCHED_NUM_REQ: usize = 0;
    pub const SCHED_NUM_RESP: usize = 2;
    pub const TOPO_PORT: usize = 0;
    pub const TOPO_NUM_BRANCHES: usize = 1;

    /// Restart Autonegotiation (0x0605): `lport` (u8 at 0), `cmd_flags` (u8 at 2): restart (bit 1), link enable (bit 2).
    /// Set MAC config (direct): `max_frame_size` (u16) at 0, then the Tx timer and flow-control refresh fields this
    /// driver leaves 0 (it never sends pause frames).
    pub const SET_MAC_CFG_MAX_FRAME: usize = 0;
    pub const RESTART_AN_LPORT: usize = 0;
    pub const RESTART_AN_FLAGS: usize = 2;
    pub const RESTART_AN_RESTART: u8 = 1 << 1;
    pub const RESTART_AN_ENABLE: u8 = 1 << 2;

    /// Get Link Status (0x0607): `lport` (u8 at 0), `cmd_flags` (u16 at 2: link status events off = 2). Response
    /// buffer: `link_info` at 2 (bit 0 = up), `an_info` at 3, `max_frame_size` (u16) at 6, `link_speed` (u16) at 10.
    pub const LINK_LPORT: usize = 0;
    pub const LINK_FLAGS: usize = 2;
    pub const LINK_LSE_DISABLE: u16 = 0x2;
    pub const LINK_BUF: usize = 32;
    pub const LINK_INFO: usize = 2;
    pub const LINK_UP: u8 = 1 << 0;
    pub const LINK_MAX_FRAME: usize = 6;
    pub const LINK_SPEED: usize = 10;

    /// Set RSS Key (0x0B02) and Set RSS LUT (0x0B03): `vsi_id` (u16 at 0, bit 15 valid); LUT `flags` (u16 at 2):
    /// type in bits 1:0 (VSI 0, PF 1), size in bits 3:2 (64 entries 0, 2K entries bit 3).
    pub const RSS_VSI_VALID: u16 = 1 << 15;
    pub const RSS_LUT_FLAGS: usize = 2;
    pub const RSS_LUT_TYPE_PF: u16 = 1;
    pub const RSS_LUT_SIZE_2K: u16 = 1 << 3;
    pub const RSS_LUT_PF_ENTRIES: usize = 2048;
    pub const RSS_KEY_BYTES: usize = 52;

    /// Add Tx LAN Queues (0x0C30): `num_qgrps` (u8 at 0).
    pub const TXQS_NUM_QGRPS: usize = 0;
}

/// The link speed in Mb/s of a `link_speed` bit.
pub fn link_speed_mbps(link_speed: u16) -> u32 {
    const SPEEDS: [u32; 12] = [10, 100, 1000, 2500, 5000, 10000, 20000, 25000, 40000, 50000, 100000, 200000];
    (0..12).rev().find(|&b| link_speed & (1 << b) != 0).map_or(0, |b| SPEEDS[b])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn descriptor_layout() {
        let mut d = AqDesc::new(opc::ADD_VSI);
        d.set_u16(cmd::VSI_FLAGS, cmd::VSI_TYPE_PF);
        d.attach_buffer(0x0000_0012_3456_7000, 128);
        let bytes: [u8; 32] = unsafe { core::mem::transmute(d) };
        assert_eq!(&bytes[0..2], &(flags::SI | flags::BUF).to_le_bytes());
        assert_eq!(&bytes[2..4], &[0x10, 0x02]);
        assert_eq!(&bytes[4..6], &[128, 0]);
        // params start at byte 16: vsi_flags at 16 + 6, address high at 24, low at 28.
        assert_eq!(&bytes[22..24], &[2, 0]);
        assert_eq!(&bytes[24..28], &[0x12, 0, 0, 0]);
        assert_eq!(&bytes[28..32], &[0x00, 0x70, 0x56, 0x34]);
        assert_eq!(d.buffer_iova(), 0x12_3456_7000);
        let mut big = AqDesc::new(opc::GET_DFLT_TOPO);
        big.attach_buffer(0x1000, 4096);
        assert_eq!(big.flags, flags::SI | flags::BUF | flags::LB);
        assert_eq!(big.datalen, 4096);
    }

    #[test]
    fn speeds() {
        assert_eq!(link_speed_mbps(0x400), 100_000);
        assert_eq!(link_speed_mbps(0x80), 25_000);
        assert_eq!(link_speed_mbps(0), 0);
        assert_eq!(retval_name(14), "EINVAL");
    }
}
