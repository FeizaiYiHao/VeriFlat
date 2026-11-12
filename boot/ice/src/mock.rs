//! A software model of the parts of an E810 PF the driver uses, for host tests: registers, the admin queue with
//! canned firmware answers, the Tx scheduler tree, Tx queues that loop every frame back to the Rx queue the switch
//! rules pick. It checks what it can: that every DMA address the driver hands over lies in memory the driver
//! allocated, that contexts carry what the driver configured, that the scheduler tree stays consistent. It encodes
//! the same reading of the datasheet as the driver, so it catches plumbing errors, not misreadings of the hardware.

use crate::aq::{cmd, flags, opc, AqDesc};
use crate::ctx::{get_bits, rx as rxf, tx as txf};
use crate::desc::{RxDesc, TxDesc, RXDID_FLEX_NIC, RX_STATUS0_DD, RX_STATUS0_EOF, TX_CMD_RS, TX_DTYPE_DESC_DONE};
use crate::regs::*;
use crate::sched::{self, ELEM_DATA_BYTES, GRP_HDR_BYTES};
use crate::{DmaRegion, Platform};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::vec::Vec;

pub const MOCK_MAC: [u8; 6] = [0x00, 0x1b, 0x21, 0xaa, 0xbb, 0xcc];
pub const MOCK_LPORT: u8 = 1;
pub const MOCK_VSI: u16 = 7;

#[derive(Default, Debug, Clone)]
pub struct MockTxq {
    pub base: u64,
    pub qlen: usize,
    pub head: usize,
    pub parent: u32,
}

#[derive(Default, Debug, Clone)]
pub struct MockRxq {
    pub base: u64,
    pub qlen: usize,
    pub buf_len: usize,
    pub head: usize,
    pub tail: usize,
    pub enabled: bool,
    pub dropped: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MockRule {
    pub recipe: u16,
    pub src: u16,
    pub act: u32,
    pub da: [u8; 6],
}

#[derive(Default)]
pub struct State {
    pub regs: HashMap<usize, u32>,
    pub allocations: Vec<(u64, usize)>,
    pub log: Vec<u16>,
    atq_head: usize,
    /// Scheduler nodes: TEID -> (parent, layer).
    pub nodes: HashMap<u32, (u32, usize)>,
    next_teid: u32,
    pub deleted: Vec<u32>,
    pub vsi_queues: usize,
    pub txq: HashMap<usize, MockTxq>,
    pub rxq: HashMap<usize, MockRxq>,
    pub rules: Vec<MockRule>,
    pub rss_lut: Vec<u8>,
    pub link_up: bool,
    pub resets: usize,
    /// Fault injection: Get Version answers EAGAIN this many more times; MAC rules are refused.
    pub get_ver_failures: usize,
    pub reject_mac_rules: bool,
}

pub struct Mock {
    pub state: Mutex<State>,
    clock: AtomicU64,
}

fn rd<T: Copy>(addr: u64) -> T {
    unsafe { std::ptr::read_volatile(addr as *const T) }
}

fn wr<T: Copy>(addr: u64, v: T) {
    unsafe { std::ptr::write_volatile(addr as *mut T, v) }
}

impl Mock {
    pub fn new(link_up_at_start: bool) -> Mock {
        let mut s = State { next_teid: 0x100, link_up: link_up_at_start, ..Default::default() };
        s.regs.insert(GLNVM_ULD, GLNVM_ULD_RESET_DONE);
        Mock { state: Mutex::new(s), clock: AtomicU64::new(0) }
    }
}

impl State {
    /// Panics unless `[addr, addr + len)` lies in one DMA allocation.
    fn check_dma(&self, addr: u64, len: usize, what: &str) {
        assert!(
            self.allocations.iter().any(|&(a, l)| addr >= a && addr + len as u64 <= a + l as u64),
            "device access to {:#x}+{} ({}) outside DMA memory",
            addr,
            len,
            what
        );
    }

    fn reg(&self, off: usize) -> u32 {
        *self.regs.get(&off).unwrap_or(&0)
    }

    fn pf_reset(&mut self) {
        self.resets += 1;
        let uld = self.reg(GLNVM_ULD);
        self.regs.clear();
        self.regs.insert(GLNVM_ULD, uld);
        self.atq_head = 0;
        self.nodes.clear();
        self.txq.clear();
        self.rxq.clear();
        self.rules.clear();
    }

    fn process_atq(&mut self, tail: usize) {
        let base = (self.reg(PF_FW_ATQBAH) as u64) << 32 | self.reg(PF_FW_ATQBAL) as u64;
        let len = (self.reg(PF_FW_ATQLEN) & PF_FW_QLEN_M) as usize;
        assert!(self.reg(PF_FW_ATQLEN) & PF_FW_QLEN_ENABLE != 0, "ATQ not enabled");
        self.check_dma(base, len * 32, "ATQ ring");
        while self.atq_head != tail {
            let addr = base + (self.atq_head * 32) as u64;
            let mut d: AqDesc = rd(addr);
            let retval = self.command(&mut d);
            d.flags |= flags::DD | flags::CMP;
            if retval != 0 {
                d.flags |= flags::ERR;
            }
            d.retval = retval;
            wr(addr, d);
            self.atq_head = (self.atq_head + 1) % len;
        }
        self.regs.insert(PF_FW_ATQH, self.atq_head as u32);
    }

    /// The command's buffer, after checking the descriptor's buffer flags.
    fn buffer(&self, d: &AqDesc, to_fw: bool) -> &'static mut [u8] {
        assert!(d.flags & flags::BUF != 0, "opcode {:#x} needs a buffer", d.opcode);
        assert_eq!(d.flags & flags::RD != 0, to_fw, "opcode {:#x}: RD flag", d.opcode);
        assert_eq!(d.flags & flags::LB != 0, d.datalen as usize > 512, "opcode {:#x}: LB flag", d.opcode);
        let iova = d.buffer_iova();
        self.check_dma(iova, d.datalen as usize, "admin buffer");
        unsafe { std::slice::from_raw_parts_mut(iova as *mut u8, d.datalen as usize) }
    }

    fn command(&mut self, d: &mut AqDesc) -> u16 {
        self.log.push(d.opcode);
        match d.opcode {
            opc::GET_VER if self.get_ver_failures > 0 => {
                self.get_ver_failures -= 1;
                8
            }
            opc::GET_VER => {
                d.set_u8(cmd::VER_FW_MAJOR, 1);
                d.set_u8(cmd::VER_FW_MINOR, 7);
                d.set_u8(cmd::VER_API_MAJOR, 1);
                d.set_u8(cmd::VER_API_MINOR, 7);
                0
            }
            opc::CLEAR_PF_CFG => 0,
            opc::CLEAR_PXE_MODE => {
                assert_eq!(d.u8_at(0), cmd::CLEAR_PXE_RX_CNT);
                0
            }
            opc::LIST_FUNC_CAPS => {
                let b = self.buffer(d, false);
                let caps = [(cmd::CAP_RXQS, 64u32, 0u32), (cmd::CAP_TXQS, 64, 0), (cmd::CAP_RSS, 2048, 8), (cmd::CAP_VSI, 768, 0)];
                for (i, (cap, number, phys)) in caps.iter().enumerate() {
                    let e = &mut b[i * cmd::CAPS_ELEM..(i + 1) * cmd::CAPS_ELEM];
                    e[0..2].copy_from_slice(&cap.to_le_bytes());
                    e[4..8].copy_from_slice(&number.to_le_bytes());
                    e[12..16].copy_from_slice(&phys.to_le_bytes());
                }
                d.set_u32(cmd::CAPS_COUNT, caps.len() as u32);
                0
            }
            opc::GET_SW_CFG => {
                let b = self.buffer(d, false);
                // A VSI element (type 2) first, then the physical port.
                b[0..2].copy_from_slice(&((2u16 << 14) | 5).to_le_bytes());
                b[6..8].copy_from_slice(&(MOCK_LPORT as u16).to_le_bytes());
                b[8..10].copy_from_slice(&3u16.to_le_bytes());
                d.set_u16(cmd::SW_CFG_NUM_ELEMS, 2);
                d.set_u16(cmd::SW_CFG_ELEMENT, 0);
                0
            }
            opc::MANAGE_MAC_READ => {
                let b = self.buffer(d, false);
                b[0] = MOCK_LPORT;
                b[1] = 0;
                b[2..8].copy_from_slice(&MOCK_MAC);
                d.set_u16(cmd::MAC_READ_FLAGS, cmd::MAC_READ_LAN_VALID);
                d.set_u8(cmd::MAC_READ_NUM_ADDR, 1);
                0
            }
            opc::QUERY_SCHED_RES => {
                let b = self.buffer(d, false);
                b.copy_from_slice(&sched::tests::resources_buf(9, [1, 1, 8, 8, 8, 8, 8, 8, 8]));
                0
            }
            opc::GET_DFLT_TOPO => {
                assert_eq!(d.u8_at(cmd::TOPO_PORT), MOCK_LPORT);
                let b = self.buffer(d, false);
                let topo = sched::tests::default_topology_buf();
                b.copy_from_slice(&topo[..b.len()]);
                for j in 0..9 {
                    let e = GRP_HDR_BYTES + j * ELEM_DATA_BYTES;
                    let parent = u32::from_le_bytes(topo[e..e + 4].try_into().unwrap());
                    let teid = u32::from_le_bytes(topo[e + 4..e + 8].try_into().unwrap());
                    self.nodes.insert(teid, (parent, j));
                }
                d.set_u8(cmd::TOPO_NUM_BRANCHES, 1);
                0
            }
            opc::DELETE_SCHED_ELEMS => {
                let b = self.buffer(d, true);
                let parent = u32::from_le_bytes(b[0..4].try_into().unwrap());
                let teid = u32::from_le_bytes(b[8..12].try_into().unwrap());
                assert_eq!(self.nodes.get(&teid).map(|n| n.0), Some(parent), "delete: wrong parent");
                assert!(!self.nodes.values().any(|n| n.0 == teid), "delete of a node with children");
                self.nodes.remove(&teid);
                self.deleted.push(teid);
                0
            }
            opc::ADD_SCHED_ELEMS => {
                assert_eq!(d.u16_at(cmd::SCHED_NUM_REQ), 1);
                let b = self.buffer(d, true);
                let parent = u32::from_le_bytes(b[0..4].try_into().unwrap());
                let n = u16::from_le_bytes([b[4], b[5]]) as usize;
                let (_, layer) = *self.nodes.get(&parent).expect("add: unknown parent");
                assert!(layer + 1 <= 7, "add: generic node below the queue group layer");
                for i in 0..n {
                    let e = GRP_HDR_BYTES + i * ELEM_DATA_BYTES;
                    assert_eq!(u32::from_le_bytes(b[e..e + 4].try_into().unwrap()), parent);
                    assert_eq!(&b[e + 8..e + 24], &sched::default_elem_info(sched::ELEM_TYPE_SE_GENERIC));
                    let teid = self.next_teid;
                    self.next_teid += 1;
                    b[e + 4..e + 8].copy_from_slice(&teid.to_le_bytes());
                    self.nodes.insert(teid, (parent, layer + 1));
                }
                assert!(self.nodes.values().filter(|v| v.0 == parent).count() <= 8, "too many children");
                d.set_u16(cmd::SCHED_NUM_RESP, 1);
                0
            }
            opc::ADD_VSI => {
                let b = self.buffer(d, true);
                assert_eq!(b.len(), 128);
                assert_eq!(d.u16_at(cmd::VSI_FLAGS), cmd::VSI_TYPE_PF);
                assert_eq!(b[2], 3, "switch ID");
                self.vsi_queues = u16::from_le_bytes([b[32], b[33]]) as usize;
                d.set_u16(0, MOCK_VSI);
                0
            }
            opc::ADD_TXQS => {
                assert_eq!(d.u8_at(cmd::TXQS_NUM_QGRPS), 1);
                let b = self.buffer(d, true);
                let parent = u32::from_le_bytes(b[0..4].try_into().unwrap());
                assert_eq!(self.nodes.get(&parent).map(|n| n.1), Some(7), "queue parent not a queue group node");
                assert_eq!(b[4], 1);
                let q = u16::from_le_bytes([b[8], b[9]]) as usize;
                let ctx = &b[16..38];
                let base = get_bits(ctx, txf::BASE.0, txf::BASE.1) << 7;
                let qlen = get_bits(ctx, txf::QLEN.0, txf::QLEN.1) as usize;
                assert_eq!(get_bits(ctx, txf::SRC_VSI.0, txf::SRC_VSI.1), MOCK_VSI as u64);
                assert_eq!(get_bits(ctx, txf::PORT_NUM.0, txf::PORT_NUM.1), MOCK_LPORT as u64);
                assert_eq!(get_bits(ctx, txf::VMVF_TYPE.0, 2), txf::VMVF_TYPE_PF);
                assert_eq!(get_bits(ctx, txf::TSO_QNUM.0, txf::TSO_QNUM.1), q as u64);
                self.check_dma(base, qlen * 16, "Tx ring");
                assert!(q < self.vsi_queues && !self.txq.contains_key(&q));
                let teid = 0x1000 + q as u32;
                b[12..16].copy_from_slice(&teid.to_le_bytes());
                self.nodes.insert(teid, (parent, 8));
                assert!(self.nodes.values().filter(|v| v.0 == parent).count() <= 8, "too many queues under a group");
                self.txq.insert(q, MockTxq { base, qlen, head: 0, parent });
                0
            }
            opc::SET_RSS_KEY => {
                assert_eq!(d.u16_at(0), MOCK_VSI | cmd::RSS_VSI_VALID);
                assert_eq!(self.buffer(d, true).len(), cmd::RSS_KEY_BYTES);
                0
            }
            opc::SET_RSS_LUT => {
                assert_eq!(d.u16_at(0), MOCK_VSI | cmd::RSS_VSI_VALID);
                assert_eq!(d.u16_at(cmd::RSS_LUT_FLAGS), cmd::RSS_LUT_TYPE_PF | cmd::RSS_LUT_SIZE_2K);
                self.rss_lut = self.buffer(d, true).to_vec();
                0
            }
            opc::ADD_SW_RULES => {
                assert_eq!(d.u16_at(cmd::SW_RULES_NUM), 1);
                let b = self.buffer(d, true);
                assert_eq!(u16::from_le_bytes([b[0], b[1]]), 0, "Rx lookup rule");
                if self.reject_mac_rules && u16::from_le_bytes([b[4], b[5]]) == 1 {
                    return 14;
                }
                assert_eq!(u16::from_le_bytes([b[14], b[15]]), 16);
                let rule = MockRule {
                    recipe: u16::from_le_bytes([b[4], b[5]]),
                    src: u16::from_le_bytes([b[6], b[7]]),
                    act: u32::from_le_bytes(b[8..12].try_into().unwrap()),
                    da: b[16..22].try_into().unwrap(),
                };
                b[12..14].copy_from_slice(&(self.rules.len() as u16).to_le_bytes());
                self.rules.push(rule);
                0
            }
            opc::GET_LINK_STATUS => {
                assert_eq!(d.u8_at(cmd::LINK_LPORT), MOCK_LPORT);
                let b = self.buffer(d, false);
                b[cmd::LINK_INFO] = self.link_up as u8;
                b[cmd::LINK_SPEED..cmd::LINK_SPEED + 2].copy_from_slice(&0x400u16.to_le_bytes());
                b[cmd::LINK_MAX_FRAME..cmd::LINK_MAX_FRAME + 2].copy_from_slice(&9728u16.to_le_bytes());
                0
            }
            opc::RESTART_AN => {
                assert_eq!(d.u8_at(cmd::RESTART_AN_FLAGS), cmd::RESTART_AN_RESTART | cmd::RESTART_AN_ENABLE);
                self.link_up = true;
                0
            }
            _ => 14,
        }
    }

    fn enable_rxq(&mut self, q: usize) {
        let mut ctx = [0u8; 32];
        for i in 0..8 {
            ctx[4 * i..4 * i + 4].copy_from_slice(&self.reg(qrx_context(i, q)).to_le_bytes());
        }
        let base = get_bits(&ctx, rxf::BASE.0, rxf::BASE.1) << 7;
        let qlen = get_bits(&ctx, rxf::QLEN.0, rxf::QLEN.1) as usize;
        let buf_len = (get_bits(&ctx, rxf::DBUF.0, rxf::DBUF.1) << 7) as usize;
        assert_eq!(get_bits(&ctx, rxf::DSIZE.0, 1), 1, "32-byte descriptors");
        assert_eq!(get_bits(&ctx, rxf::CRCSTRIP.0, 1), 1);
        assert_eq!(self.reg(qrxflxp_cntxt(q)) & QRXFLXP_CNTXT_RXDID_IDX_M, RXDID_FLEX_NIC);
        self.check_dma(base, qlen * 32, "Rx ring");
        let tail = self.rxq.get(&q).map_or(0, |r| r.tail);
        self.rxq.insert(q, MockRxq { base, qlen, buf_len, head: 0, tail, enabled: true, dropped: 0 });
    }

    /// The Rx queue the switch picks for a frame to `da`.
    fn rx_target(&self, da: [u8; 6]) -> Option<usize> {
        for r in &self.rules {
            if r.recipe == 1 && r.da == da {
                return Some(if r.act & 0x3 == 1 { ((r.act >> 4) & 0x7FF) as usize } else { self.rss_lut.first().copied().unwrap_or(0) as usize });
            }
        }
        self.rules.iter().any(|r| r.recipe == 5).then(|| self.rss_lut.first().copied().unwrap_or(0) as usize)
    }

    fn receive(&mut self, frame: &[u8]) {
        let Some(q) = self.rx_target(frame[0..6].try_into().unwrap()) else { return };
        let Some(r) = self.rxq.get(&q).cloned() else { return };
        if !r.enabled || r.head == r.tail {
            self.rxq.get_mut(&q).unwrap().dropped += 1;
            return;
        }
        let daddr = r.base + (r.head * 32) as u64;
        let d: RxDesc = rd(daddr);
        assert_eq!(RxDesc::status0(d.qw[1]) & RX_STATUS0_DD, 0, "Rx descriptor handed to the device with DD set");
        self.check_dma(d.qw[0], r.buf_len, "Rx buffer");
        assert!(frame.len() <= r.buf_len);
        unsafe { std::ptr::copy_nonoverlapping(frame.as_ptr(), d.qw[0] as *mut u8, frame.len()) };
        wr(daddr, RxDesc::writeback(frame.len() as u16, RX_STATUS0_DD | RX_STATUS0_EOF, 0));
        self.rxq.get_mut(&q).unwrap().head = (r.head + 1) % r.qlen;
    }

    fn transmit(&mut self, q: usize, tail: usize) {
        let t = self.txq.get(&q).cloned().expect("doorbell of a queue that was not added");
        assert!(tail < t.qlen);
        let mut head = t.head;
        while head != tail {
            let daddr = t.base + (head * 16) as u64;
            let d: TxDesc = rd(daddr);
            let len = TxDesc::buf_len(d.cmd_type_offset_bsz) as usize;
            assert!(!TxDesc::is_done(d.cmd_type_offset_bsz), "stale descriptor handed to the device");
            self.check_dma(d.buf_addr, len, "Tx buffer");
            let frame = unsafe { std::slice::from_raw_parts(d.buf_addr as *const u8, len) }.to_vec();
            if TxDesc::cmd(d.cmd_type_offset_bsz) & TX_CMD_RS != 0 {
                wr(daddr + 8, d.cmd_type_offset_bsz | TX_DTYPE_DESC_DONE);
            }
            if self.link_up {
                self.receive(&frame);
            }
            head = (head + 1) % t.qlen;
        }
        self.txq.get_mut(&q).unwrap().head = head;
    }
}

impl Platform for Mock {
    fn read32(&self, offset: usize) -> u32 {
        self.state.lock().unwrap().reg(offset)
    }

    fn write32(&self, offset: usize, value: u32) {
        let mut s = self.state.lock().unwrap();
        match offset {
            PFGEN_CTRL if value & PFGEN_CTRL_PFSWR != 0 => s.pf_reset(),
            PF_FW_ATQH => {
                s.atq_head = value as usize;
                s.regs.insert(offset, value);
            }
            PF_FW_ATQT => {
                s.regs.insert(offset, value);
                if s.reg(PF_FW_ATQLEN) & PF_FW_QLEN_ENABLE != 0 {
                    s.process_atq(value as usize);
                }
            }
            o if (0x0012_0000..0x0012_2000).contains(&o) => {
                let q = (o - 0x0012_0000) / 4;
                let mut v = value & !QRX_CTRL_QENA_STAT;
                if value & QRX_CTRL_QENA_REQ != 0 {
                    s.enable_rxq(q);
                    v |= QRX_CTRL_QENA_STAT;
                }
                s.regs.insert(o, v);
            }
            o if (0x0029_0000..0x0029_2000).contains(&o) => {
                let q = (o - 0x0029_0000) / 4;
                // The device ignores the low 3 bits of the Rx tail.
                let tail = (value & !7) as usize;
                s.rxq.entry(q).or_default().tail = tail;
                s.regs.insert(o, value);
            }
            o if (0x002C_0000..0x002C_8000).contains(&o) => s.transmit((o - 0x002C_0000) / 4, value as usize),
            _ => {
                s.regs.insert(offset, value);
            }
        }
    }

    fn dma_alloc(&self, len: usize, align: usize) -> Option<DmaRegion> {
        assert!(len <= 2 << 20, "a DMA region above 2 MiB");
        let layout = std::alloc::Layout::from_size_align(len, align.max(128)).unwrap();
        let va = unsafe { std::alloc::alloc_zeroed(layout) };
        self.state.lock().unwrap().allocations.push((va as u64, len));
        Some(DmaRegion { va, iova: va as u64, len })
    }

    fn delay_us(&self, us: u64) {
        self.clock.fetch_add(us * 1000, Ordering::Relaxed);
    }

    fn tsc(&self) -> u64 {
        self.clock.fetch_add(100, Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bench::{run_queue_pair, TxFrame};
    use crate::packet::{steering_mac, UdpFrame};
    use crate::{Config, Device, RxSteering};

    fn frame(dst: [u8; 6], q: usize) -> UdpFrame {
        UdpFrame {
            dst_mac: dst,
            src_mac: MOCK_MAC,
            src_ip: [10, 0, 0, 1],
            dst_ip: [10, 0, 1, q as u8],
            src_port: 1024 + q as u16,
            dst_port: 5001,
            len: 60,
        }
    }

    #[test]
    fn bring_up_sequence() {
        let m = Mock::new(false);
        let cfg = Config { queues: 12, tx_ring: 256, rx_ring: 128, ..Default::default() };
        let mut dev = Device::new(&m, cfg).unwrap();
        assert_eq!(dev.info.mac, MOCK_MAC);
        assert_eq!(dev.info.lport, MOCK_LPORT);
        assert_eq!(dev.info.sw_id, 3);
        assert_eq!(dev.info.vsi_num, MOCK_VSI);
        assert_eq!(dev.info.sched_layers, 9);
        assert_eq!(dev.info.queue_teids.len(), 12);
        assert_eq!(dev.info.qgroup_teids.len(), 2);
        {
            let s = m.state.lock().unwrap();
            assert_eq!(s.resets, 1);
            assert_eq!(&s.log[..3], &[opc::GET_VER, opc::CLEAR_PF_CFG, opc::CLEAR_PXE_MODE]);
            assert_eq!(s.deleted, [0x18, 0x17, 0x16, 0x15]);
            // Chain under the layer 4 node: layers 5 and 6, then two queue groups at layer 7.
            assert_eq!(s.nodes.values().filter(|n| n.1 == 7).count(), 2);
            assert_eq!(s.txq.len(), 12);
            assert!(s.txq.values().filter(|t| t.parent == dev.info.qgroup_teids[1]).count() == 6);
            assert_eq!(s.rxq.len(), 12);
            assert!(s.rxq.values().all(|r| r.enabled && r.tail == 120 && r.qlen == 128));
            assert_eq!(s.rules.len(), 13);
            assert_eq!(s.rules[0].act, (7 << 4) | (1 << 17));
            assert_eq!(s.rules[5].da, steering_mac(MOCK_MAC, 4));
            assert_eq!(s.rules[5].act, 1 | (4 << 4));
            assert_eq!(s.rss_lut.len(), 2048);
            assert_eq!(s.rss_lut[13], 1);
        }
        assert!(!dev.link_status().unwrap().up);
        let link = dev.bring_link_up(1000).unwrap();
        assert_eq!(link, crate::LinkStatus { up: true, speed_mbps: 100_000, max_frame: 9728 });
    }

    #[test]
    fn steered_loopback_through_every_queue() {
        let m = Mock::new(true);
        let n = 4;
        let cfg = Config { queues: n, tx_ring: 128, rx_ring: 512, tx_batch: 32, ..Default::default() };
        let mut dev = Device::new(&m, cfg).unwrap();
        let mut queues = dev.take_queues();
        // Queue q sends to queue (q + 1) % n of the same port.
        let frames: Vec<TxFrame> = (0..n).map(|q| TxFrame::new(&m, &frame(steering_mac(MOCK_MAC, (q + 1) % n), q)).unwrap()).collect();
        let mut sent = vec![0u64; n];
        let mut received = vec![0u64; n];
        for _round in 0..20 {
            for q in 0..n {
                let (tx, rx) = &mut queues[q];
                let r = run_queue_pair(&m, tx, rx, Some(&frames[q]), true, 5_000);
                sent[q] += r.tx_packets;
                received[q] += r.rx.packets;
                assert_eq!(r.rx.errors, 0);
            }
        }
        // Drain what arrived after each queue's last poll.
        for q in 0..n {
            let (tx, rx) = &mut queues[q];
            tx.clean();
            while rx.poll(1024) > 0 {}
            received[q] = rx.counts.packets;
            sent[q] = tx.completed;
        }
        let s = m.state.lock().unwrap();
        for q in 0..n {
            let from = (q + n - 1) % n;
            let dropped = s.rxq[&q].dropped;
            assert!(sent[from] > 1000, "queue {} sent only {}", from, sent[from]);
            // Every frame is either received or dropped for want of descriptors; completions lag by < one batch ring.
            let queued = s.txq[&from].head as u64;
            assert!(received[q] + dropped >= sent[from], "q {}: rx {} + dropped {} < sent {} ({})", q, received[q], dropped, sent[from], queued);
            assert_eq!(rx_bytes_per_frame(&queues[q].1), 60);
        }
    }

    fn rx_bytes_per_frame(rx: &crate::RxQueue<'_, Mock>) -> u64 {
        rx.counts.bytes / rx.counts.packets.max(1)
    }

    #[test]
    fn promiscuous_lands_in_queue_zero() {
        let m = Mock::new(true);
        let cfg = Config { queues: 3, tx_ring: 64, rx_ring: 64, tx_batch: 16, steering: RxSteering::Promiscuous, ..Default::default() };
        let mut dev = Device::new(&m, cfg).unwrap();
        assert_eq!(m.state.lock().unwrap().rules, [MockRule { recipe: 5, src: 1, act: (7 << 4) | (1 << 17), da: [2, 0, 0, 0, 0, 0] }]);
        let mut queues = dev.take_queues();
        let f = TxFrame::new(&m, &frame([0xff; 6], 2)).unwrap();
        let sent = queues[2].0.send_batches(f.buf.iova, f.len, 1);
        assert_eq!(sent, 16);
        let (len, status, data) = queues[0].1.peek(0);
        assert_eq!((len, status & 3), (60, 3));
        assert_eq!(&data[0..6], &[0xff; 6]);
        assert_eq!(queues[0].1.poll(64), 16);
        assert_eq!(queues[1].1.poll(64), 0);
        assert_eq!(queues[2].0.clean(), 16);
        dev.shutdown().unwrap();
        assert_eq!(m.state.lock().unwrap().resets, 2);
    }

    #[test]
    fn retries_and_steering_fallback() {
        let m = Mock::new(true);
        m.state.lock().unwrap().get_ver_failures = 2;
        m.state.lock().unwrap().reject_mac_rules = true;
        let dev = Device::new(&m, Config { queues: 2, ..Default::default() }).unwrap();
        let s = m.state.lock().unwrap();
        assert_eq!(&s.log[..3], &[opc::GET_VER; 3]);
        assert_eq!(s.rules.len(), 1);
        assert_eq!(s.rules[0].recipe, 5);
        assert_eq!(dev.info.vsi_num, MOCK_VSI);
    }

    #[test]
    fn tx_ring_never_overruns() {
        let m = Mock::new(false);
        let cfg = Config { queues: 1, tx_ring: 64, rx_ring: 32, tx_batch: 16, ..Default::default() };
        let mut dev = Device::new(&m, cfg).unwrap();
        let mut q = dev.take_queues();
        let tx = &mut q[0].0;
        let f = TxFrame::new(&m, &frame([0xff; 6], 0)).unwrap();
        // Three batches fit (one stays empty); the device completes them all at once.
        assert_eq!(tx.send_batches(f.buf.iova, f.len, 10), 48);
        assert_eq!(tx.send_batches(f.buf.iova, f.len, 10), 0);
        assert_eq!(tx.clean(), 48);
        assert_eq!(tx.send_batches(f.buf.iova, f.len, 10), 48);
        assert_eq!(tx.in_flight(), 48);
    }
}
