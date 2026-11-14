//! A software model of the parts of an E810 PF the driver uses, for host tests and (feature `mock`) for dom0 runs
//! without the device: registers, the admin queue with canned firmware answers, the Tx scheduler tree, Tx queues that
//! loop every frame back to the Rx queue the switch rules pick. It checks what it can: that every DMA address the
//! driver hands over lies in memory the driver allocated, that contexts carry what the driver configured, that the
//! scheduler tree stays consistent. It encodes the same reading of the datasheet as the driver, so it catches plumbing
//! errors, not misreadings of the hardware. The model reads and writes DMA memory at its IOVA, so it runs in the
//! address space of a driver whose IOVAs equal its VAs.
//!
//! Locks: the control path (admin queue, contexts, registers) runs under `state`; each queue's Tx and Rx sides have
//! their own locks, so queue pairs driven from different CPUs do not contend. Order: `state`, then a Tx side, then
//! an Rx side; the steering table and the allocation list are leaves.

use crate::aq::{cmd, flags, opc, AqDesc};
use crate::ctx::{get_bits, rx as rxf, tx as txf};
use crate::desc::{RxDesc, TxDesc, RXDID_FLEX_NIC, RX_STATUS0_DD, RX_STATUS0_EOF, TX_CMD_RS, TX_DTYPE_DESC_DONE};
use crate::regs::*;
use crate::sched::{self, canned, ELEM_DATA_BYTES, GRP_HDR_BYTES};
use crate::{DmaRegion, Platform};
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

pub const MOCK_MAC: [u8; 6] = [0x00, 0x1b, 0x21, 0xaa, 0xbb, 0xcc];
pub const MOCK_LPORT: u8 = 1;
pub const MOCK_VSI: u16 = 7;
/// Queue pairs the model offers (its function capabilities).
pub const MOCK_QUEUES: usize = 64;

/// A spin lock, for the model's state in `no_std`.
pub struct Spin<T> {
    locked: AtomicBool,
    value: UnsafeCell<T>,
}

unsafe impl<T: Send> Sync for Spin<T> {}
unsafe impl<T: Send> Send for Spin<T> {}

pub struct SpinGuard<'a, T> {
    lock: &'a Spin<T>,
}

impl<T> Spin<T> {
    pub const fn new(value: T) -> Spin<T> {
        Spin { locked: AtomicBool::new(false), value: UnsafeCell::new(value) }
    }

    pub fn lock(&self) -> SpinGuard<'_, T> {
        while self.locked.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
            while self.locked.load(Ordering::Relaxed) {
                core::hint::spin_loop();
            }
        }
        SpinGuard { lock: self }
    }
}

impl<T> Deref for SpinGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.value.get() }
    }
}

impl<T> DerefMut for SpinGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.value.get() }
    }
}

impl<T> Drop for SpinGuard<'_, T> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}

#[derive(Default, Debug, Clone)]
pub struct MockTxq {
    pub base: u64,
    pub qlen: usize,
    pub head: usize,
    pub parent: u32,
    /// The last destination this queue sent to, the steering generation it was looked up in, and its Rx queue.
    route: Option<([u8; 6], u64, Option<usize>)>,
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

/// The control path's state.
#[derive(Default)]
pub struct State {
    pub regs: BTreeMap<usize, u32>,
    pub log: Vec<u16>,
    atq_head: usize,
    /// Scheduler nodes: TEID -> (parent, layer).
    pub nodes: BTreeMap<u32, (u32, usize)>,
    next_teid: u32,
    pub deleted: Vec<u32>,
    pub vsi_queues: usize,
    pub rules: Vec<MockRule>,
    pub rss_lut: Vec<u8>,
    pub resets: usize,
    /// Fault injection: Get Version answers EAGAIN this many more times; MAC rules are refused.
    pub get_ver_failures: usize,
    pub reject_mac_rules: bool,
}

/// What the data path needs of the switch: the rules and the first lookup table entry.
#[derive(Default)]
struct Steering {
    rules: Vec<MockRule>,
    lut0: usize,
}

impl Steering {
    /// The Rx queue the switch picks for a frame to `da`.
    fn target(&self, da: [u8; 6]) -> Option<usize> {
        for r in &self.rules {
            if r.recipe == 1 && r.da == da {
                return Some(if r.act & 0x3 == 1 { ((r.act >> 4) & 0x7FF) as usize } else { self.lut0 });
            }
        }
        self.rules.iter().any(|r| r.recipe == 5).then_some(self.lut0)
    }
}

/// One queue pair's data path, on cache lines of its own.
#[repr(align(128))]
struct QueuePath {
    tx: Spin<Option<MockTxq>>,
    rx: Spin<Option<MockRxq>>,
}

pub struct Mock {
    pub state: Spin<State>,
    queues: Box<[QueuePath]>,
    steering: Spin<Steering>,
    /// Bumped whenever `steering` changes.
    steering_gen: AtomicU64,
    allocations: Spin<Vec<(u64, usize)>>,
    link_up: AtomicBool,
    /// Whether the data path checks every buffer address against the allocations (a linear search under one lock):
    /// on in tests, off for timing runs.
    check_buffers: bool,
    clock: AtomicU64,
}

fn rd<T: Copy>(addr: u64) -> T {
    unsafe { core::ptr::read_volatile(addr as *const T) }
}

fn wr<T: Copy>(addr: u64, v: T) {
    unsafe { core::ptr::write_volatile(addr as *mut T, v) }
}

impl Mock {
    pub fn new(link_up_at_start: bool) -> Mock {
        let mut s = State { next_teid: 0x100, ..Default::default() };
        s.regs.insert(GLNVM_ULD, GLNVM_ULD_RESET_DONE);
        let queues = (0..MOCK_QUEUES).map(|_| QueuePath { tx: Spin::new(None), rx: Spin::new(None) }).collect();
        Mock {
            state: Spin::new(s),
            queues,
            steering: Spin::new(Steering::default()),
            steering_gen: AtomicU64::new(0),
            allocations: Spin::new(Vec::new()),
            link_up: AtomicBool::new(link_up_at_start),
            check_buffers: true,
            clock: AtomicU64::new(0),
        }
    }

    /// A model whose data path skips the buffer address checks, for timing runs (the rings and the control path are
    /// still checked).
    pub fn new_unchecked(link_up_at_start: bool) -> Mock {
        Mock { check_buffers: false, ..Mock::new(link_up_at_start) }
    }

    /// Records DMA memory that a front end allocated itself, which the model then accepts in descriptors.
    pub fn note_dma(&self, region: &DmaRegion) {
        self.allocations.lock().push((region.iova, region.len));
    }

    /// A snapshot of the Tx and Rx queues the driver set up, by queue index.
    pub fn txqs(&self) -> BTreeMap<usize, MockTxq> {
        self.queues.iter().enumerate().filter_map(|(q, p)| p.tx.lock().clone().map(|t| (q, t))).collect()
    }

    pub fn rxqs(&self) -> BTreeMap<usize, MockRxq> {
        self.queues.iter().enumerate().filter_map(|(q, p)| p.rx.lock().clone().map(|r| (q, r))).collect()
    }

    /// Panics unless `[addr, addr + len)` lies in one DMA allocation.
    fn check_dma(&self, addr: u64, len: usize, what: &str) {
        assert!(
            self.allocations.lock().iter().any(|&(a, l)| addr >= a && addr + len as u64 <= a + l as u64),
            "device access to {:#x}+{} ({}) outside DMA memory",
            addr,
            len,
            what
        );
    }

    fn publish_steering(&self, s: &State) {
        *self.steering.lock() = Steering { rules: s.rules.clone(), lut0: s.rss_lut.first().copied().unwrap_or(0) as usize };
        self.steering_gen.fetch_add(1, Ordering::Release);
    }

    fn pf_reset(&self, s: &mut State) {
        s.resets += 1;
        let uld = s.reg(GLNVM_ULD);
        s.regs.clear();
        s.regs.insert(GLNVM_ULD, uld);
        s.atq_head = 0;
        s.nodes.clear();
        s.rules.clear();
        for p in self.queues.iter() {
            *p.tx.lock() = None;
            *p.rx.lock() = None;
        }
        self.publish_steering(s);
    }

    fn process_atq(&self, s: &mut State, tail: usize) {
        let base = (s.reg(PF_FW_ATQBAH) as u64) << 32 | s.reg(PF_FW_ATQBAL) as u64;
        let len = (s.reg(PF_FW_ATQLEN) & PF_FW_QLEN_M) as usize;
        assert!(s.reg(PF_FW_ATQLEN) & PF_FW_QLEN_ENABLE != 0, "ATQ not enabled");
        self.check_dma(base, len * 32, "ATQ ring");
        while s.atq_head != tail {
            let addr = base + (s.atq_head * 32) as u64;
            let mut d: AqDesc = rd(addr);
            let retval = self.command(s, &mut d);
            d.flags |= flags::DD | flags::CMP;
            if retval != 0 {
                d.flags |= flags::ERR;
            }
            d.retval = retval;
            wr(addr, d);
            s.atq_head = (s.atq_head + 1) % len;
        }
        s.regs.insert(PF_FW_ATQH, s.atq_head as u32);
    }

    /// The command's buffer, after checking the descriptor's buffer flags.
    fn buffer(&self, d: &AqDesc, to_fw: bool) -> &'static mut [u8] {
        assert!(d.flags & flags::BUF != 0, "opcode {:#x} needs a buffer", d.opcode);
        assert_eq!(d.flags & flags::RD != 0, to_fw, "opcode {:#x}: RD flag", d.opcode);
        assert_eq!(d.flags & flags::LB != 0, d.datalen as usize > 512, "opcode {:#x}: LB flag", d.opcode);
        let iova = d.buffer_iova();
        self.check_dma(iova, d.datalen as usize, "admin buffer");
        unsafe { core::slice::from_raw_parts_mut(iova as *mut u8, d.datalen as usize) }
    }

    fn command(&self, s: &mut State, d: &mut AqDesc) -> u16 {
        s.log.push(d.opcode);
        match d.opcode {
            opc::GET_VER if s.get_ver_failures > 0 => {
                s.get_ver_failures -= 1;
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
                let q = MOCK_QUEUES as u32;
                let caps = [(cmd::CAP_RXQS, q, 0u32), (cmd::CAP_TXQS, q, 0), (cmd::CAP_RSS, 2048, 8), (cmd::CAP_VSI, 768, 0)];
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
                b.copy_from_slice(&canned::resources_buf(9, [1, 1, 8, 8, 8, 8, 8, 8, 8]));
                0
            }
            opc::GET_DFLT_TOPO => {
                assert_eq!(d.u8_at(cmd::TOPO_PORT), MOCK_LPORT);
                let b = self.buffer(d, false);
                let topo = canned::default_topology_buf();
                b.copy_from_slice(&topo[..b.len()]);
                for j in 0..9 {
                    let e = GRP_HDR_BYTES + j * ELEM_DATA_BYTES;
                    let parent = u32::from_le_bytes(topo[e..e + 4].try_into().unwrap());
                    let teid = u32::from_le_bytes(topo[e + 4..e + 8].try_into().unwrap());
                    s.nodes.insert(teid, (parent, j));
                }
                d.set_u8(cmd::TOPO_NUM_BRANCHES, 1);
                0
            }
            opc::DELETE_SCHED_ELEMS => {
                let b = self.buffer(d, true);
                let parent = u32::from_le_bytes(b[0..4].try_into().unwrap());
                let teid = u32::from_le_bytes(b[8..12].try_into().unwrap());
                assert_eq!(s.nodes.get(&teid).map(|n| n.0), Some(parent), "delete: wrong parent");
                assert!(!s.nodes.values().any(|n| n.0 == teid), "delete of a node with children");
                s.nodes.remove(&teid);
                s.deleted.push(teid);
                0
            }
            opc::ADD_SCHED_ELEMS => {
                assert_eq!(d.u16_at(cmd::SCHED_NUM_REQ), 1);
                let b = self.buffer(d, true);
                let parent = u32::from_le_bytes(b[0..4].try_into().unwrap());
                let n = u16::from_le_bytes([b[4], b[5]]) as usize;
                let (_, layer) = *s.nodes.get(&parent).expect("add: unknown parent");
                assert!(layer + 1 <= 7, "add: generic node below the queue group layer");
                for i in 0..n {
                    let e = GRP_HDR_BYTES + i * ELEM_DATA_BYTES;
                    assert_eq!(u32::from_le_bytes(b[e..e + 4].try_into().unwrap()), parent);
                    assert_eq!(&b[e + 8..e + 24], &sched::default_elem_info(sched::ELEM_TYPE_SE_GENERIC));
                    let teid = s.next_teid;
                    s.next_teid += 1;
                    b[e + 4..e + 8].copy_from_slice(&teid.to_le_bytes());
                    s.nodes.insert(teid, (parent, layer + 1));
                }
                assert!(s.nodes.values().filter(|v| v.0 == parent).count() <= 8, "too many children");
                d.set_u16(cmd::SCHED_NUM_RESP, 1);
                0
            }
            opc::ADD_VSI => {
                let b = self.buffer(d, true);
                assert_eq!(b.len(), 128);
                assert_eq!(d.u16_at(cmd::VSI_FLAGS), cmd::VSI_TYPE_PF);
                assert_eq!(b[2], 3, "switch ID");
                s.vsi_queues = u16::from_le_bytes([b[32], b[33]]) as usize;
                d.set_u16(0, MOCK_VSI);
                0
            }
            opc::ADD_TXQS => {
                assert_eq!(d.u8_at(cmd::TXQS_NUM_QGRPS), 1);
                let b = self.buffer(d, true);
                let parent = u32::from_le_bytes(b[0..4].try_into().unwrap());
                assert_eq!(s.nodes.get(&parent).map(|n| n.1), Some(7), "queue parent not a queue group node");
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
                let mut txq = self.queues[q].tx.lock();
                assert!(q < s.vsi_queues && txq.is_none());
                let teid = 0x1000 + q as u32;
                b[12..16].copy_from_slice(&teid.to_le_bytes());
                s.nodes.insert(teid, (parent, 8));
                assert!(s.nodes.values().filter(|v| v.0 == parent).count() <= 8, "too many queues under a group");
                *txq = Some(MockTxq { base, qlen, head: 0, parent, route: None });
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
                s.rss_lut = self.buffer(d, true).to_vec();
                self.publish_steering(s);
                0
            }
            opc::ADD_SW_RULES => {
                assert_eq!(d.u16_at(cmd::SW_RULES_NUM), 1);
                let b = self.buffer(d, true);
                assert_eq!(u16::from_le_bytes([b[0], b[1]]), 0, "Rx lookup rule");
                if s.reject_mac_rules && u16::from_le_bytes([b[4], b[5]]) == 1 {
                    return 14;
                }
                assert_eq!(u16::from_le_bytes([b[14], b[15]]), 16);
                let rule = MockRule {
                    recipe: u16::from_le_bytes([b[4], b[5]]),
                    src: u16::from_le_bytes([b[6], b[7]]),
                    act: u32::from_le_bytes(b[8..12].try_into().unwrap()),
                    da: b[16..22].try_into().unwrap(),
                };
                b[12..14].copy_from_slice(&(s.rules.len() as u16).to_le_bytes());
                s.rules.push(rule);
                self.publish_steering(s);
                0
            }
            opc::GET_LINK_STATUS => {
                assert_eq!(d.u8_at(cmd::LINK_LPORT), MOCK_LPORT);
                let b = self.buffer(d, false);
                b[cmd::LINK_INFO] = self.link_up.load(Ordering::SeqCst) as u8;
                b[cmd::LINK_SPEED..cmd::LINK_SPEED + 2].copy_from_slice(&0x400u16.to_le_bytes());
                b[cmd::LINK_MAX_FRAME..cmd::LINK_MAX_FRAME + 2].copy_from_slice(&9728u16.to_le_bytes());
                0
            }
            opc::RESTART_AN => {
                assert_eq!(d.u8_at(cmd::RESTART_AN_FLAGS), cmd::RESTART_AN_RESTART | cmd::RESTART_AN_ENABLE);
                self.link_up.store(true, Ordering::SeqCst);
                0
            }
            _ => 14,
        }
    }

    fn enable_rxq(&self, s: &State, q: usize) {
        let mut ctx = [0u8; 32];
        for i in 0..8 {
            ctx[4 * i..4 * i + 4].copy_from_slice(&s.reg(qrx_context(i, q)).to_le_bytes());
        }
        let base = get_bits(&ctx, rxf::BASE.0, rxf::BASE.1) << 7;
        let qlen = get_bits(&ctx, rxf::QLEN.0, rxf::QLEN.1) as usize;
        let buf_len = (get_bits(&ctx, rxf::DBUF.0, rxf::DBUF.1) << 7) as usize;
        assert_eq!(get_bits(&ctx, rxf::DSIZE.0, 1), 1, "32-byte descriptors");
        assert_eq!(get_bits(&ctx, rxf::CRCSTRIP.0, 1), 1);
        assert_eq!(s.reg(qrxflxp_cntxt(q)) & QRXFLXP_CNTXT_RXDID_IDX_M, RXDID_FLEX_NIC);
        self.check_dma(base, qlen * 32, "Rx ring");
        let mut rxq = self.queues[q].rx.lock();
        let tail = rxq.as_ref().map_or(0, |r| r.tail);
        *rxq = Some(MockRxq { base, qlen, buf_len, head: 0, tail, enabled: true, dropped: 0 });
    }

    /// Delivers `len` bytes at `frame` to Rx queue `q`, or drops them for want of a descriptor.
    fn receive(&self, q: usize, frame: u64, len: usize) {
        let Some(path) = self.queues.get(q) else { return };
        let mut guard = path.rx.lock();
        let Some(r) = guard.as_mut() else { return };
        if !r.enabled || r.head == r.tail {
            r.dropped += 1;
            return;
        }
        let daddr = r.base + (r.head * 32) as u64;
        let d: RxDesc = rd(daddr);
        assert_eq!(RxDesc::status0(d.qw[1]) & RX_STATUS0_DD, 0, "Rx descriptor handed to the device with DD set");
        if self.check_buffers {
            self.check_dma(d.qw[0], r.buf_len, "Rx buffer");
        }
        assert!(len <= r.buf_len);
        unsafe { core::ptr::copy_nonoverlapping(frame as *const u8, d.qw[0] as *mut u8, len) };
        wr(daddr, RxDesc::writeback(len as u16, RX_STATUS0_DD | RX_STATUS0_EOF, 0));
        r.head = (r.head + 1) % r.qlen;
    }

    fn transmit(&self, q: usize, tail: usize) {
        let mut guard = self.queues[q].tx.lock();
        let t = guard.as_mut().expect("doorbell of a queue that was not added");
        assert!(tail < t.qlen);
        let link_up = self.link_up.load(Ordering::Relaxed);
        while t.head != tail {
            let daddr = t.base + (t.head * 16) as u64;
            let d: TxDesc = rd(daddr);
            let len = TxDesc::buf_len(d.cmd_type_offset_bsz) as usize;
            assert!(!TxDesc::is_done(d.cmd_type_offset_bsz), "stale descriptor handed to the device");
            if self.check_buffers {
                self.check_dma(d.buf_addr, len, "Tx buffer");
            }
            if link_up {
                let da: [u8; 6] = rd(d.buf_addr);
                let gen = self.steering_gen.load(Ordering::Acquire);
                let target = match t.route {
                    Some((cached, g, target)) if cached == da && g == gen => target,
                    _ => {
                        let target = self.steering.lock().target(da);
                        t.route = Some((da, gen, target));
                        target
                    }
                };
                if let Some(rq) = target {
                    self.receive(rq, d.buf_addr, len);
                }
            }
            // The write-back comes after the frame left the buffer.
            if TxDesc::cmd(d.cmd_type_offset_bsz) & TX_CMD_RS != 0 {
                wr(daddr + 8, d.cmd_type_offset_bsz | TX_DTYPE_DESC_DONE);
            }
            t.head = (t.head + 1) % t.qlen;
        }
    }
}

impl State {
    fn reg(&self, off: usize) -> u32 {
        *self.regs.get(&off).unwrap_or(&0)
    }
}

impl Platform for Mock {
    fn read32(&self, offset: usize) -> u32 {
        self.state.lock().reg(offset)
    }

    fn write32(&self, offset: usize, value: u32) {
        match offset {
            // The data path: doorbells and Rx tails, under their queue's lock only.
            o if (0x002C_0000..0x002C_8000).contains(&o) => self.transmit((o - 0x002C_0000) / 4, value as usize),
            o if (0x0029_0000..0x0029_2000).contains(&o) => {
                // The device ignores the low 3 bits of the Rx tail.
                let tail = (value & !7) as usize;
                self.queues[(o - 0x0029_0000) / 4].rx.lock().get_or_insert_with(MockRxq::default).tail = tail;
            }
            _ => {
                let mut guard = self.state.lock();
                let s = &mut *guard;
                match offset {
                    PFGEN_CTRL if value & PFGEN_CTRL_PFSWR != 0 => self.pf_reset(s),
                    PF_FW_ATQH => {
                        s.atq_head = value as usize;
                        s.regs.insert(offset, value);
                    }
                    PF_FW_ATQT => {
                        s.regs.insert(offset, value);
                        if s.reg(PF_FW_ATQLEN) & PF_FW_QLEN_ENABLE != 0 {
                            self.process_atq(s, value as usize);
                        }
                    }
                    o if (0x0012_0000..0x0012_2000).contains(&o) => {
                        let q = (o - 0x0012_0000) / 4;
                        let mut v = value & !QRX_CTRL_QENA_STAT;
                        if value & QRX_CTRL_QENA_REQ != 0 {
                            self.enable_rxq(s, q);
                            v |= QRX_CTRL_QENA_STAT;
                        }
                        s.regs.insert(o, v);
                    }
                    _ => {
                        s.regs.insert(offset, value);
                    }
                }
            }
        }
    }

    fn dma_alloc(&self, len: usize, align: usize) -> Option<DmaRegion> {
        assert!(len <= 2 << 20, "a DMA region above 2 MiB");
        let layout = core::alloc::Layout::from_size_align(len, align.max(128)).unwrap();
        let va = unsafe { alloc::alloc::alloc_zeroed(layout) };
        if va.is_null() {
            return None;
        }
        let region = DmaRegion { va, iova: va as u64, len };
        self.note_dma(&region);
        Some(region)
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
            let (txq, rxq) = (m.txqs(), m.rxqs());
            let s = m.state.lock();
            assert_eq!(s.resets, 1);
            assert_eq!(&s.log[..3], &[opc::GET_VER, opc::CLEAR_PF_CFG, opc::CLEAR_PXE_MODE]);
            assert_eq!(s.deleted, [0x18, 0x17, 0x16, 0x15]);
            // Chain under the layer 4 node: layers 5 and 6, then two queue groups at layer 7.
            assert_eq!(s.nodes.values().filter(|n| n.1 == 7).count(), 2);
            assert_eq!(txq.len(), 12);
            assert!(txq.values().filter(|t| t.parent == dev.info.qgroup_teids[1]).count() == 6);
            assert_eq!(rxq.len(), 12);
            assert!(rxq.values().all(|r| r.enabled && r.tail == 120 && r.qlen == 128));
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
        let (txq, rxq) = (m.txqs(), m.rxqs());
        for q in 0..n {
            let from = (q + n - 1) % n;
            let dropped = rxq[&q].dropped;
            assert!(sent[from] > 1000, "queue {} sent only {}", from, sent[from]);
            // Every frame is either received or dropped for want of descriptors; completions lag by < one batch ring.
            let queued = txq[&from].head as u64;
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
        assert_eq!(m.state.lock().rules, [MockRule { recipe: 5, src: 1, act: (7 << 4) | (1 << 17), da: [2, 0, 0, 0, 0, 0] }]);
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
        assert_eq!(m.state.lock().resets, 2);
    }

    #[test]
    fn retries_and_steering_fallback() {
        let m = Mock::new(true);
        m.state.lock().get_ver_failures = 2;
        m.state.lock().reject_mac_rules = true;
        let dev = Device::new(&m, Config { queues: 2, ..Default::default() }).unwrap();
        let s = m.state.lock();
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

    #[test]
    fn forwarder_rewrites_and_returns_buffers() {
        use crate::bench::run_forwarder;
        use crate::maglev::{populate_lut, Maglev, CACHE_ENTRIES, TABLE_SIZE};
        let m = Mock::new(true);
        let cfg = Config { queues: 3, tx_ring: 128, rx_ring: 64, tx_batch: 16, ..Default::default() };
        let mut dev = Device::new(&m, cfg).unwrap();
        let mut q = dev.take_queues();
        let mut lut = vec![0i8; TABLE_SIZE];
        populate_lut(&mut lut);
        let mut cache = vec![[0u64; 2]; CACHE_ENTRIES];
        let mut mg = Maglev::new(&lut, &mut cache);
        let bufs: Vec<TxFrame> = (0..48u16)
            .map(|i| TxFrame::new(&m, &UdpFrame { src_port: 1000 + i, ..frame(steering_mac(MOCK_MAC, 1), 0) }).unwrap())
            .collect();
        let list: Vec<(u64, u16)> = bufs.iter().map(|f| (f.buf.iova, f.len)).collect();
        // Queue 0 sends 48 frames to queue 1; the forwarder on Tx queue 2 sends them on to queue 0's steering MAC.
        assert_eq!(q[0].0.send_frames(&list), 48);
        let (a, b) = q.split_at_mut(2);
        let (rx1, tx2) = (&mut a[1].1, &mut b[0].0);
        let r = run_forwarder(&m, tx2, &mut [rx1], &mut mg, [2, 2, 2, 2, 2, 2], steering_mac(MOCK_MAC, 0), 100_000);
        assert_eq!(r.rx.packets, 48);
        assert_eq!(r.tx_packets, 48);
        let mut seen = 0;
        q[0].1.take(64, |f| {
            assert_eq!(unsafe { core::slice::from_raw_parts(f.va.add(6), 6) }, &[2, 2, 2, 2, 2, 2]);
            seen += 1;
        });
        assert_eq!(seen, 48);
    }

    #[test]
    fn frames_sent_one_by_one_and_taken_until_given_back() {
        let m = Mock::new(true);
        let cfg = Config { queues: 2, tx_ring: 64, rx_ring: 64, tx_batch: 16, ..Default::default() };
        let mut dev = Device::new(&m, cfg).unwrap();
        let mut q = dev.take_queues();
        let bufs: Vec<TxFrame> = (0..40u8)
            .map(|i| {
                let f = TxFrame::new(&m, &frame(steering_mac(MOCK_MAC, 1), 0)).unwrap();
                unsafe { *f.buf.va.add(50) = i };
                f
            })
            .collect();
        let list: Vec<(u64, u16)> = bufs.iter().map(|f| (f.buf.iova, f.len)).collect();
        // The tail of 63 leaves the device descriptors 0..56 (it ignores the low 3 bits).
        assert_eq!(q[0].0.send_frames(&list), 40);
        assert_eq!(q[0].0.clean_frames(), 32); // only whole batches of 32 are written back
        assert_eq!(q[0].0.completed, 32);
        let mut seen = Vec::new();
        assert_eq!(q[1].1.take(10, |f| seen.push(unsafe { *f.va.add(50) })), 10);
        assert_eq!(q[1].1.take(64, |f| seen.push(unsafe { *f.va.add(50) })), 30);
        assert_eq!(seen, (0..40).collect::<Vec<u8>>());
        // The taken descriptors stay the driver's until given back: 16 of the next 20 frames fit, then none.
        assert_eq!(q[0].0.send_frames(&list[..20]), 20);
        assert_eq!(q[1].1.take(64, |_| {}), 16);
        q[0].0.send_frames(&list[..5]);
        assert_eq!(q[1].1.take(64, |_| {}), 0);
        assert_eq!(m.rxqs()[&1].dropped, 9);
        q[1].1.give_back();
        q[0].0.send_frames(&list[..5]);
        assert_eq!(q[1].1.take(64, |_| {}), 5);
        assert_eq!(q[1].1.counts.packets, 61);
        assert_eq!(m.rxqs()[&1].dropped, 9);
    }
}
