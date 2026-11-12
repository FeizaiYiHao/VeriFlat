//! Bring-up of one E810 PF with N queue pairs, following the order of the Linux driver's `ice_init_hw` and
//! `ice_vsi_setup` for a single PF VSI.

use crate::aq::{cmd, opc, AqDesc, ControlQueue, AQ_BUF};
use crate::ctx::{RxQueueContext, TxQueueContext};
use crate::desc::RXDID_FLEX_NIC;
use crate::packet::steering_mac;
use crate::queue::{RxQueue, TxQueue};
use crate::regs::*;
use crate::sched::{self, SchedResources, ELEM_DATA_BYTES, ELEM_TYPE_SE_GENERIC, GRP_HDR_BYTES};
use crate::{DmaRegion, Error, Mac, Platform, Result};
use alloc::vec;
use alloc::vec::Vec;

/// How received frames reach the queues.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RxSteering {
    /// One switch rule per queue forwards frames whose destination is `packet::steering_mac(mac, q)` to queue `q`, and
    /// one rule forwards frames to the PF's own MAC to the VSI. Needs no DDP package; the sender picks the queue.
    PerQueueMac,
    /// The default-VSI rule: every frame the port receives that no other rule takes goes to the VSI, which spreads it
    /// with RSS. Without a DDP package the device computes no hash, so everything lands in one queue.
    Promiscuous,
}

#[derive(Clone, Copy, Debug)]
pub struct Config {
    /// Queue pairs (one per worker CPU).
    pub queues: usize,
    /// Descriptors per Tx ring; a multiple of `tx_batch`, at most 8160.
    pub tx_ring: usize,
    /// Descriptors per Rx ring; a multiple of 32, at most 8160.
    pub rx_ring: usize,
    /// Tx descriptors per doorbell and per write-back.
    pub tx_batch: usize,
    /// Rx buffer size, a multiple of 128 of at least the largest frame.
    pub rx_buf: usize,
    pub steering: RxSteering,
}

impl Default for Config {
    fn default() -> Self {
        Config { queues: 1, tx_ring: 1024, rx_ring: 1024, tx_batch: 32, rx_buf: 2048, steering: RxSteering::PerQueueMac }
    }
}

/// What the bring-up learned.
#[derive(Clone, Debug, Default)]
pub struct DeviceInfo {
    pub pf_id: u8,
    pub fw: [u8; 3],
    pub fw_build: u32,
    pub api: [u8; 3],
    /// The PF's first device-wide queue index and queue counts, and the RSS table size (function capabilities).
    pub rxq_first: u32,
    pub num_rxq: u32,
    pub txq_first: u32,
    pub num_txq: u32,
    pub rss_table_size: u32,
    pub num_vsi: u32,
    pub lport: u8,
    pub sw_id: u16,
    pub mac: [u8; 6],
    pub vsi_num: u16,
    pub sched_layers: usize,
    /// TEIDs of the scheduler nodes the queues hang under, and of the queues.
    pub qgroup_teids: Vec<u32>,
    pub queue_teids: Vec<u32>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LinkStatus {
    pub up: bool,
    pub speed_mbps: u32,
    pub max_frame: u16,
}

/// Port counters (40-bit, wrapping; CRC and illegal byte errors 32-bit).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PortStats {
    pub rx_bytes: u64,
    pub rx_unicast: u64,
    pub rx_multicast: u64,
    pub rx_broadcast: u64,
    pub tx_bytes: u64,
    pub tx_unicast: u64,
    pub tx_multicast: u64,
    pub tx_broadcast: u64,
    pub crc_errors: u64,
    pub illegal_bytes: u64,
}

impl PortStats {
    /// `self - earlier`, modulo the counter widths.
    pub fn since(&self, earlier: &PortStats) -> PortStats {
        let d40 = |a: u64, b: u64| a.wrapping_sub(b) & ((1 << 40) - 1);
        let d32 = |a: u64, b: u64| a.wrapping_sub(b) & 0xffff_ffff;
        PortStats {
            rx_bytes: d40(self.rx_bytes, earlier.rx_bytes),
            rx_unicast: d40(self.rx_unicast, earlier.rx_unicast),
            rx_multicast: d40(self.rx_multicast, earlier.rx_multicast),
            rx_broadcast: d40(self.rx_broadcast, earlier.rx_broadcast),
            tx_bytes: d40(self.tx_bytes, earlier.tx_bytes),
            tx_unicast: d40(self.tx_unicast, earlier.tx_unicast),
            tx_multicast: d40(self.tx_multicast, earlier.tx_multicast),
            tx_broadcast: d40(self.tx_broadcast, earlier.tx_broadcast),
            crc_errors: d32(self.crc_errors, earlier.crc_errors),
            illegal_bytes: d32(self.illegal_bytes, earlier.illegal_bytes),
        }
    }
}

/// An initialized PF. The queue pairs leave it with `take_queues`; the device keeps the admin queue for link and
/// statistics.
pub struct Device<'p, P: Platform> {
    p: &'p P,
    aq: ControlQueue,
    pub info: DeviceInfo,
    pub config: Config,
    queues: Vec<(TxQueue<'p, P>, RxQueue<'p, P>)>,
}

/// Polls `done` every `step_us` for up to `timeout_us`.
fn poll(p: &impl Platform, timeout_us: u64, step_us: u64, what: &'static str, mut done: impl FnMut() -> bool) -> Result<()> {
    let mut waited = 0;
    while !done() {
        if waited >= timeout_us {
            return Err(Error::Timeout(what));
        }
        p.delay_us(step_us);
        waited += step_us;
    }
    Ok(())
}

/// Waits until no global reset is in progress and the device finished loading after its last one.
fn wait_reset_done(p: &impl Platform) -> Result<()> {
    poll(p, 10_000_000, 1000, "the end of a global reset", || {
        p.read32(GLGEN_RSTAT) & GLGEN_RSTAT_DEVSTATE_M == 0 && p.read32(GLNVM_ULD) & GLNVM_ULD_RESET_DONE == GLNVM_ULD_RESET_DONE
    })
}

/// PF software reset (E810 datasheet: resets, PF reset): clears the PF's queues, VSIs and control queues. As in the Linux
/// driver, a global reset in progress replaces it.
pub(crate) fn pf_reset(p: &impl Platform) -> Result<()> {
    if p.read32(GLGEN_RSTAT) & GLGEN_RSTAT_DEVSTATE_M != 0 || p.read32(GLNVM_ULD) & GLNVM_ULD_RESET_DONE != GLNVM_ULD_RESET_DONE {
        log::info!("ice: a global reset is in progress, waiting for it instead of a PF reset");
        return wait_reset_done(p);
    }
    p.write32(PFGEN_CTRL, p.read32(PFGEN_CTRL) | PFGEN_CTRL_PFSWR);
    // The Linux driver allows the global configuration lock timeout (5 s) plus 300 ms.
    poll(p, 6_000_000, 1000, "the PF reset", || p.read32(PFGEN_CTRL) & PFGEN_CTRL_PFSWR == 0)
}

fn dma(p: &impl Platform, len: usize, align: usize) -> Result<DmaRegion> {
    p.dma_alloc(len, align).ok_or(Error::NoDmaMemory)
}

fn ceil_log2(n: usize) -> u16 {
    (usize::BITS - (n.max(1) - 1).leading_zeros()) as u16
}

/// 1:1 user priority translation table: UP i -> i in bits 3i+2..3i.
const UP_TABLE_1TO1: u32 = 0x00FA_C688;

/// The VSI properties block (`ice_aqc_vsi_props`, 128 bytes) of the PF VSI with `queues` contiguous queues from PF
/// queue 0, as the Linux driver's `ice_set_dflt_vsi_ctx`, `ice_set_rss_vsi_ctx` and `ice_vsi_setup_q_map` fill it.
pub fn vsi_properties(sw_id: u16, queues: usize) -> [u8; 128] {
    let mut v = [0u8; 128];
    // Valid sections: security, Rx queue map (the add command takes the others as given).
    v[0..2].copy_from_slice(&((1u16 << 1) | (1 << 6)).to_le_bytes());
    v[2] = sw_id as u8;
    // sw_flags: source pruning, loopback allowed (VEB mode); sw_flags2: traffic may go to the LAN.
    v[3] = 0x80 | 0x20;
    v[4] = 0x10;
    // sec_flags: the PF VSI may override the destination (control frames).
    v[6] = 0x01;
    // inner_vlan_flags: accept tagged and untagged frames on Tx; show VLAN in the descriptor.
    v[12] = 0x3;
    v[16..20].copy_from_slice(&UP_TABLE_1TO1.to_le_bytes());
    v[20..24].copy_from_slice(&UP_TABLE_1TO1.to_le_bytes());
    // Contiguous queue map: first queue 0, `queues` queues; TC 0 gets all of them at offset 0.
    v[28..30].copy_from_slice(&0u16.to_le_bytes());
    v[30..32].copy_from_slice(&0u16.to_le_bytes());
    v[32..34].copy_from_slice(&(queues as u16).to_le_bytes());
    v[62..64].copy_from_slice(&(ceil_log2(queues) << 11).to_le_bytes());
    // q_opt_rss: PF lookup table, Toeplitz hash.
    v[78] = 0x2;
    v[84..88].copy_from_slice(&UP_TABLE_1TO1.to_le_bytes());
    v
}

/// Switch rule recipes and actions (`ice_sw_rule_lkup_rx_tx`).
pub mod rule {
    pub const T_LKUP_RX: u16 = 0x0;
    pub const RECIPE_MAC: u16 = 1;
    pub const RECIPE_DFLT: u16 = 5;
    pub const ACT_VSI_FORWARDING: u32 = 0;
    pub const ACT_TO_Q: u32 = 1;
    pub const ACT_VSI_ID_S: u32 = 4;
    pub const ACT_VSI_ID_M: u32 = 0x3FF0;
    pub const ACT_Q_INDEX_S: u32 = 4;
    pub const ACT_Q_INDEX_M: u32 = 0x7FF0;
    pub const ACT_VALID: u32 = 1 << 17;
    pub const BYTES: usize = 32;
    /// The dummy Ethernet header of a lookup rule: DA, SA, TPID 0x8100, TCI 0.
    pub const DUMMY_ETH: [u8; 16] = [0x02, 0, 0, 0, 0, 0, 0x02, 0, 0, 0, 0, 0, 0x81, 0x00, 0, 0];

    /// An Rx lookup rule of `recipe` from logical port `lport` with action `act`; `da` (MAC rules) goes to the header.
    pub fn rx(recipe: u16, lport: u8, act: u32, da: Option<[u8; 6]>) -> [u8; BYTES] {
        let mut r = [0u8; BYTES];
        r[0..2].copy_from_slice(&T_LKUP_RX.to_le_bytes());
        r[4..6].copy_from_slice(&recipe.to_le_bytes());
        r[6..8].copy_from_slice(&(lport as u16).to_le_bytes());
        r[8..12].copy_from_slice(&act.to_le_bytes());
        r[14..16].copy_from_slice(&(DUMMY_ETH.len() as u16).to_le_bytes());
        r[16..32].copy_from_slice(&DUMMY_ETH);
        if let Some(da) = da {
            r[16..22].copy_from_slice(&da);
        }
        r
    }

    pub fn to_vsi(vsi: u16) -> u32 {
        ACT_VSI_FORWARDING | ((vsi as u32) << ACT_VSI_ID_S & ACT_VSI_ID_M) | ACT_VALID
    }

    /// Forward to the device-wide Rx queue `q` (the Linux driver sets no valid bit on this action).
    pub fn to_queue(q: u32) -> u32 {
        ACT_TO_Q | (q << ACT_Q_INDEX_S & ACT_Q_INDEX_M)
    }
}

/// A fixed RSS key (the 40-byte Toeplitz key many drivers use by default, then 12 bytes of extended key).
const RSS_KEY: [u8; cmd::RSS_KEY_BYTES] = [
    0x6d, 0x5a, 0x56, 0xda, 0x25, 0x5b, 0x0e, 0xc2, 0x41, 0x67, 0x25, 0x3d, 0x43, 0xa3, 0x8f, 0xb0, 0xd0, 0xca, 0x2b, 0xcb, 0xae,
    0x7b, 0x30, 0xb4, 0x77, 0xcb, 0x2d, 0xa3, 0x80, 0x30, 0xf2, 0x0c, 0x6a, 0x42, 0xb7, 0x3b, 0xbe, 0xac, 0x01, 0xfa, 0x6d, 0x5a,
    0x56, 0xda, 0x25, 0x5b, 0x0e, 0xc2, 0x41, 0x67, 0x25, 0x3d,
];

impl<'p, P: Platform> Device<'p, P> {
    /// Resets the PF and brings it up with `config.queues` queue pairs. The link may still be down: see
    /// `bring_link_up`.
    pub fn new(p: &'p P, config: Config) -> Result<Self> {
        if config.queues == 0 || config.queues > 256 {
            return Err(Error::Config("1 to 256 queue pairs"));
        }
        if config.tx_ring % config.tx_batch != 0 || config.tx_ring > 8160 || config.rx_ring % 32 != 0 || config.rx_ring > 8160 {
            return Err(Error::Config("ring sizes"));
        }
        if config.rx_buf % 128 != 0 || config.rx_buf < 1536 || config.rx_buf > 16256 {
            return Err(Error::Config("Rx buffer size"));
        }
        let mut info = DeviceInfo { pf_id: (p.read32(PF_FUNC_RID) & PF_FUNC_RID_FUNC_NUM_M) as u8, ..Default::default() };
        pf_reset(p)?;
        p.write32(PFINT_OICR_ENA, 0);
        // As the Linux driver, retry the control queue bring-up for about a second while the firmware is not ready.
        let mut tries = 0;
        let mut dev = loop {
            ControlQueue::disable(p);
            let aq = ControlQueue::init(p)?;
            let mut dev = Device { p, aq, info: DeviceInfo::default(), config, queues: Vec::new() };
            match dev.get_version(&mut info) {
                Ok(()) => break dev,
                Err(e) if tries < 10 => {
                    log::warn!("ice: firmware not answering yet ({}), retrying", e);
                    tries += 1;
                    p.delay_us(100_000);
                }
                Err(e) => return Err(e),
            }
        };
        log::info!(
            "ice: PF {} firmware {}.{}.{} build {:#x}, API {}.{}.{}",
            info.pf_id, info.fw[0], info.fw[1], info.fw[2], info.fw_build, info.api[0], info.api[1], info.api[2]
        );
        dev.send(AqDesc::new(opc::CLEAR_PF_CFG), None)?;
        let mut pxe = AqDesc::new(opc::CLEAR_PXE_MODE);
        pxe.set_u8(0, cmd::CLEAR_PXE_RX_CNT);
        // The Linux driver ignores the result too.
        if let Err(e) = dev.send(pxe, None) {
            log::warn!("ice: clear PXE mode: {}", e);
        }
        dev.read_caps(&mut info)?;
        log::info!(
            "ice: queues rx {} from {}, tx {} from {}, RSS table {}, VSIs {}",
            info.num_rxq, info.rxq_first, info.num_txq, info.txq_first, info.rss_table_size, info.num_vsi
        );
        if config.queues as u32 > info.num_rxq.min(info.num_txq) {
            return Err(Error::Config("more queue pairs than the PF has"));
        }
        dev.read_switch_config(&mut info)?;
        info.mac = dev.read_mac()?;
        log::info!("ice: logical port {}, switch {}, MAC {}", info.lport, info.sw_id, Mac(info.mac));
        let (parent, res) = dev.init_scheduler(&mut info)?;
        info.vsi_num = dev.add_vsi(info.sw_id, config.queues)?;
        log::info!("ice: VSI {} with {} queue pairs", info.vsi_num, config.queues);
        dev.build_queue_tree(&mut info, parent, &res)?;
        dev.info = info;
        let mut queues = Vec::new();
        for q in 0..config.queues {
            let tx = dev.add_tx_queue(q)?;
            let rx = dev.add_rx_queue(q)?;
            queues.push((tx, rx));
        }
        dev.queues = queues;
        if let Err(e) = dev.set_rss() {
            log::warn!("ice: RSS key/LUT not set: {}", e);
        }
        dev.add_rx_rules()?;
        dev.aq.drain_events(p);
        Ok(dev)
    }

    fn send(&mut self, mut desc: AqDesc, buf: Option<&mut [u8]>) -> Result<AqDesc> {
        self.aq.send(self.p, &mut desc, buf)?;
        Ok(desc)
    }

    fn get_version(&mut self, info: &mut DeviceInfo) -> Result<()> {
        let d = self.send(AqDesc::new(opc::GET_VER), None)?;
        info.fw_build = d.u32_at(cmd::VER_FW_BUILD);
        info.fw = [d.u8_at(cmd::VER_FW_MAJOR), d.u8_at(cmd::VER_FW_MINOR), d.u8_at(cmd::VER_FW_PATCH)];
        info.api = [d.u8_at(cmd::VER_API_MAJOR), d.u8_at(cmd::VER_API_MINOR), d.u8_at(cmd::VER_API_PATCH)];
        Ok(())
    }

    fn read_caps(&mut self, info: &mut DeviceInfo) -> Result<()> {
        let mut buf = vec![0u8; AQ_BUF];
        let d = self.send(AqDesc::new(opc::LIST_FUNC_CAPS), Some(&mut buf))?;
        let count = (d.u32_at(cmd::CAPS_COUNT) as usize).min(AQ_BUF / cmd::CAPS_ELEM);
        for e in buf.chunks(cmd::CAPS_ELEM).take(count) {
            let cap = u16::from_le_bytes([e[0], e[1]]);
            let number = u32::from_le_bytes(e[4..8].try_into().unwrap());
            let phys_id = u32::from_le_bytes(e[12..16].try_into().unwrap());
            match cap {
                cmd::CAP_RXQS => (info.num_rxq, info.rxq_first) = (number, phys_id),
                cmd::CAP_TXQS => (info.num_txq, info.txq_first) = (number, phys_id),
                cmd::CAP_RSS => info.rss_table_size = number,
                cmd::CAP_VSI => info.num_vsi = number,
                _ => {}
            }
        }
        Ok(())
    }

    fn read_switch_config(&mut self, info: &mut DeviceInfo) -> Result<()> {
        let mut next = 0u16;
        let mut found = false;
        loop {
            let mut buf = vec![0u8; cmd::SW_CFG_BUF];
            let mut d = AqDesc::new(opc::GET_SW_CFG);
            d.set_u16(cmd::SW_CFG_ELEMENT, next);
            let d = self.send(d, Some(&mut buf))?;
            let n = (d.u16_at(cmd::SW_CFG_NUM_ELEMS) as usize).min(cmd::SW_CFG_BUF / cmd::SW_CFG_ELEM);
            for e in buf.chunks(cmd::SW_CFG_ELEM).take(n) {
                let port = u16::from_le_bytes([e[0], e[1]]);
                let ty = port >> cmd::SW_CFG_TYPE_S;
                if !found && (ty == cmd::SW_CFG_TYPE_PHYS_PORT || ty == cmd::SW_CFG_TYPE_VIRT_PORT) {
                    info.lport = (port & 0xff) as u8;
                    info.sw_id = u16::from_le_bytes([e[2], e[3]]);
                    found = true;
                }
            }
            next = d.u16_at(cmd::SW_CFG_ELEMENT);
            if next == 0 {
                break;
            }
        }
        if found { Ok(()) } else { Err(Error::Device("the switch configuration names no port of this PF")) }
    }

    fn read_mac(&mut self) -> Result<[u8; 6]> {
        let mut buf = [0u8; 2 * cmd::MAC_READ_ENTRY];
        let d = self.send(AqDesc::new(opc::MANAGE_MAC_READ), Some(&mut buf))?;
        if d.u16_at(cmd::MAC_READ_FLAGS) & cmd::MAC_READ_LAN_VALID == 0 {
            return Err(Error::Device("the firmware has no valid LAN MAC address"));
        }
        let n = (d.u8_at(cmd::MAC_READ_NUM_ADDR) as usize).min(2);
        buf.chunks(cmd::MAC_READ_ENTRY)
            .take(n)
            .find(|e| e[1] == 0)
            .map(|e| e[2..8].try_into().unwrap())
            .ok_or(Error::Device("no LAN MAC address in the response"))
    }

    /// Reads the scheduler's layers and the port's default tree and removes the default nodes; returns the node the
    /// driver's branch hangs under.
    fn init_scheduler(&mut self, info: &mut DeviceInfo) -> Result<(sched::Node, SchedResources)> {
        let mut buf = vec![0u8; sched::RES_BUF_BYTES];
        self.send(AqDesc::new(opc::QUERY_SCHED_RES), Some(&mut buf))?;
        let res = SchedResources::parse(&buf).ok_or(Error::Device("scheduler resources"))?;
        info.sched_layers = res.layers;
        let mut buf = vec![0u8; AQ_BUF];
        let mut d = AqDesc::new(opc::GET_DFLT_TOPO);
        d.set_u8(cmd::TOPO_PORT, info.lport);
        let d = self.send(d, Some(&mut buf))?;
        let branches = sched::parse_topology(&buf, d.u8_at(cmd::TOPO_NUM_BRANCHES) as usize)
            .ok_or(Error::Device("default scheduler topology"))?;
        let entry = sched::entry_point_layer(&branches).ok_or(Error::Device("no entry point in the default topology"))?;
        let doomed = sched::default_nodes_to_remove(&branches, entry);
        log::info!(
            "ice: scheduler {} layers, {} branches, entry point layer {}, removing {} default nodes",
            res.layers, branches.len(), entry, doomed.len()
        );
        for n in &doomed {
            let mut buf = [0u8; GRP_HDR_BYTES + 4];
            buf[0..4].copy_from_slice(&n.parent_teid.to_le_bytes());
            buf[4..6].copy_from_slice(&1u16.to_le_bytes());
            buf[8..12].copy_from_slice(&n.teid.to_le_bytes());
            let mut d = AqDesc::new(opc::DELETE_SCHED_ELEMS);
            d.flags |= crate::aq::flags::RD;
            d.set_u16(cmd::SCHED_NUM_REQ, 1);
            self.send(d, Some(&mut buf))?;
        }
        Ok((sched::chain_parent(&branches, &doomed), res))
    }

    /// Adds `count` generic nodes under `parent`; returns their TEIDs.
    fn add_sched_nodes(&mut self, parent: u32, count: usize) -> Result<Vec<u32>> {
        let mut buf = vec![0u8; GRP_HDR_BYTES + count * ELEM_DATA_BYTES];
        buf[0..4].copy_from_slice(&parent.to_le_bytes());
        buf[4..6].copy_from_slice(&(count as u16).to_le_bytes());
        for i in 0..count {
            let e = GRP_HDR_BYTES + i * ELEM_DATA_BYTES;
            buf[e..e + 4].copy_from_slice(&parent.to_le_bytes());
            buf[e + 8..e + 24].copy_from_slice(&sched::default_elem_info(ELEM_TYPE_SE_GENERIC));
        }
        let mut d = AqDesc::new(opc::ADD_SCHED_ELEMS);
        d.flags |= crate::aq::flags::RD;
        d.set_u16(cmd::SCHED_NUM_REQ, 1);
        let d = self.send(d, Some(&mut buf))?;
        if d.u16_at(cmd::SCHED_NUM_RESP) != 1 {
            return Err(Error::Device("the firmware added no scheduler node group"));
        }
        Ok((0..count)
            .map(|i| {
                let e = GRP_HDR_BYTES + i * ELEM_DATA_BYTES + 4;
                u32::from_le_bytes(buf[e..e + 4].try_into().unwrap())
            })
            .collect())
    }

    fn build_queue_tree(&mut self, info: &mut DeviceInfo, parent: sched::Node, res: &SchedResources) -> Result<()> {
        let plan = sched::plan(res, &parent, self.config.queues).map_err(Error::Device)?;
        let mut teid = parent.teid;
        for _ in plan.chain_layers.clone() {
            teid = self.add_sched_nodes(teid, 1)?[0];
        }
        info.qgroup_teids = self.add_sched_nodes(teid, plan.qgroups)?;
        log::info!(
            "ice: Tx tree under node {:#x} (layer {}): {} chain nodes, {} queue groups of up to {} queues",
            parent.teid, parent.layer, plan.chain_layers.len(), plan.qgroups, plan.per_qgroup
        );
        Ok(())
    }

    fn add_vsi(&mut self, sw_id: u16, queues: usize) -> Result<u16> {
        let mut props = vsi_properties(sw_id, queues);
        let mut d = AqDesc::new(opc::ADD_VSI);
        d.flags |= crate::aq::flags::RD;
        // vsi_num 0 without the valid bit: the firmware picks the VSI number.
        d.set_u16(cmd::VSI_FLAGS, cmd::VSI_TYPE_PF);
        let d = self.send(d, Some(&mut props))?;
        log::debug!("ice: VSIs used {} free {}", d.u16_at(cmd::VSI_USED), d.u16_at(cmd::VSI_FREE));
        Ok(d.u16_at(0) & cmd::VSI_NUM_M)
    }

    fn add_tx_queue(&mut self, q: usize) -> Result<TxQueue<'p, P>> {
        let size = self.config.tx_ring;
        let descs = dma(self.p, size * 16, 4096)?;
        let ctx = TxQueueContext {
            base: descs.iova,
            port_num: self.info.lport,
            pf_num: self.info.pf_id,
            src_vsi: self.info.vsi_num,
            qlen: size as u16,
            pf_q: q as u16,
        };
        let per_group = self.config.queues.div_ceil(self.info.qgroup_teids.len());
        let parent = self.info.qgroup_teids[q / per_group];
        // One queue group of one queue: parent TEID, count, then the queue (ID, TEID, context, element).
        let mut buf = [0u8; 56];
        buf[0..4].copy_from_slice(&parent.to_le_bytes());
        buf[4] = 1;
        buf[8..10].copy_from_slice(&(q as u16).to_le_bytes());
        buf[16..38].copy_from_slice(&ctx.pack());
        buf[40..56].copy_from_slice(&sched::default_elem_info(0));
        let mut d = AqDesc::new(opc::ADD_TXQS);
        d.flags |= crate::aq::flags::RD;
        d.set_u8(cmd::TXQS_NUM_QGRPS, 1);
        self.send(d, Some(&mut buf))?;
        self.info.queue_teids.push(u32::from_le_bytes(buf[12..16].try_into().unwrap()));
        Ok(TxQueue::new(self.p, q, descs, size, self.config.tx_batch))
    }

    fn add_rx_queue(&mut self, q: usize) -> Result<RxQueue<'p, P>> {
        let (size, buf_len) = (self.config.rx_ring, self.config.rx_buf);
        let descs = dma(self.p, size * 32, 4096)?;
        // Buffers in chunks of at most 1 MiB, each contiguous in IOVA.
        let per_chunk = ((1 << 20) / buf_len).max(1);
        let mut bufs = Vec::with_capacity(size);
        while bufs.len() < size {
            let n = per_chunk.min(size - bufs.len());
            let chunk = dma(self.p, n * buf_len, 4096)?;
            bufs.extend((0..n).map(|i| chunk.slice(i * buf_len, buf_len)));
        }
        let ctx = RxQueueContext { base: descs.iova, qlen: size as u16, buf_len: buf_len as u16, rxmax: buf_len.min(9728) as u16 };
        for (i, dw) in ctx.dwords().iter().enumerate() {
            self.p.write32(qrx_context(i, q), *dw);
        }
        let mut flx = self.p.read32(qrxflxp_cntxt(q));
        flx &= !(QRXFLXP_CNTXT_RXDID_IDX_M | QRXFLXP_CNTXT_RXDID_PRIO_M | QRXFLXP_CNTXT_TS);
        flx |= RXDID_FLEX_NIC | (3 << QRXFLXP_CNTXT_RXDID_PRIO_S);
        self.p.write32(qrxflxp_cntxt(q), flx);
        self.p.write32(qrx_tail(q), 0);
        let rxq = RxQueue::new(self.p, q, descs, bufs);
        rxq.start();
        self.p.write32(qrx_ctrl(q), self.p.read32(qrx_ctrl(q)) | QRX_CTRL_QENA_REQ);
        let p = self.p;
        poll(p, 100_000, 20, "an Rx queue to start", || p.read32(qrx_ctrl(q)) & QRX_CTRL_QENA_STAT != 0)?;
        Ok(rxq)
    }

    fn set_rss(&mut self) -> Result<()> {
        let vsi = self.info.vsi_num | cmd::RSS_VSI_VALID;
        let mut key = RSS_KEY;
        let mut d = AqDesc::new(opc::SET_RSS_KEY);
        d.flags |= crate::aq::flags::RD;
        d.set_u16(0, vsi);
        self.send(d, Some(&mut key))?;
        let mut lut: Vec<u8> = (0..cmd::RSS_LUT_PF_ENTRIES).map(|i| (i % self.config.queues) as u8).collect();
        let mut d = AqDesc::new(opc::SET_RSS_LUT);
        d.flags |= crate::aq::flags::RD;
        d.set_u16(0, vsi);
        d.set_u16(cmd::RSS_LUT_FLAGS, cmd::RSS_LUT_TYPE_PF | cmd::RSS_LUT_SIZE_2K);
        self.send(d, Some(&mut lut))?;
        Ok(())
    }

    fn add_rule(&mut self, mut r: [u8; rule::BYTES]) -> Result<u16> {
        let mut d = AqDesc::new(opc::ADD_SW_RULES);
        d.flags |= crate::aq::flags::RD;
        d.set_u16(cmd::SW_RULES_NUM, 1);
        self.send(d, Some(&mut r))?;
        Ok(u16::from_le_bytes([r[12], r[13]]))
    }

    fn add_rx_rules(&mut self) -> Result<()> {
        let (lport, vsi, mac) = (self.info.lport, self.info.vsi_num, self.info.mac);
        match self.config.steering {
            RxSteering::PerQueueMac => {
                let mut steer = || -> Result<()> {
                    self.add_rule(rule::rx(rule::RECIPE_MAC, lport, rule::to_vsi(vsi), Some(mac)))?;
                    for q in 0..self.config.queues {
                        let target = self.info.rxq_first + q as u32;
                        self.add_rule(rule::rx(rule::RECIPE_MAC, lport, rule::to_queue(target), Some(steering_mac(mac, q))))?;
                    }
                    Ok(())
                };
                match steer() {
                    Ok(()) => {
                        log::info!(
                            "ice: frames to {} .. {} go to queues 0 .. {}",
                            Mac(steering_mac(mac, 0)), Mac(steering_mac(mac, self.config.queues - 1)), self.config.queues - 1
                        );
                        return Ok(());
                    }
                    // Untested on hardware: keep receiving through the default-VSI rule rather than fail the bring-up.
                    Err(e) => log::error!("ice: per-queue steering rules rejected ({}); falling back to the default-VSI rule", e),
                }
            }
            RxSteering::Promiscuous => {}
        }
        self.add_rule(rule::rx(rule::RECIPE_DFLT, lport, rule::to_vsi(vsi), None))?;
        log::info!("ice: every frame no other rule takes goes to VSI {}", vsi);
        Ok(())
    }

    /// The queue pairs, in queue order; the device keeps none.
    pub fn take_queues(&mut self) -> Vec<(TxQueue<'p, P>, RxQueue<'p, P>)> {
        core::mem::take(&mut self.queues)
    }

    pub fn link_status(&mut self) -> Result<LinkStatus> {
        let mut buf = [0u8; cmd::LINK_BUF];
        let mut d = AqDesc::new(opc::GET_LINK_STATUS);
        d.set_u8(cmd::LINK_LPORT, self.info.lport);
        d.set_u16(cmd::LINK_FLAGS, cmd::LINK_LSE_DISABLE);
        self.send(d, Some(&mut buf))?;
        Ok(LinkStatus {
            up: buf[cmd::LINK_INFO] & cmd::LINK_UP != 0,
            speed_mbps: crate::aq::link_speed_mbps(u16::from_le_bytes([buf[cmd::LINK_SPEED], buf[cmd::LINK_SPEED + 1]])),
            max_frame: u16::from_le_bytes([buf[cmd::LINK_MAX_FRAME], buf[cmd::LINK_MAX_FRAME + 1]]),
        })
    }

    /// Waits up to `timeout_ms` for the link, restarting autonegotiation with the link enabled once if it is down.
    pub fn bring_link_up(&mut self, timeout_ms: u64) -> Result<LinkStatus> {
        let mut status = self.link_status()?;
        if status.up {
            return Ok(status);
        }
        let mut d = AqDesc::new(opc::RESTART_AN);
        d.set_u8(cmd::RESTART_AN_LPORT, self.info.lport);
        d.set_u8(cmd::RESTART_AN_FLAGS, cmd::RESTART_AN_RESTART | cmd::RESTART_AN_ENABLE);
        self.send(d, None)?;
        let mut waited = 0;
        while !status.up && waited < timeout_ms {
            self.p.delay_us(100_000);
            waited += 100;
            self.aq.drain_events(self.p);
            status = self.link_status()?;
        }
        Ok(status)
    }

    fn stat40(&self, low: usize) -> u64 {
        let lo = self.p.read32(low) as u64;
        let hi = (self.p.read32(low + 4) & 0xff) as u64;
        (hi << 32) | lo
    }

    pub fn port_stats(&self) -> PortStats {
        let lp = self.info.lport as usize;
        PortStats {
            rx_bytes: self.stat40(glprt_gorcl(lp)),
            rx_unicast: self.stat40(glprt_uprcl(lp)),
            rx_multicast: self.stat40(glprt_mprcl(lp)),
            rx_broadcast: self.stat40(glprt_bprcl(lp)),
            tx_bytes: self.stat40(glprt_gotcl(lp)),
            tx_unicast: self.stat40(glprt_uptcl(lp)),
            tx_multicast: self.stat40(glprt_mptcl(lp)),
            tx_broadcast: self.stat40(glprt_bptcl(lp)),
            crc_errors: self.p.read32(glprt_crcerrs(lp)) as u64,
            illegal_bytes: self.p.read32(glprt_illerrc(lp)) as u64,
        }
    }

    /// Stops everything with a PF reset. The queues taken out must not be used afterwards.
    pub fn shutdown(self) -> Result<()> {
        pf_reset(self.p)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vsi_properties_layout() {
        let v = vsi_properties(0x12, 28);
        assert_eq!(u16::from_le_bytes([v[0], v[1]]), 0x42);
        assert_eq!(v[2], 0x12);
        assert_eq!(v[3], 0xa0);
        assert_eq!(v[4], 0x10);
        assert_eq!(UP_TABLE_1TO1, 0x00fa_c688);
        assert_eq!(&v[16..20], &0x00fa_c688u32.to_le_bytes());
        assert_eq!(u16::from_le_bytes([v[32], v[33]]), 28);
        // 28 queues -> 2^5 in the TC queue number field (bits 14:11), offset 0.
        assert_eq!(u16::from_le_bytes([v[62], v[63]]), 5 << 11);
        assert_eq!(v[78], 2);
        assert_eq!(ceil_log2(1), 0);
        assert_eq!(ceil_log2(2), 1);
        assert_eq!(ceil_log2(8), 3);
        assert_eq!(ceil_log2(9), 4);
    }

    #[test]
    fn switch_rules() {
        let r = rule::rx(rule::RECIPE_MAC, 1, rule::to_queue(37), Some([2, 1, 2, 3, 4, 5]));
        assert_eq!(&r[0..2], &[0, 0]);
        assert_eq!(&r[4..6], &[1, 0]);
        assert_eq!(&r[6..8], &[1, 0]);
        assert_eq!(u32::from_le_bytes(r[8..12].try_into().unwrap()), 1 | (37 << 4));
        assert_eq!(&r[14..16], &[16, 0]);
        assert_eq!(&r[16..22], &[2, 1, 2, 3, 4, 5]);
        assert_eq!(&r[28..30], &[0x81, 0x00]);
        assert_eq!(rule::to_vsi(0x2a), (0x2a << 4) | (1 << 17));
    }
}
