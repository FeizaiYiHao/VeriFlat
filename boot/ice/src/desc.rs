//! Tx data descriptors and 32-byte Rx flexible descriptors (E810 datasheet: transmit data descriptor
//! and receive descriptors, RXDID 2 "flex NIC" write-back format).

/// A 16-byte Tx data descriptor: buffer address and the command/type/offset/size quadword.
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TxDesc {
    pub buf_addr: u64,
    pub cmd_type_offset_bsz: u64,
}

const _: () = assert!(core::mem::size_of::<TxDesc>() == 16);

/// `DTYPE` (bits 3:0) of a data descriptor, and the value the device writes back once it is done with a descriptor
/// whose `RS` bit was set.
pub const TX_DTYPE_DATA: u64 = 0x0;
pub const TX_DTYPE_DESC_DONE: u64 = 0xF;
pub const TX_DTYPE_M: u64 = 0xF;
/// Command bits, at bit 4 of the quadword: end of packet, report status. The device always appends the CRC.
pub const TX_CMD_EOP: u64 = 0x0001;
pub const TX_CMD_RS: u64 = 0x0002;
pub const TX_QW1_CMD_S: u64 = 4;
pub const TX_QW1_OFFSET_S: u64 = 16;
pub const TX_QW1_BUF_SZ_S: u64 = 34;
/// Largest buffer one descriptor can point to (14 bits).
pub const TX_MAX_BUF: u64 = 0x3FFF;

impl TxDesc {
    /// One single-buffer frame of `len` bytes at `iova`, without offloads; `rs` asks for a write-back.
    pub fn data(iova: u64, len: u16, rs: bool) -> TxDesc {
        assert!((len as u64) <= TX_MAX_BUF);
        let cmd = TX_CMD_EOP | if rs { TX_CMD_RS } else { 0 };
        TxDesc { buf_addr: iova, cmd_type_offset_bsz: TX_DTYPE_DATA | (cmd << TX_QW1_CMD_S) | ((len as u64) << TX_QW1_BUF_SZ_S) }
    }

    /// Whether the device wrote this descriptor back as done.
    pub fn is_done(qw1: u64) -> bool {
        qw1 & TX_DTYPE_M == TX_DTYPE_DESC_DONE
    }

    pub fn buf_len(qw1: u64) -> u16 {
        ((qw1 >> TX_QW1_BUF_SZ_S) & TX_MAX_BUF) as u16
    }

    pub fn cmd(qw1: u64) -> u64 {
        (qw1 >> TX_QW1_CMD_S) & 0xFFF
    }
}

/// A 32-byte Rx descriptor. The driver writes the read format (packet buffer address, header buffer address 0);
/// the device overwrites it with the write-back format.
#[repr(C, align(32))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RxDesc {
    pub qw: [u64; 4],
}

const _: () = assert!(core::mem::size_of::<RxDesc>() == 32);

/// The RXDID the driver selects in `QRXFLXP_CNTXT`: the flex NIC profile, as the Linux driver uses.
pub const RXDID_FLEX_NIC: u32 = 2;

/// Write-back fields of the flex NIC format: byte 0 RXDID, bytes 2..3 packet type (bits 9:0), bytes 4..5 packet
/// length (bits 13:0), bytes 8..9 `status_error0`, bytes 12..15 the RSS hash.
pub const RX_PKT_LEN_M: u64 = 0x3FFF;
pub const RX_PTYPE_M: u64 = 0x3FF;
pub const RX_STATUS0_DD: u16 = 1 << 0;
pub const RX_STATUS0_EOF: u16 = 1 << 1;
pub const RX_STATUS0_RXE: u16 = 1 << 10;
pub const RX_STATUS0_RSS_VALID: u16 = 1 << 12;

impl RxDesc {
    /// The read format for a buffer at `iova`; clears the DD bit, which shares bit 0 of quadword 1.
    pub fn read(iova: u64) -> RxDesc {
        RxDesc { qw: [iova, 0, 0, 0] }
    }

    pub fn rxdid(qw0: u64) -> u8 {
        qw0 as u8
    }

    pub fn ptype(qw0: u64) -> u16 {
        ((qw0 >> 16) & RX_PTYPE_M) as u16
    }

    pub fn pkt_len(qw0: u64) -> u16 {
        ((qw0 >> 32) & RX_PKT_LEN_M) as u16
    }

    pub fn status0(qw1: u64) -> u16 {
        qw1 as u16
    }

    pub fn rss_hash(qw1: u64) -> u32 {
        (qw1 >> 32) as u32
    }

    /// The write-back a device produces for a frame of `len` bytes (for the tests' device model).
    pub fn writeback(len: u16, status0: u16, rss_hash: u32) -> RxDesc {
        RxDesc { qw: [(RXDID_FLEX_NIC as u64) | ((len as u64 & RX_PKT_LEN_M) << 32), status0 as u64 | ((rss_hash as u64) << 32), 0, 0] }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tx_data_descriptor() {
        let d = TxDesc::data(0x1_2345_6000, 60, true);
        assert_eq!(d.buf_addr, 0x1_2345_6000);
        // dtype 0, cmd EOP|RS = 3 at bit 4 -> 0x30, size 60 at bit 34.
        assert_eq!(d.cmd_type_offset_bsz, 0x30 | (60u64 << 34));
        assert_eq!(TxDesc::buf_len(d.cmd_type_offset_bsz), 60);
        assert_eq!(TxDesc::cmd(d.cmd_type_offset_bsz), TX_CMD_EOP | TX_CMD_RS);
        assert!(!TxDesc::is_done(d.cmd_type_offset_bsz));
        assert!(TxDesc::is_done(d.cmd_type_offset_bsz | 0xF));
        let d = TxDesc::data(0x1000, 1514, false);
        assert_eq!(TxDesc::cmd(d.cmd_type_offset_bsz), TX_CMD_EOP);
    }

    #[test]
    fn rx_read_and_writeback() {
        let r = RxDesc::read(0xdead_b000);
        assert_eq!(r.qw, [0xdead_b000, 0, 0, 0]);
        assert_eq!(RxDesc::status0(r.qw[1]) & RX_STATUS0_DD, 0);
        let w = RxDesc::writeback(60, RX_STATUS0_DD | RX_STATUS0_EOF | RX_STATUS0_RSS_VALID, 0x1234_5678);
        assert_eq!(RxDesc::rxdid(w.qw[0]), 2);
        assert_eq!(RxDesc::pkt_len(w.qw[0]), 60);
        assert_eq!(RxDesc::status0(w.qw[1]), 0x1003);
        assert_eq!(RxDesc::rss_hash(w.qw[1]), 0x1234_5678);
        // Packet length is bytes 4..5 of the descriptor.
        let bytes: [u8; 8] = w.qw[0].to_le_bytes();
        assert_eq!(u16::from_le_bytes([bytes[4], bytes[5]]), 60);
    }
}
