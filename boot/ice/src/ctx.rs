//! Queue contexts: the Rx LAN queue context the driver writes through `QRX_CONTEXT`, and the Tx LAN queue context
//! it hands to the firmware in "Add Tx LAN Queues" (E810 datasheet: receive queue context and
//! transmit queue context). A context is a little-endian bit string: a field of width `w` at bit `lsb` holds bits
//! `lsb .. lsb + w` of the buffer, bit `n` being bit `n % 8` of byte `n / 8`.

/// Rx context size: 8 dwords.
pub const RXQ_CTX_BYTES: usize = 32;
/// Tx context size in the "Add Tx LAN Queues" buffer.
pub const TXQ_CTX_BYTES: usize = 22;

/// Writes the low `width` bits of `value` at bit `lsb` of `buf`.
pub fn set_bits(buf: &mut [u8], lsb: usize, width: usize, value: u64) {
    assert!(width <= 64 && lsb + width <= buf.len() * 8, "context field out of bounds");
    assert!(width == 64 || value >> width == 0, "context value wider than its field");
    for i in 0..width {
        let bit = lsb + i;
        let mask = 1u8 << (bit % 8);
        if (value >> i) & 1 != 0 {
            buf[bit / 8] |= mask;
        } else {
            buf[bit / 8] &= !mask;
        }
    }
}

/// Reads `width` bits at bit `lsb` of `buf`.
pub fn get_bits(buf: &[u8], lsb: usize, width: usize) -> u64 {
    assert!(width <= 64 && lsb + width <= buf.len() * 8, "context field out of bounds");
    (0..width).fold(0u64, |v, i| {
        let bit = lsb + i;
        v | ((((buf[bit / 8] >> (bit % 8)) & 1) as u64) << i)
    })
}

/// Field positions (lsb, width) of the Rx LAN queue context.
pub mod rx {
    pub const HEAD: (usize, usize) = (0, 13);
    pub const CPUID: (usize, usize) = (13, 8);
    pub const BASE: (usize, usize) = (32, 57);
    pub const QLEN: (usize, usize) = (89, 13);
    pub const DBUF: (usize, usize) = (102, 7);
    pub const HBUF: (usize, usize) = (109, 5);
    pub const DTYPE: (usize, usize) = (114, 2);
    pub const DSIZE: (usize, usize) = (116, 1);
    pub const CRCSTRIP: (usize, usize) = (117, 1);
    pub const L2TSEL: (usize, usize) = (119, 1);
    pub const HSPLIT_0: (usize, usize) = (120, 4);
    pub const HSPLIT_1: (usize, usize) = (124, 2);
    pub const SHOWIV: (usize, usize) = (127, 1);
    pub const RXMAX: (usize, usize) = (174, 14);
    pub const TPHRDESC_ENA: (usize, usize) = (193, 1);
    pub const TPHWDESC_ENA: (usize, usize) = (194, 1);
    pub const TPHDATA_ENA: (usize, usize) = (195, 1);
    pub const TPHHEAD_ENA: (usize, usize) = (196, 1);
    pub const LRXQTHRESH: (usize, usize) = (198, 3);
    pub const PREFENA: (usize, usize) = (201, 1);
}

/// Field positions (lsb, width) of the Tx LAN queue context.
pub mod tx {
    pub const BASE: (usize, usize) = (0, 57);
    pub const PORT_NUM: (usize, usize) = (57, 3);
    pub const CGD_NUM: (usize, usize) = (60, 5);
    pub const PF_NUM: (usize, usize) = (65, 3);
    pub const VMVF_NUM: (usize, usize) = (68, 10);
    pub const VMVF_TYPE: (usize, usize) = (78, 2);
    pub const SRC_VSI: (usize, usize) = (80, 10);
    pub const TSYN_ENA: (usize, usize) = (90, 1);
    pub const INTERNAL_USAGE_FLAG: (usize, usize) = (91, 1);
    pub const ALT_VLAN: (usize, usize) = (92, 1);
    pub const CPUID: (usize, usize) = (93, 8);
    pub const WB_MODE: (usize, usize) = (101, 1);
    pub const TPHRD_DESC: (usize, usize) = (102, 1);
    pub const TPHRD: (usize, usize) = (103, 1);
    pub const TPHWR_DESC: (usize, usize) = (104, 1);
    pub const CMPQ_ID: (usize, usize) = (105, 9);
    pub const QNUM_IN_FUNC: (usize, usize) = (114, 14);
    pub const ITR_NOTIFICATION_MODE: (usize, usize) = (128, 1);
    pub const ADJUST_PROF_ID: (usize, usize) = (129, 6);
    pub const QLEN: (usize, usize) = (135, 13);
    pub const QUANTA_PROF_IDX: (usize, usize) = (148, 4);
    pub const TSO_ENA: (usize, usize) = (152, 1);
    pub const TSO_QNUM: (usize, usize) = (153, 11);
    pub const LEGACY_INT: (usize, usize) = (164, 1);
    pub const DROP_ENA: (usize, usize) = (165, 1);
    pub const CACHE_PROF_IDX: (usize, usize) = (166, 2);
    pub const PKT_SHAPER_PROF_IDX: (usize, usize) = (168, 3);
    /// `vmvf_type` of a PF queue.
    pub const VMVF_TYPE_PF: u64 = 2;
}

fn put(buf: &mut [u8], field: (usize, usize), value: u64) {
    set_bits(buf, field.0, field.1, value);
}

/// The Rx context of a queue in the driver's one configuration: 32-byte descriptors, no header split, CRC stripped,
/// one data buffer per frame.
#[derive(Clone, Copy, Debug)]
pub struct RxQueueContext {
    /// Ring IOVA, 128-byte aligned.
    pub base: u64,
    /// Descriptors in the ring.
    pub qlen: u16,
    /// Data buffer size in bytes, a multiple of 128.
    pub buf_len: u16,
    /// Largest frame the queue accepts, in bytes.
    pub rxmax: u16,
}

impl RxQueueContext {
    pub fn pack(&self) -> [u8; RXQ_CTX_BYTES] {
        assert!(self.base % 128 == 0 && self.buf_len % 128 == 0, "Rx ring or buffer not 128-byte aligned");
        let mut b = [0u8; RXQ_CTX_BYTES];
        put(&mut b, rx::BASE, self.base >> 7);
        put(&mut b, rx::QLEN, self.qlen as u64);
        put(&mut b, rx::DBUF, (self.buf_len >> 7) as u64);
        put(&mut b, rx::DSIZE, 1);
        put(&mut b, rx::CRCSTRIP, 1);
        // The VLAN tag goes to L2TAG1 of the descriptor (single VLAN mode, as the Linux driver sets without DVM).
        put(&mut b, rx::L2TSEL, 1);
        put(&mut b, rx::RXMAX, self.rxmax as u64);
        put(&mut b, rx::LRXQTHRESH, 1);
        put(&mut b, rx::PREFENA, 1);
        b
    }

    /// The context as the 8 dwords of `QRX_CONTEXT(0..8, q)`.
    pub fn dwords(&self) -> [u32; RXQ_CTX_BYTES / 4] {
        let b = self.pack();
        core::array::from_fn(|i| u32::from_le_bytes([b[4 * i], b[4 * i + 1], b[4 * i + 2], b[4 * i + 3]]))
    }
}

/// The Tx context of a PF queue.
#[derive(Clone, Copy, Debug)]
pub struct TxQueueContext {
    /// Ring IOVA, 128-byte aligned.
    pub base: u64,
    /// Logical port of the PF.
    pub port_num: u8,
    pub pf_num: u8,
    /// Hardware VSI number that sends from this queue.
    pub src_vsi: u16,
    pub qlen: u16,
    /// The PF queue index.
    pub pf_q: u16,
}

impl TxQueueContext {
    pub fn pack(&self) -> [u8; TXQ_CTX_BYTES] {
        assert!(self.base % 128 == 0, "Tx ring not 128-byte aligned");
        let mut b = [0u8; TXQ_CTX_BYTES];
        put(&mut b, tx::BASE, self.base >> 7);
        put(&mut b, tx::PORT_NUM, self.port_num as u64);
        put(&mut b, tx::PF_NUM, self.pf_num as u64);
        put(&mut b, tx::VMVF_TYPE, tx::VMVF_TYPE_PF);
        put(&mut b, tx::SRC_VSI, self.src_vsi as u64);
        put(&mut b, tx::TSYN_ENA, 1);
        put(&mut b, tx::QLEN, self.qlen as u64);
        // "Legacy" (non-TSO-specific) queue, as the Linux driver configures every LAN queue.
        put(&mut b, tx::TSO_ENA, 1);
        put(&mut b, tx::TSO_QNUM, self.pf_q as u64);
        put(&mut b, tx::LEGACY_INT, 1);
        b
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bits_roundtrip_across_bytes() {
        let mut b = [0u8; 32];
        set_bits(&mut b, 89, 13, 0x1abc);
        assert_eq!(get_bits(&b, 89, 13), 0x1abc);
        // Bit 89 is bit 1 of byte 11.
        assert_eq!(b[11] & 0b10, 0b0 | ((0x1abc & 1) << 1) as u8);
        set_bits(&mut b, 32, 57, (1u64 << 57) - 1);
        assert_eq!(get_bits(&b, 32, 57), (1u64 << 57) - 1);
        assert_eq!(get_bits(&b, 89, 13), 0x1abc, "neighbouring field untouched");
        set_bits(&mut b, 32, 57, 0);
        assert_eq!(&b[4..11], &[0u8; 7]);
        assert_eq!(b[11] & 1, 0);
    }

    #[test]
    #[should_panic]
    fn bits_reject_wide_value() {
        let mut b = [0u8; 4];
        set_bits(&mut b, 0, 3, 8);
    }

    #[test]
    fn rx_context_layout() {
        let ctx = RxQueueContext { base: 0x1234_5680, qlen: 512, buf_len: 2048, rxmax: 1536 };
        let b = ctx.pack();
        assert_eq!(get_bits(&b, rx::BASE.0, rx::BASE.1), 0x1234_5680 >> 7);
        // base starts at byte 4: 0x1234_5680 >> 7 = 0x2468ad.
        assert_eq!(&b[4..8], &[0xad, 0x68, 0x24, 0x00]);
        assert_eq!(get_bits(&b, rx::QLEN.0, rx::QLEN.1), 512);
        assert_eq!(get_bits(&b, rx::DBUF.0, rx::DBUF.1), 16);
        assert_eq!(get_bits(&b, rx::DSIZE.0, 1), 1);
        assert_eq!(get_bits(&b, rx::CRCSTRIP.0, 1), 1);
        assert_eq!(get_bits(&b, rx::RXMAX.0, rx::RXMAX.1), 1536);
        assert_eq!(get_bits(&b, rx::PREFENA.0, 1), 1);
        assert_eq!(get_bits(&b, rx::LRXQTHRESH.0, 3), 1);
        assert_eq!(get_bits(&b, rx::HEAD.0, rx::HEAD.1), 0);
        // Byte 25 holds bit 201 (prefena) as its bit 1 and lrxqthresh bits 198..200 in byte 24 bits 6..7 + byte 25 bit 0.
        assert_eq!(b[25] & 0b10, 0b10);
        let d = ctx.dwords();
        assert_eq!(d[1], 0x0024_68ad);
        assert!(b[26..].iter().all(|&x| x == 0));
    }

    #[test]
    fn tx_context_layout() {
        let ctx = TxQueueContext { base: 0xabc_d000_0080, port_num: 1, pf_num: 2, src_vsi: 0x155, qlen: 1024, pf_q: 37 };
        let b = ctx.pack();
        assert_eq!(get_bits(&b, tx::BASE.0, tx::BASE.1), 0xabc_d000_0080 >> 7);
        assert_eq!(get_bits(&b, tx::PORT_NUM.0, 3), 1);
        assert_eq!(get_bits(&b, tx::PF_NUM.0, 3), 2);
        assert_eq!(get_bits(&b, tx::VMVF_TYPE.0, 2), 2);
        assert_eq!(get_bits(&b, tx::SRC_VSI.0, 10), 0x155);
        assert_eq!(get_bits(&b, tx::TSYN_ENA.0, 1), 1);
        assert_eq!(get_bits(&b, tx::QLEN.0, 13), 1024);
        assert_eq!(get_bits(&b, tx::TSO_ENA.0, 1), 1);
        assert_eq!(get_bits(&b, tx::TSO_QNUM.0, 11), 37);
        assert_eq!(get_bits(&b, tx::LEGACY_INT.0, 1), 1);
        assert_eq!(get_bits(&b, tx::WB_MODE.0, 1), 0, "descriptor write-back mode");
        // port_num at bit 57: bit 1 of byte 7.
        assert_eq!(b[7] >> 1 & 0x7, 1);
    }
}
