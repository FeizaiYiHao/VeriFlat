//! The benchmark's test frame: Ethernet II, IPv4 without options, UDP with checksum 0 (allowed over IPv4), and a
//! zero payload. Each queue sends one fixed frame, which differs per queue in the destination MAC (per-queue steering
//! on the receiver), the source IP and the UDP ports (so that a receiver hashing flows sees one flow per queue).

/// Ethernet header, IPv4 header, UDP header.
pub const ETH_HDR: usize = 14;
pub const IP_HDR: usize = 20;
pub const UDP_HDR: usize = 8;
pub const HEADERS: usize = ETH_HDR + IP_HDR + UDP_HDR;
/// Smallest frame without the CRC the device appends.
pub const MIN_FRAME: usize = 60;
/// Largest frame without CRC and VLAN tag.
pub const MAX_FRAME: usize = 1514;

#[derive(Clone, Copy, Debug)]
pub struct UdpFrame {
    pub dst_mac: [u8; 6],
    pub src_mac: [u8; 6],
    pub src_ip: [u8; 4],
    pub dst_ip: [u8; 4],
    pub src_port: u16,
    pub dst_port: u16,
    /// Frame length without the CRC: `MIN_FRAME..=MAX_FRAME`.
    pub len: usize,
}

/// The one's complement checksum of an IPv4 header.
pub fn ipv4_checksum(hdr: &[u8]) -> u16 {
    let mut sum: u32 = hdr.chunks(2).map(|w| u16::from_be_bytes([w[0], *w.get(1).unwrap_or(&0)]) as u32).sum();
    while sum >> 16 != 0 {
        sum = (sum & 0xffff) + (sum >> 16);
    }
    !(sum as u16)
}

impl UdpFrame {
    /// Writes the frame into `buf[..self.len]`.
    pub fn write(&self, buf: &mut [u8]) {
        assert!((MIN_FRAME..=MAX_FRAME).contains(&self.len) && buf.len() >= self.len, "bad frame length");
        let f = &mut buf[..self.len];
        f.fill(0);
        f[0..6].copy_from_slice(&self.dst_mac);
        f[6..12].copy_from_slice(&self.src_mac);
        f[12..14].copy_from_slice(&0x0800u16.to_be_bytes());
        let ip_len = (self.len - ETH_HDR) as u16;
        let ip = &mut f[ETH_HDR..ETH_HDR + IP_HDR];
        ip[0] = 0x45;
        ip[2..4].copy_from_slice(&ip_len.to_be_bytes());
        // Don't fragment.
        ip[6] = 0x40;
        ip[8] = 64;
        ip[9] = 17;
        ip[12..16].copy_from_slice(&self.src_ip);
        ip[16..20].copy_from_slice(&self.dst_ip);
        let csum = ipv4_checksum(ip);
        ip[10..12].copy_from_slice(&csum.to_be_bytes());
        let udp = &mut f[ETH_HDR + IP_HDR..HEADERS];
        udp[0..2].copy_from_slice(&self.src_port.to_be_bytes());
        udp[2..4].copy_from_slice(&self.dst_port.to_be_bytes());
        udp[4..6].copy_from_slice(&(ip_len - IP_HDR as u16).to_be_bytes());
    }
}

/// The locally administered MAC address that steers frames to queue `q` of the host whose MAC is `base`:
/// `02:b2:b3:b4:b5:qq`.
pub fn steering_mac(base: [u8; 6], q: usize) -> [u8; 6] {
    [0x02, base[2], base[3], base[4], base[5], q as u8]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frame_layout_and_checksum() {
        let f = UdpFrame {
            dst_mac: [0x02, 1, 2, 3, 4, 5],
            src_mac: [0x00, 0x1b, 0x21, 0xaa, 0xbb, 0xcc],
            src_ip: [10, 0, 0, 1],
            dst_ip: [10, 0, 1, 2],
            src_port: 1024,
            dst_port: 5001,
            len: 60,
        };
        let mut buf = [0xffu8; 64];
        f.write(&mut buf);
        assert_eq!(&buf[12..14], &[0x08, 0x00]);
        assert_eq!(&buf[16..18], &46u16.to_be_bytes());
        assert_eq!(&buf[38..40], &26u16.to_be_bytes());
        // A header with its checksum sums to 0xffff, so the checksum over it is 0.
        assert_eq!(ipv4_checksum(&buf[14..34]), 0);
        assert!(buf[42..60].iter().all(|&b| b == 0));
        assert_eq!(buf[60], 0xff, "nothing written past the frame");
    }

    #[test]
    fn known_checksum() {
        // The classic example header from RFC 1071 style worked examples.
        let hdr = [0x45, 0x00, 0x00, 0x73, 0x00, 0x00, 0x40, 0x00, 0x40, 0x11, 0x00, 0x00, 0xc0, 0xa8, 0x00, 0x01, 0xc0, 0xa8, 0x00, 0xc7];
        assert_eq!(ipv4_checksum(&hdr), 0xb861);
    }

    #[test]
    fn steering() {
        assert_eq!(steering_mac([0xb4, 0x96, 0x91, 0xaa, 0xbb, 0xcc], 7), [0x02, 0x91, 0xaa, 0xbb, 0xcc, 7]);
    }
}
