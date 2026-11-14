//! The per-packet work of Atmosphere's maglev load-balancer benchmark (Atmosphere `dom0/src/maglev.rs`, the same file
//! as `user/maglev/src/maglev.rs`, which `start_ixgbe_driver_maglev_test` and the maglev user process call), ported
//! for `bench::run_forwarder`: the flow hash (FNV-1 over source and destination IPv4 address, protocol, ports and the
//! two bytes at frame offset 24), a flow cache keyed by that hash (open addressing, linear probing, key 0 = empty) in
//! front of the maglev lookup table of 65537 entries over the 3 backends 800, 273 and 8255, filled by the same
//! permutation. `ixgbe_driver::ixgbe_test::run_fwd_maglevtest` itself calls a `maglev::Maglev` type that is not in the
//! Atmosphere tree (its `mod maglev` is commented out), so this follows the file its maglev benchmarks do use.
//!
//! Deviations: the arithmetic wraps (`wrapping_mul`, as the original's release build does); a hash of 0 (not TCP or
//! UDP, or too short) logs nothing; each worker has its own flow cache of `CACHE_ENTRIES` entries instead of one
//! shared cache of 2 Mi entries (one shared mutable cache would race between workers, and 2 Mi entries of 16 bytes
//! per worker would not fit the DMA arenas); the lookup table is shared read-only.

/// Entries of the maglev lookup table (a prime, as in the original).
pub const TABLE_SIZE: usize = 65537;
/// Entries of each worker's flow cache (a power of two; the original has one cache of 2 Mi entries).
pub const CACHE_ENTRIES: usize = 1 << 16;
/// Bytes of one cache entry.
pub const ENTRY_BYTES: usize = 16;

const FNV_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x100_0000_01b3;
const ETH_HEADER_LEN: usize = 14;
const IPV4_PROTO_OFFSET: usize = 9;
const IPV4_SRCDST_OFFSET: usize = 12;
const IPV4_SRCDST_LEN: usize = 8;
/// The backends of the original.
const NODES: [u32; 3] = [800, 273, 8255];
/// What `process` returns when the frame has no flow hash.
pub const NO_BACKEND: usize = 0xFFFF_FFFF;

fn fnv_1_multi(data: &[u8], mut state: u64) -> u64 {
    for &b in data {
        state = state.wrapping_mul(FNV_PRIME);
        state ^= b as u64;
    }
    state
}

/// The original's `fnv_1_multi_u32` (it shifts by bits, not bytes; kept).
fn fnv_1_u32(data: u32) -> u64 {
    let mut state = FNV_BASIS;
    for i in 0..4 {
        state = state.wrapping_mul(FNV_PRIME);
        state ^= ((data & (0xFF << i)) >> i) as u64;
    }
    state
}

/// The original's `fnv_1_usize` (bit shifts kept).
fn fnv_1_u64(data: u64) -> u64 {
    let mut state = FNV_BASIS;
    for i in 0..8 {
        state = state.wrapping_mul(FNV_PRIME);
        state ^= (data & (0xFF << i)) >> i;
    }
    state
}

/// The flow hash of the frame `f`, or 0 if it is not TCP or UDP or too short (the original's `flowhash`).
pub fn flowhash(f: &[u8]) -> u64 {
    if f.len() < ETH_HEADER_LEN + 20 {
        return 0;
    }
    let proto = f[ETH_HEADER_LEN + IPV4_PROTO_OFFSET];
    if proto != 6 && proto != 17 {
        return 0;
    }
    let v4len = 4 * (f[ETH_HEADER_LEN] & 0b1111) as usize;
    if f.len() < ETH_HEADER_LEN + v4len + 4 {
        return 0;
    }
    let ip = ETH_HEADER_LEN + IPV4_SRCDST_OFFSET;
    let mut hash = fnv_1_multi(&f[ip..ip + IPV4_SRCDST_LEN], FNV_BASIS);
    hash = fnv_1_multi(&f[ETH_HEADER_LEN + IPV4_PROTO_OFFSET..ETH_HEADER_LEN + IPV4_PROTO_OFFSET + 1], hash);
    hash = fnv_1_multi(&f[ETH_HEADER_LEN + v4len..ETH_HEADER_LEN + v4len + 4], hash);
    fnv_1_multi(&f[24..26], hash)
}

fn permutation(node: u32, j: usize) -> usize {
    let offset = (fnv_1_u32(node) % (TABLE_SIZE as u64 - 1) + 1) as usize;
    let skip = (fnv_1_u32(node) % TABLE_SIZE as u64) as usize;
    (offset + j * skip) % TABLE_SIZE
}

/// Fills the lookup table `lut` (`TABLE_SIZE` entries) as the original's `populate_lut`.
pub fn populate_lut(lut: &mut [i8]) {
    assert_eq!(lut.len(), TABLE_SIZE);
    lut.fill(-1);
    let mut next = [0usize; 3];
    let mut n = 0;
    loop {
        for i in 0..NODES.len() {
            let mut c = permutation(NODES[i], next[i]);
            while lut[c] >= 0 {
                next[i] += 1;
                c = permutation(NODES[i], next[i]);
            }
            lut[c] = i as i8;
            next[i] += 1;
            n += 1;
            if n == TABLE_SIZE {
                return;
            }
        }
    }
}

/// One worker's maglev state: the shared lookup table and its own flow cache.
pub struct Maglev<'a> {
    lut: &'a [i8],
    /// (key, value) pairs; key 0 marks an empty entry.
    cache: &'a mut [[u64; 2]],
}

impl<'a> Maglev<'a> {
    /// A worker's state over the lookup table `lut` and a zeroed cache of `CACHE_ENTRIES` entries.
    pub fn new(lut: &'a [i8], cache: &'a mut [[u64; 2]]) -> Self {
        assert!(lut.len() == TABLE_SIZE && cache.len() == CACHE_ENTRIES);
        Maglev { lut, cache }
    }

    fn get(&self, key: u64) -> Option<u64> {
        let hash = fnv_1_u64(key);
        for i in 0..CACHE_ENTRIES as u64 {
            let e = &self.cache[(hash.wrapping_add(i) % CACHE_ENTRIES as u64) as usize];
            if e[0] == 0 {
                return None;
            }
            if e[0] == key {
                return Some(e[1]);
            }
        }
        None
    }

    fn insert(&mut self, key: u64, value: u64) {
        let hash = fnv_1_u64(key);
        for i in 0..CACHE_ENTRIES as u64 {
            let e = &mut self.cache[(hash.wrapping_add(i) % CACHE_ENTRIES as u64) as usize];
            if e[0] == key || e[0] == 0 {
                *e = [key, value];
                break;
            }
        }
    }

    /// The backend of frame `f` (the original's `maglev_process_frame`): the cached one, or the lookup table's,
    /// which it then caches; `NO_BACKEND` if the frame has no flow hash.
    pub fn process(&mut self, f: &[u8]) -> usize {
        let hash = flowhash(f);
        if hash == 0 {
            return NO_BACKEND;
        }
        match self.get(hash) {
            Some(b) => b as usize,
            None => {
                let b = self.lut[(hash % TABLE_SIZE as u64) as usize] as usize;
                self.insert(hash, b as u64);
                b
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_and_cache() {
        let mut lut = alloc::vec![0i8; TABLE_SIZE];
        populate_lut(&mut lut);
        let mut counts = [0usize; 3];
        lut.iter().for_each(|&b| counts[b as usize] += 1);
        assert!(counts.iter().all(|&c| c > TABLE_SIZE / 3 - 2 && c < TABLE_SIZE / 3 + 2), "{:?}", counts);
        let mut cache = alloc::vec![[0u64; 2]; CACHE_ENTRIES];
        let mut m = Maglev::new(&lut, &mut cache);
        let mut f = [0u8; 60];
        f[14] = 0x45;
        f[14 + 9] = 17;
        f[26..30].copy_from_slice(&[10, 0, 0, 1]);
        let b = m.process(&f);
        assert!(b < 3);
        assert_eq!(m.process(&f), b);
        f[14 + 9] = 1;
        assert_eq!(m.process(&f), NO_BACKEND);
    }
}
