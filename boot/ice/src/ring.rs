//! Index arithmetic of a descriptor ring of `size` entries.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ring {
    size: usize,
}

impl Ring {
    pub fn new(size: usize) -> Ring {
        assert!(size >= 2, "a ring needs at least two descriptors");
        Ring { size }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    /// `i + n` modulo the size.
    pub fn add(&self, i: usize, n: usize) -> usize {
        (i + n % self.size) % self.size
    }

    /// `i - n` modulo the size.
    pub fn sub(&self, i: usize, n: usize) -> usize {
        (i + self.size - n % self.size) % self.size
    }

    /// Entries from `from` up to, not including, `to`.
    pub fn distance(&self, from: usize, to: usize) -> usize {
        (to + self.size - from) % self.size
    }

    /// Entries a producer at `next_to_use` may still fill when the consumer reclaimed up to `next_to_clean`; one
    /// entry always stays empty, so that a full ring differs from an empty one.
    pub fn free(&self, next_to_use: usize, next_to_clean: usize) -> usize {
        self.size - 1 - self.distance(next_to_clean, next_to_use)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic() {
        let r = Ring::new(8);
        assert_eq!(r.add(6, 3), 1);
        assert_eq!(r.add(6, 16), 6);
        assert_eq!(r.sub(1, 3), 6);
        assert_eq!(r.sub(0, 1), 7);
        assert_eq!(r.distance(6, 1), 3);
        assert_eq!(r.distance(3, 3), 0);
        assert_eq!(r.free(0, 0), 7);
        assert_eq!(r.free(7, 0), 0);
        assert_eq!(r.free(2, 3), 0);
        assert_eq!(r.free(3, 2), 6);
    }

    #[test]
    fn fill_and_drain_cycle() {
        let r = Ring::new(16);
        let (mut ntu, mut ntc) = (0, 0);
        for round in 0..100 {
            let n = r.free(ntu, ntc).min(5 + round % 7);
            ntu = r.add(ntu, n);
            let done = r.distance(ntc, ntu).min(3 + round % 5);
            ntc = r.add(ntc, done);
            assert!(r.distance(ntc, ntu) < 16);
        }
    }
}
