//! Fixed-capability strings.

/// A fixed-capacity string.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct ArrayString<const N: usize> {
    data: [u8; N],
    len: usize,
}

impl<const N: usize> ArrayString<N> {
    /// Creates an empty string.
    pub const fn empty() -> Self {
        Self {
            data: [0u8; N],
            len: 0,
        }
    }

    /// Creates a fixed-capacity string.
    pub fn new(s: &str) -> Option<Self> {
        if s.len() > N {
            return None;
        }

        let mut data = [0u8; N];
        let len = s.len();
        data[0..len].copy_from_slice(s.as_bytes());

        Some(Self { data, len })
    }

    /// Extracts the string slice.
    pub fn as_str(&self) -> &str {
        // Safety: UTf-8 already checked during construction
        #[allow(unsafe_code)]
        unsafe {
            core::str::from_utf8_unchecked(self.as_slice())
        }
    }

    fn as_slice(&self) -> &[u8] {
        &self.data[0..self.len]
    }
}
