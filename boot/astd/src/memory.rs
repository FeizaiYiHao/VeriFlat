//! Common memory utilities.


/// The virtual base address userspace programs are loaded to.
pub const USERSPACE_BASE: u64 = 0x8000000000;

/// The virtual base address the payload is loaded in dom0.
pub const USERSPACE_PAYLOAD_BASE: u64 = 0x8080000000;

/// Protection on a page.
#[derive(Debug, Clone, Copy)]
pub struct PageProtection {
    /// The page can be read.
    pub read: bool,

    /// The page can be written.
    pub write: bool,

    /// The page can be executed.
    pub execute: bool,
}
