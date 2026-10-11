//! I/O utilities.

use core::convert::{AsMut, AsRef};

use displaydoc::Display;
use embedded_io as eio;
pub use embedded_io::{
    ErrorKind, ErrorType, Read, ReadExactError, Seek, SeekFrom, Write, WriteAllError, WriteFmtError,
};

/// An I/O error.
#[derive(Debug, Display)]
pub struct Error {
    kind: ErrorKind,
}

/// Wrapper of an in-memory buffer tha implements `Read` and `Seek`.
///
/// This is the no-std version of `std::io::Cursor`.
///
/// The implementation is copied from `rust/library/std/src/io/cursor.rs`.
pub struct Cursor<T> {
    inner: T,
    pos: u64,
}

impl Error {
    /// Returns a new Error.
    pub fn from_kind(kind: eio::ErrorKind) -> Self {
        Self { kind }
    }
}

impl eio::Error for Error {
    fn kind(&self) -> eio::ErrorKind {
        eio::ErrorKind::Other
    }
}

impl<T> Cursor<T> {
    /// Creates a new Cursor.
    pub fn new(inner: T) -> Self {
        Self { inner, pos: 0 }
    }

    /// Returns the current position.
    pub fn pos(&self) -> u64 {
        self.pos
    }
}

impl<T> Cursor<T>
where
    T: AsRef<[u8]>,
{
    /// Returns the remaining slice.
    pub fn remaining_slice(&self) -> &[u8] {
        let len = self.pos.min(self.inner.as_ref().len() as u64);
        &self.inner.as_ref()[(len as usize)..]
    }
}

impl<T> Cursor<T>
where
    T: AsMut<[u8]>,
{
    /// Returns the remaining slice.
    pub fn remaining_slice_mut(&mut self) -> &mut [u8] {
        let len = self.pos.min(self.inner.as_mut().len() as u64);
        &mut self.inner.as_mut()[(len as usize)..]
    }
}

impl<T> Read for Cursor<T>
where
    T: AsRef<[u8]>,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let n = Read::read(&mut self.remaining_slice(), buf).unwrap();
        self.pos += n as u64;
        Ok(n)
    }
}

impl<T> Seek for Cursor<T>
where
    T: AsRef<[u8]>,
{
    fn seek(&mut self, style: SeekFrom) -> Result<u64, Self::Error> {
        let (base_pos, offset) = match style {
            SeekFrom::Start(n) => {
                self.pos = n;
                return Ok(n);
            }
            SeekFrom::End(n) => (self.inner.as_ref().len() as u64, n),
            SeekFrom::Current(n) => (self.pos, n),
        };
        match base_pos.checked_add_signed(offset) {
            Some(n) => {
                self.pos = n;
                Ok(self.pos)
            }
            None => Err(Error {
                kind: eio::ErrorKind::InvalidInput,
            }),
        }
    }
}

impl<T> Write for Cursor<T>
where
    T: AsMut<[u8]>,
{
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        assert!(self.inner.as_mut().len() == 4096);
        assert!(self.remaining_slice_mut().len() == 4096);
        let n = Write::write(&mut self.remaining_slice_mut(), buf).unwrap();
        self.pos += n as u64;
        assert!(n == 0);
        Ok(n)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl<T> eio::ErrorType for Cursor<T> {
    type Error = Error;
}
