//! Port of the generic part of Atmosphere's `ring_buffer/src/lib.rs`: `RingBuffer` of
//! `GenericRingBufferNode`s and `GenericRingBuffer` with its free stack of data buffers. Changes: a
//! node's flag and value are read and written volatile with fences, since the two sides run in two
//! processes, possibly on two cores; `SIZE_OF_QUEUE` is 1024 instead of 4096 (4 MiB of data buffers
//! instead of 16 MiB); the `usize` ring and the ixgbe types are left out.

use core::ptr::{read_volatile, write_volatile};
use core::sync::atomic::{fence, Ordering};

pub const SIZE_OF_QUEUE: usize = 1024;
pub const SIZE_OF_BUFFER: usize = 4096;

#[repr(C, align(4096))]
pub struct RingBuffer<T, const N: usize> {
    pub head: usize,
    pub head_padding: [usize; 8],
    pub ar: [T; N],
    pub tail_padding: [usize; 8],
    pub tail: usize,
}

#[derive(Debug, Clone, Copy)]
#[repr(C, align(64))]
pub struct GenericRingBufferNode<T> {
    pub is_free: bool,
    pub value: T,
}

impl<T: Copy + Clone> GenericRingBufferNode<T> {
    pub fn is_free(&self) -> bool {
        let free = unsafe { read_volatile(&self.is_free) };
        fence(Ordering::Acquire);
        free
    }
    pub fn free_value(&mut self) {
        fence(Ordering::Release);
        unsafe { write_volatile(&mut self.is_free, true) };
    }
    pub fn set_value(&mut self, target: &T) {
        unsafe { write_volatile(&mut self.value, *target) };
        fence(Ordering::Release);
        unsafe { write_volatile(&mut self.is_free, false) };
    }
    fn value(&self) -> T {
        unsafe { read_volatile(&self.value) }
    }
}

#[repr(C, align(4096))]
pub struct GenericRingBuffer<I, J> {
    pub request_queue: RingBuffer<GenericRingBufferNode<I>, SIZE_OF_QUEUE>,
    pub reply_queue: RingBuffer<GenericRingBufferNode<J>, SIZE_OF_QUEUE>,
    pub free_stack: [usize; SIZE_OF_QUEUE],
    pub data_buffer: [[u8; SIZE_OF_BUFFER]; SIZE_OF_QUEUE],
    pub len: usize,
}

impl<const N: usize, T: Copy + Clone> RingBuffer<GenericRingBufferNode<T>, N> {
    pub fn init(&mut self) {
        self.head = 0;
        self.tail = 0;
        for i in 0..N {
            self.ar[i].free_value();
        }
    }

    pub fn try_push(&mut self, target: &T) -> bool {
        if !self.ar[self.head].is_free() {
            false
        } else {
            self.ar[self.head].set_value(target);
            if self.head == N - 1 {
                self.head = 0;
            } else {
                self.head += 1;
            }
            true
        }
    }

    pub fn try_pop(&mut self) -> Option<T> {
        if self.ar[self.tail].is_free() {
            None
        } else {
            let ret = Some(self.ar[self.tail].value());
            self.ar[self.tail].free_value();
            if self.tail == N - 1 {
                self.tail = 0;
            } else {
                self.tail += 1;
            }
            ret
        }
    }

    pub fn try_read(&self) -> Option<T> {
        if self.ar[self.tail].is_free() {
            None
        } else {
            Some(self.ar[self.tail].value())
        }
    }

    pub fn try_free(&mut self) -> bool {
        if self.ar[self.tail].is_free() {
            false
        } else {
            self.ar[self.tail].free_value();
            if self.tail == N - 1 {
                self.tail = 0;
            } else {
                self.tail += 1;
            }
            true
        }
    }

    pub fn is_full(&self) -> bool {
        !self.ar[self.head].is_free()
    }
}

impl<I: Copy, J: Copy> GenericRingBuffer<I, J> {
    pub fn init(&mut self) {
        self.request_queue.init();
        self.reply_queue.init();
        self.len = 0;
        for i in 0..SIZE_OF_QUEUE {
            for j in 0..SIZE_OF_BUFFER {
                self.data_buffer[i][j] = 0;
            }
        }

        for i in 0..SIZE_OF_QUEUE {
            self.free_stack[self.len] = &self.data_buffer[i] as *const u8 as usize;
            self.len += 1;
        }
    }

    pub fn try_push_allocator(&mut self, value: usize) -> bool {
        if self.len < SIZE_OF_QUEUE {
            self.free_stack[self.len] = value;
            self.len += 1;
            true
        } else {
            false
        }
    }

    pub fn try_pop_allocator(&mut self) -> Option<usize> {
        if self.len > 0 {
            self.len -= 1;
            Some(self.free_stack[self.len])
        } else {
            None
        }
    }
}
