//! dom0's heap, after Atmosphere's `dom0/src/slab_alloc.rs`: a global allocator whose pager maps fresh
//! pages with `mmap_4k` and maps them into the process's IOMMU table at IOVA = VA with `iommu_map_4k`,
//! so every allocation can be handed to a device, as Atmosphere's `sys_mmap` + `sys_io_mmap` pager does.
//! The `slabmalloc` zone allocator and `spin` are not in the boot workspace; in their place objects up to
//! 2 KiB come from power-of-two slabs carved out of 4 KiB pages, and larger ones are page-granular runs
//! from a contiguous bump region with per-size free lists, so a multi-page allocation (an NVMe queue) is
//! contiguous in VA and IOVA.
//!
//! The allocator state lives in a private page at `HEAP_STATE_VA` of each process, not in dom0's image,
//! because the NVMe driver process shares that image: each process calls `init` once before allocating.

use core::alloc::{GlobalAlloc, Layout};
use core::ptr;
use core::sync::atomic::{AtomicBool, Ordering};

use vsys::*;

pub const HEAP_STATE_VA: usize = 0xd8_0000_0000;
/// The bump region, from 2 MiB above the state page to the next GiB.
const HEAP_BASE: usize = HEAP_STATE_VA + 0x20_0000;
const HEAP_LIMIT: usize = HEAP_STATE_VA + 0x4000_0000;
const PAGE: usize = 4096;
/// Pages the pager maps at least per refill.
const MAP_CHUNK: usize = 64;
/// Slab classes 16, 32, ..., 2048 bytes.
const SMALL_CLASSES: usize = 8;
/// Free lists of page runs of 1 to 64 pages; longer runs are not reused.
const LARGE_CLASSES: usize = 64;

#[repr(C)]
struct HeapState {
    lock: AtomicBool,
    /// Next free byte of the bump region and the end of its mapped part.
    next: usize,
    mapped: usize,
    small: [usize; SMALL_CLASSES],
    large: [usize; LARGE_CLASSES],
}

fn state() -> *mut HeapState {
    HEAP_STATE_VA as *mut HeapState
}

/// Funds the calling thread with `amount` 4K quota through its process.
fn fund(amount: usize) -> bool {
    unsafe { sys_alloc_quota_4k(amount) >= 0 && sys_alloc_thread_quota_4k(amount) >= 0 }
}

/// Runs `map`, an `mmap_4k` (`per_page` = 4) or `iommu_map_4k` (3) of `count` pages, which the kernel refuses with
/// `ErrorNoQuota` unless the calling thread holds `per_page` 4K quota per page for the worst case of page tables.
/// Each refusal funds the thread `count` more, so it is funded only for its shortfall; what the call leaves unused
/// stays with the thread for the next one.
fn funded(per_page: usize, count: usize, map: impl Fn() -> isize) -> bool {
    for _ in 0..per_page {
        match map() {
            r if r >= 0 => return true,
            r if error_name(r) == "ErrorNoQuota" && fund(count) => {}
            _ => return false,
        }
    }
    map() >= 0
}

/// Maps the state page of the calling process. Call once per process before the first allocation.
pub fn init() {
    if !fund(4) || unsafe { sys_mmap_4k(HEAP_STATE_VA, 1) } < 0 {
        log::error!("heap: cannot map the state page");
        unsafe { sys_debug_exit(1) };
    }
    unsafe {
        state().write(HeapState { lock: AtomicBool::new(false), next: HEAP_BASE, mapped: HEAP_BASE, small: [0; SMALL_CLASSES], large: [0; LARGE_CLASSES] });
    }
}

impl HeapState {
    /// Maps at least `pages` more pages at the end of the bump region, CPU and IOMMU.
    fn grow(&mut self, pages: usize) -> bool {
        let count = pages.max(MAP_CHUNK);
        if self.mapped + count * PAGE > HEAP_LIMIT {
            return false;
        }
        let va = self.mapped;
        if !funded(4, count, || unsafe { sys_mmap_4k(va, count) }) || !funded(3, count, || unsafe { sys_iommu_map_4k(va, va, count) }) {
            return false;
        }
        self.mapped += count * PAGE;
        true
    }

    fn alloc_pages(&mut self, pages: usize) -> *mut u8 {
        if pages <= LARGE_CLASSES && self.large[pages - 1] != 0 {
            let run = self.large[pages - 1];
            self.large[pages - 1] = unsafe { *(run as *const usize) };
            return run as *mut u8;
        }
        if self.next + pages * PAGE > self.mapped && !self.grow((self.next + pages * PAGE - self.mapped) / PAGE) {
            return ptr::null_mut();
        }
        let run = self.next;
        self.next += pages * PAGE;
        run as *mut u8
    }

    fn alloc_small(&mut self, class: usize) -> *mut u8 {
        if self.small[class] == 0 {
            let page = self.alloc_pages(1) as usize;
            if page == 0 {
                return ptr::null_mut();
            }
            let size = 16 << class;
            for block in (page..page + PAGE).step_by(size).rev() {
                unsafe { *(block as *mut usize) = self.small[class] };
                self.small[class] = block;
            }
        }
        let block = self.small[class];
        self.small[class] = unsafe { *(block as *const usize) };
        block as *mut u8
    }
}

/// The slab class of `layout`, or `None` for a page run.
fn class_of(layout: Layout) -> Option<usize> {
    let size = layout.size().max(layout.align()).max(16).next_power_of_two();
    (size <= 2048).then(|| size.trailing_zeros() as usize - 4)
}

pub struct Heap;

unsafe impl GlobalAlloc for Heap {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if layout.align() > PAGE {
            return ptr::null_mut();
        }
        let st = unsafe { &mut *state() };
        while st.lock.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
            core::hint::spin_loop();
        }
        let p = match class_of(layout) {
            Some(class) => st.alloc_small(class),
            None => st.alloc_pages(layout.size().div_ceil(PAGE)),
        };
        st.lock.store(false, Ordering::Release);
        p
    }

    unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
        let st = unsafe { &mut *state() };
        while st.lock.compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed).is_err() {
            core::hint::spin_loop();
        }
        match class_of(layout) {
            Some(class) => {
                unsafe { *(p as *mut usize) = st.small[class] };
                st.small[class] = p as usize;
            }
            None => {
                let pages = layout.size().div_ceil(PAGE);
                if pages <= LARGE_CLASSES {
                    unsafe { *(p as *mut usize) = st.large[pages - 1] };
                    st.large[pages - 1] = p as usize;
                }
            }
        }
        st.lock.store(false, Ordering::Release);
    }
}
