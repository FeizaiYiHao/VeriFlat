//! PCI functions and their BAR0 through the kernel's ownership and BAR syscalls. Every function starts unowned: dom0,
//! the root process, claims one (`claim`) before it attaches it or sends it to a driver process. The loader maps no
//! BAR; a process maps BAR0 of a function it owns (`map_bar0`) at `bar_va(physical base)`, the address the loader used
//! to map BAR0 at, so every driver keeps its register addresses: as 2M pages when BAR0 is 2M-aligned and at least
//! 2 MiB large, as 4K pages otherwise. A function cannot be sent while a BAR page of it is mapped, so its owner unmaps
//! BAR0 (`unmap_bar0`) before sending it and the receiver maps it again; a killed owner leaves it unowned.

use crate::quiet;
use vsys::*;

/// The window every process of the benchmark maps BAR0 into, at this base plus the physical address.
const BAR_WINDOW_BASE: usize = 0xd0_0000_0000;
const SIZE_2M: usize = 2 << 20;
const SIZE_1G: usize = 1 << 30;

/// BAR0's virtual address in any process of the benchmark: `BAR_WINDOW_BASE` plus its physical base.
pub fn bar_va(phys: usize) -> usize {
    BAR_WINDOW_BASE + phys
}

/// Claims `bus:dev.fun` for dom0. A function dom0 already owns (an earlier benchmark claimed it) stays owned; owned by
/// a child, it makes the next attach or map fail.
pub fn claim(who: &str, bus: usize, dev: usize, fun: usize) {
    let ret = unsafe { sys_pci_claim(bus, dev, fun) };
    if ret < 0 && error_name(ret) != "ErrorPciAlreadyOwned" {
        quiet(who, ret);
    }
}

/// The BAR-table slot of BAR0 of `bus:dev.fun` (`sys_pci_bar`'s index, the `slot` of the map calls), with its
/// physical base and size in bytes.
fn bar0_slot(who: &str, bus: usize, dev: usize, fun: usize) -> (usize, usize, usize) {
    let bdf = bus << 8 | dev << 3 | fun;
    let mut i = 0;
    loop {
        let (key, base, size) = unsafe { sys_pci_bar(i) };
        if key < 0 {
            log::error!("{}: the loader recorded no BAR0 of {:02x}:{:02x}.{}", who, bus, dev, fun);
            unsafe { sys_debug_exit(1) };
        }
        if (key as usize >> 8) & 0xffff == bdf && key as usize & 0xff == 0 {
            return (i, base, size);
        }
        i += 1;
    }
}

/// The page size and page count `map_bar0` maps BAR0 with.
fn layout(base: usize, size: usize) -> (usize, usize) {
    if base % SIZE_2M == 0 && size >= SIZE_2M { (SIZE_2M, size / SIZE_2M) } else { (4096, size.div_ceil(4096)) }
}

/// Maps BAR0 of `bus:dev.fun`, which the calling process owns, at `bar_va` of its base, after funding the calling
/// thread for the page-table pages the map calls may take (an L3 page, an L2 page per GiB, an L1 page per 2M window of
/// 4K pages) plus the 4 quota each call wants left.
pub fn map_bar0(who: &str, bus: usize, dev: usize, fun: usize) {
    let (slot, base, size) = bar0_slot(who, bus, dev, fun);
    let (va, (page, count)) = (bar_va(base), layout(base, size));
    let end = va + count * page - 1;
    let windows = if page == SIZE_2M { 0 } else { end / SIZE_2M - va / SIZE_2M + 1 };
    crate::fund(who, 4 + 1 + (end / SIZE_1G - va / SIZE_1G + 1) + windows);
    for i in 0..count {
        let ret = unsafe { if page == SIZE_2M { sys_map_pci_bar_2m(slot, i, va + i * page) } else { sys_map_pci_bar_4k(slot, i, va + i * page) } };
        quiet(who, ret);
    }
}

/// Removes the mapping `map_bar0` made of BAR0 of `bus:dev.fun`.
pub fn unmap_bar0(who: &str, bus: usize, dev: usize, fun: usize) {
    let (_, base, size) = bar0_slot(who, bus, dev, fun);
    let (va, (page, count)) = (bar_va(base), layout(base, size));
    for i in 0..count {
        let ret = unsafe { if page == SIZE_2M { sys_unmap_pci_bar_2m(va + i * page) } else { sys_unmap_pci_bar_4k(va + i * page) } };
        quiet(who, ret);
    }
}
