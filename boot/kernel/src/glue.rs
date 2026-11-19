//! Boot glue: turns the loader handoff into the runtime image that the ghost preconditions of
//! `finish_init_from_boot` describe, then calls it.
//!
//! Everything here is trusted. It classifies every physical page, picks the pages of the boot
//! singletons, the free 2M blocks and the free 1G block, writes every page lock into its cell in the page-cell static
//! and every PCID-needflush lock into its cell in the needflush-cell static, threads every free page's
//! intrusive node into the global 4K pool, every free 2M head's node into the global 2M pool and the
//! free 1G head's node into the global 1G pool at that final address, and hands the rest to the verified initializer.
//!
//! Device memory: the loader reports every assigned memory BAR as a BAR slot and maps every page of every slot's page
//! envelope into dom0 with a 4K IO leaf. The glue copies the slots into the sealed `PciBarTable` in its own static; the
//! verified initializer takes the table and the IO leaves on trust, and `check_bar_slots` and `walk_dom0` check at boot
//! what it assumes about them.

use core::mem::{align_of, size_of, MaybeUninit};
use core::ptr;

use astd::boot::{BarSlot, BootInfo, PhysicalMemoryType, MAX_PAGES};
use veriflat_monolith::*;
use vstd::prelude::{Ghost, Tracked};

use crate::gdt::GlobalDescriptorTable;

const _: () = assert!(MAX_PAGES == NUM_PAGES);

const PAGE_SIZE: usize = 4096;
const PAGES_PER_2M: usize = 512;
const PAGES_PER_1G: usize = 512 * 512;
/// Free 2M blocks handed to the 2M allocator; they are the root container's 2M quota, and each
/// new container costs two. `VERIFLAT_BOOT_2M_BLOCKS` of the kernel build sets it (decimal, default 4);
/// the benchmark images take 128 (256 MiB below the 1G block) for the parallel mmap_2m timing.
const BOOT_FREE_2M_BLOCKS: usize = match option_env!("VERIFLAT_BOOT_2M_BLOCKS") {
    Some(blocks) => parse_decimal(blocks),
    None => 4,
};

/// Free 1G blocks handed to the 1G allocator, the root container's 1G quota: 0 or 1, the block
/// [1 GiB, 2 GiB), the second GiB of the managed memory. `VERIFLAT_BOOT_1G_BLOCKS` of the kernel build
/// sets it (default 1). Without 1G page support (CPUID 8000_0001h EDX[26]) or with any of its pages
/// unavailable, boot hands out no 1G block and those pages become ordinary free 4K pages.
const BOOT_FREE_1G_BLOCKS: usize = match option_env!("VERIFLAT_BOOT_1G_BLOCKS") {
    Some(blocks) => parse_decimal(blocks),
    None => 1,
};
const _: () = assert!(BOOT_FREE_1G_BLOCKS <= 1 && 4 * PAGES_PER_1G == NUM_PAGES);

/// The value of the decimal number `text`, at compile time.
const fn parse_decimal(text: &str) -> usize {
    let digits = text.as_bytes();
    assert!(!digits.is_empty(), "boot block count is empty");
    let (mut value, mut i) = (0, 0);
    while i < digits.len() {
        assert!(digits[i].is_ascii_digit(), "boot block count is not a decimal number");
        value = value * 10 + (digits[i] - b'0') as usize;
        i += 1;
    }
    value
}
const PTE_PRESENT: u64 = 1;
const PTE_HUGE: u64 = 1 << 7;
const PTE_ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;
/// The IO bit and its uncached attributes (PWT, PCD), as the kernel encodes an IO leaf.
const PTE_IO: u64 = PAGE_ENTRY_IO_MASK;
const PTE_IO_CACHE: u64 = PAGE_ENTRY_IO_CACHE_MASK;
/// Every bit of a dom0 boot IO leaf other than its address, exactly as `page_entry2usize` writes a present, writable,
/// user, execute-disabled, kernel-present IO leaf: P, W, U, PWT, PCD, A, D, kernel-present, IO, XD. PS (PAT on a 4K
/// leaf) and G stay clear, so PCD|PWT select PAT entry 3, UC.
const IO_LEAF_FLAGS: u64 = PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_WRITE_MASK | PAGE_ENTRY_USER_MASK | PTE_IO_CACHE | PAGE_ENTRY_ACCESSED_MASK
    | PAGE_ENTRY_DIRTY_MASK | PAGE_ENTRY_KERNEL_PRESENT_MASK | PTE_IO | PAGE_ENTRY_EXECUTE_MASK;
/// End of the physical addresses a BAR slot may cover: `PciBarEntry::wf` (`base + size <= MEM_4K_MASK + 4K`, 2^48).
const IO_ADDRESS_LIMIT: u64 = MEM_4K_MASK + PAGE_SIZE as u64;
/// The fixed MMIO pages the kernel drives besides the VT-d units and ECAM windows: IOAPIC, and the xAPIC default.
const IOAPIC_BASE: u64 = 0xfec0_0000;
const LAPIC_DEFAULT_BASE: u64 = 0xfee0_0000;

type PageLock = LockCell<Page, (), (), NO_KILL_STATE>;
type NeedFlushLock = LockCell<PcidNeedFlush, (), Option<CpuId>, NO_KILL_STATE>;
type FreePool = LinkedList<PagePtr, 233>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    /// Kernel image, stack and heap, loader tables, firmware: never handed out.
    Unavailable,
    /// Part of the dom0 reservation; becomes free unless dom0 maps it.
    DomainSpare,
    Free,
    /// A dom0 page-table page (L4 and everything under `L4[KERNEL_MEM_END_L4INDEX..]`).
    Dom0Table,
    /// A dom0 user page.
    Dom0Leaf,
    /// Taken for a boot singleton; its state is set explicitly.
    Singleton,
    /// The head of a free 2M block in the global 2M pool.
    Free2m,
    /// Any other page of a free 2M block.
    Merged2m,
    /// The head of the free 1G block in the global 1G pool.
    Free1g,
    /// Any other page of the free 1G block.
    Merged1g,
}

static mut KINDS: [Kind; NUM_PAGES] = [Kind::Unavailable; NUM_PAGES];

/// Storage of the verified kernel object, written by `finish_init_from_boot`. It lives in the
/// identity-mapped kernel image, so its address is also its physical address.
#[repr(C, align(4096))]
struct KernelSlot(MaybeUninit<KernelK>);

static mut KERNEL: KernelSlot = KernelSlot(MaybeUninit::uninit());

/// Storage of every page's free-list node, outside its page lock cell: node `i` belongs to page `i`. It lives in the
/// identity-mapped kernel image, and each node's permission is created exactly once, when boot parks it in its page.
static mut PAGE_FREE_LIST_NODES: MaybeUninit<[Node<PageIndex>; NUM_PAGES]> = MaybeUninit::uninit();

/// Storage of the PCI BAR table, outside the kernel object, which keeps a shared reference to it; written once by
/// [`init_kernel`] and only read afterwards.
static mut PCI_BAR_TABLE: MaybeUninit<PciBarTable> = MaybeUninit::uninit();

/// The verified kernel object; valid after [`init_kernel`].
pub fn kernel() -> &'static mut KernelK {
    unsafe { (*(&raw mut KERNEL)).0.assume_init_mut() }
}

fn kinds() -> &'static mut [Kind; NUM_PAGES] {
    unsafe { &mut *(&raw mut KINDS) }
}

fn index_of(addr: u64) -> usize {
    let index = (addr as usize) / PAGE_SIZE;
    assert!(addr as usize % PAGE_SIZE == 0 && index < NUM_PAGES, "page {:#x} outside the managed range", addr);
    index
}

unsafe fn entry(table: usize, index: usize) -> u64 {
    ptr::read_volatile((table as *const u64).add(index))
}

/// Whether `[a.0, a.1)` and `[b.0, b.1)` overlap.
fn overlaps(a: (u64, u64), b: (u64, u64)) -> bool {
    a.0 < b.1 && b.0 < a.1
}

fn bdf_text(bdf: u16) -> (u16, u16, u16) {
    (bdf >> 8, (bdf >> 3) & 0x1f, bdf & 7)
}

/// The checked page envelope `(first page, end)` of `slot`.
fn envelope(slot: &BarSlot) -> (u64, u64) {
    let (b, d, f) = bdf_text(slot.bdf);
    slot.envelope().unwrap_or_else(|| panic!("BAR{} of {:02x}:{:02x}.{}: base {:#x} + size {:#x} overflows", slot.bar, b, d, f, slot.base, slot.size))
}

/// Checks at boot everything `finish_init_from_boot` takes on trust about the BAR slots (`pci_bar_table_wf`,
/// `pci_bar_pages_unavailable_wf`) and what the platform needs of them; panics with the slot otherwise:
/// - there are at most `PCI_BAR_TABLE_CAPACITY` slots;
/// - each slot's key is unique and its BAR index below 6 (the B/D/F is valid by its 16-bit encoding);
/// - each range is nonempty, a naturally aligned power of two, and ends at or below 2^48 (`PciBarEntry::wf`), below the
///   processor's physical address width, and below the DMAR host address width;
/// - no two slots' byte ranges overlap, and slots of different PCI functions never share a page of their envelopes;
/// - no page envelope overlaps firmware RAM at any address, nor the MMIO the kernel drives: IOAPIC, local APIC,
///   VT-d register pages, ECAM windows;
/// - every page-array page in an envelope has the loader type Reserved: not the kernel image, a boot page table,
///   dom0's reservation or free memory (the page-array state check comes after the classification, `check_bar_pages`).
/// Returns the number of page-array pages in BAR envelopes.
fn check_bar_slots(boot_info: &BootInfo) -> usize {
    assert!(core::arch::x86_64::__cpuid(0x8000_0000).eax >= 0x8000_0008, "no CPUID leaf 8000_0008h (physical address width)");
    let cpu_width = core::arch::x86_64::__cpuid(0x8000_0008).eax & 0xff;
    let iommu_width = boot_info.iommu_address_width as u32;
    assert!((32..=64).contains(&cpu_width) && (32..=64).contains(&iommu_width), "address widths {} / {}", cpu_width, iommu_width);
    let lapic = unsafe { x86::msr::rdmsr(x86::msr::IA32_APIC_BASE) } & PTE_ADDR_MASK;
    let mut kernel_mmio = [(0u64, 0u64); 3 + astd::boot::MAX_IOMMU_UNITS + astd::boot::MAX_MMCONFIG_WINDOWS];
    let mut n = 0;
    for base in [IOAPIC_BASE, LAPIC_DEFAULT_BASE, lapic].into_iter().chain(boot_info.iommu_units.iter().copied()) {
        kernel_mmio[n] = (base, base + PAGE_SIZE as u64);
        n += 1;
    }
    for &(base, size) in boot_info.mmconfig.iter() {
        kernel_mmio[n] = (base, base + size);
        n += 1;
    }
    assert!(boot_info.bar_slots.len() <= PCI_BAR_TABLE_CAPACITY, "{} BAR slots, more than the BAR table's {}", boot_info.bar_slots.len(), PCI_BAR_TABLE_CAPACITY);
    let mut pages = 0;
    for (k, slot) in boot_info.bar_slots.iter().enumerate() {
        let (b, d, f) = bdf_text(slot.bdf);
        assert!(slot.bar < 6, "BAR{} of {:02x}:{:02x}.{}: BAR index above 5", slot.bar, b, d, f);
        assert!(
            !boot_info.bar_slots[..k].iter().any(|o| (o.bdf, o.bar) == (slot.bdf, slot.bar)),
            "BAR{} of {:02x}:{:02x}.{} reported twice", slot.bar, b, d, f
        );
        assert!(slot.size.is_power_of_two() && slot.base % slot.size == 0, "BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x} is not a naturally aligned power of two", slot.bar, b, d, f, slot.base, slot.size);
        let (start, end) = envelope(slot);
        for o in boot_info.bar_slots[..k].iter() {
            let (ob, od, of) = bdf_text(o.bdf);
            assert!(
                !overlaps((slot.base, slot.base + slot.size), (o.base, o.base + o.size)),
                "BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x} overlaps BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x}",
                slot.bar, b, d, f, slot.base, slot.size, o.bar, ob, od, of, o.base, o.size
            );
            assert!(
                o.bdf == slot.bdf || !overlaps((start, end), envelope(o)),
                "BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x} shares a page with BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x}",
                slot.bar, b, d, f, slot.base, slot.size, o.bar, ob, od, of, o.base, o.size
            );
        }
        assert!(end <= IO_ADDRESS_LIMIT, "BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x} ends above 2^48, beyond the kernel's IO leaves", slot.bar, b, d, f, slot.base, slot.size);
        assert!(end <= 1 << cpu_width, "BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x} ends beyond the processor's {}-bit physical addresses", slot.bar, b, d, f, slot.base, slot.size, cpu_width);
        assert!(end <= 1 << iommu_width, "BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x} ends beyond the VT-d {}-bit host addresses", slot.bar, b, d, f, slot.base, slot.size, iommu_width);
        for &(base, size) in boot_info.ram_ranges.iter() {
            assert!(!overlaps((start, end), (base, base.saturating_add(size))), "BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x} overlaps firmware RAM {:#x}..{:#x}", slot.bar, b, d, f, slot.base, slot.size, base, base.saturating_add(size));
        }
        for &(base, mmio_end) in kernel_mmio[..n].iter() {
            assert!(!overlaps((start, end), (base, mmio_end)), "BAR{} of {:02x}:{:02x}.{}: {:#x} size {:#x} overlaps kernel MMIO {:#x}..{:#x}", slot.bar, b, d, f, slot.base, slot.size, base, mmio_end);
        }
        let mut page = start;
        while page < end.min((NUM_PAGES * PAGE_SIZE) as u64) {
            let ty = boot_info.pages[index_of(page)].1;
            assert!(ty == PhysicalMemoryType::Reserved, "page {:#x} of BAR{} of {:02x}:{:02x}.{} is {:?}", page, slot.bar, b, d, f, ty);
            pages += 1;
            page += PAGE_SIZE as u64;
        }
    }
    pages
}

/// Checks that every page-array page in a BAR envelope ends Unavailable (`pci_bar_pages_unavailable_wf`), after
/// every page is classified.
fn check_bar_pages(boot_info: &BootInfo) {
    let kinds = kinds();
    for slot in boot_info.bar_slots.iter() {
        let (start, end) = envelope(slot);
        let mut page = start;
        while page < end.min((NUM_PAGES * PAGE_SIZE) as u64) {
            let i = index_of(page);
            assert!(kinds[i] == Kind::Unavailable, "BAR page {:#x} is {:?}", page, kinds[i]);
            page += PAGE_SIZE as u64;
        }
    }
}

/// Whether 4K page `page` lies in the page envelope of some BAR slot (`pci_bar_page`).
fn bar_page(boot_info: &BootInfo, page: u64) -> bool {
    boot_info.bar_slots.iter().any(|slot| {
        let (start, end) = envelope(slot);
        start <= page && page < end
    })
}

/// Marks the dom0 page-table closure and its user leaves; returns the numbers of table pages, RAM leaves and IO leaves.
/// dom0's boot page table holds 4K leaves only and no IO bit above a leaf. An IO
/// leaf (bit 53) must carry exactly `IO_LEAF_FLAGS` and map a BAR page (`boot_dom0_io_manifest_wf`); a RAM leaf must
/// carry neither the IO bit nor PWT/PCD and map a page of dom0's reservation.
unsafe fn walk_dom0(boot_info: &BootInfo) -> (usize, usize, usize) {
    let dom0_pml4 = boot_info.dom0_pml4 as usize;
    let mut tables = 0;
    let mut leaves = 0;
    let mut io_leaves = 0;
    let mut mark_table = |addr: u64| {
        let kinds = kinds();
        let i = index_of(addr);
        assert!(kinds[i] == Kind::Unavailable, "dom0 table page {:#x} is {:?}", addr, kinds[i]);
        kinds[i] = Kind::Dom0Table;
        tables += 1;
    };
    let directory = |e: u64, level: &str| {
        assert!(e & PTE_HUGE == 0, "dom0's boot page table has a {} leaf: boot maps 4K pages only", level);
        assert!(e & (PTE_IO | PTE_IO_CACHE) == 0, "dom0 {} directory entry {:#x} has the IO bit or PWT/PCD", level, e);
        (e & PTE_ADDR_MASK) as usize
    };
    mark_table(dom0_pml4 as u64);
    for l4i in KERNEL_MEM_END_L4INDEX..512 {
        let e4 = entry(dom0_pml4, l4i);
        if e4 & PTE_PRESENT == 0 {
            continue;
        }
        let l3 = directory(e4, "L4");
        mark_table(l3 as u64);
        for l3i in 0..512 {
            let e3 = entry(l3, l3i);
            if e3 & PTE_PRESENT == 0 {
                continue;
            }
            let l2 = directory(e3, "1G");
            mark_table(l2 as u64);
            for l2i in 0..512 {
                let e2 = entry(l2, l2i);
                if e2 & PTE_PRESENT == 0 {
                    continue;
                }
                let l1 = directory(e2, "2M");
                mark_table(l1 as u64);
                for l1i in 0..512 {
                    let e1 = entry(l1, l1i);
                    if e1 & PTE_PRESENT == 0 {
                        continue;
                    }
                    let leaf = e1 & PTE_ADDR_MASK;
                    let va = (l4i << 39 | l3i << 30 | l2i << 21 | l1i << 12) as u64;
                    if e1 & PTE_IO != 0 {
                        assert!(e1 & !PTE_ADDR_MASK == IO_LEAF_FLAGS, "dom0 IO leaf {:#x} at {:#x}: flags are not those of a kernel IO leaf", e1, va);
                        assert!(bar_page(boot_info, leaf), "dom0 IO leaf at {:#x} maps {:#x}, outside every BAR slot", va, leaf);
                        io_leaves += 1;
                        continue;
                    }
                    assert!(e1 & PTE_IO_CACHE == 0, "dom0 RAM leaf {:#x} at {:#x} has PWT/PCD", e1, va);
                    let kinds = kinds();
                    let i = index_of(leaf);
                    kinds[i] = match kinds[i] {
                        Kind::DomainSpare => Kind::Dom0Leaf,
                        k => panic!("dom0 leaf {:#x} at {:#x} is {:?}", leaf, va, k),
                    };
                    leaves += 1;
                }
            }
        }
    }
    (tables, leaves, io_leaves)
}

fn take_4k(cursor: &mut usize) -> usize {
    let kinds = kinds();
    while *cursor < NUM_PAGES {
        let i = *cursor;
        *cursor += 1;
        if i != 0 && kinds[i] == Kind::Free {
            kinds[i] = Kind::Singleton;
            return i * PAGE_SIZE;
        }
    }
    panic!("out of free pages for boot singletons");
}

fn take_2m(cursor: &mut usize) -> usize {
    let kinds = kinds();
    while *cursor + PAGES_PER_2M <= NUM_PAGES {
        let head = *cursor;
        *cursor += PAGES_PER_2M;
        if head != 0 && kinds[head..head + PAGES_PER_2M].iter().all(|k| *k == Kind::Free) {
            kinds[head..head + PAGES_PER_2M].fill(Kind::Singleton);
            return head * PAGE_SIZE;
        }
    }
    panic!("no free 2M block left at boot");
}

/// Whether the processor maps 1G pages (CPUID 8000_0001h EDX[26], pdpe1gb).
fn cpu_has_1g_pages() -> bool {
    let max_extended = unsafe { core::arch::x86_64::__cpuid(0x8000_0000).eax };
    max_extended >= 0x8000_0001 && unsafe { core::arch::x86_64::__cpuid(0x8000_0001).edx } & (1 << 26) != 0
}

/// Takes [1 GiB, 2 GiB) as the free 1G block when the build asks for one, the processor maps 1G pages
/// and every page of it is free; returns the number of blocks taken.
fn take_1g() -> usize {
    if BOOT_FREE_1G_BLOCKS == 0 {
        return 0;
    }
    if !cpu_has_1g_pages() {
        log::warn!("no 1G page support (pdpe1gb): [1 GiB, 2 GiB) stays 4K pages");
        return 0;
    }
    let block = &mut kinds()[PAGES_PER_1G..2 * PAGES_PER_1G];
    if !block.iter().all(|k| *k == Kind::Free) {
        log::warn!("[1 GiB, 2 GiB) is not all free memory: no free 1G block");
        return 0;
    }
    block[0] = Kind::Free1g;
    block[1..].fill(Kind::Merged1g);
    1
}

fn singleton_state(layout: &BootKernelLayout, addr: usize) -> Option<PageState> {
    use Allocated4KPageState as A4;
    let a4 = |state| Some(PageState::Allocated4k { state });
    if addr == layout.root_container {
        return Some(PageState::Allocated2m { state: Allocated2MPageState::AsContainer });
    }
    if addr == layout.pcid_allocator {
        return Some(PageState::Allocated2m { state: Allocated2MPageState::AsPcidAllocator });
    }
    if addr > layout.root_container && addr < layout.root_container + PAGES_PER_2M * PAGE_SIZE
        || addr > layout.pcid_allocator && addr < layout.pcid_allocator + PAGES_PER_2M * PAGE_SIZE
    {
        return Some(PageState::Merged2m);
    }
    match addr {
        a if a == layout.allocator_4k => a4(A4::As4KAllocator),
        a if a == layout.allocator_2m => a4(A4::As2MAllocator),
        a if a == layout.allocator_1g => a4(A4::As1GAllocator),
        a if a == layout.scheduler => a4(A4::AsScheduler),
        a if a == layout.cpu_set => a4(A4::AsCpuSet),
        a if a == layout.root_process => a4(A4::AsProcess),
        a if a == layout.cpu_pagetable => a4(A4::AsPageTableRoot { table_type: PT_TYPE }),
        a if a == layout.root_thread => a4(A4::AsThread),
        a if a == layout.root_endpoint => a4(A4::AsEndpoint),
        a if a == layout.iommu_table => a4(A4::AsPageTableRoot { table_type: IOMMU_TYPE }),
        a if a == layout.iommu_l4 => a4(A4::PageTable { pagetable_root: layout.iommu_table, table_type: IOMMU_TYPE }),
        _ => None,
    }
}

fn new_page(addr: usize, state: PageState, ref_count: usize, owning_container: usize, free_list_node_storage: ExternalNode<PageIndex>) -> Page {
    Page {
        addr,
        state,
        ref_count,
        owning_container,
        mappings: Ghost::assume_new(),
        iommu_mappings: Ghost::assume_new(),
        free_list_node_storage,
        free_list: 0,
        perm_4k: Tracked::assume_new(),
        perm_2m: Tracked::assume_new(),
        perm_1g: Tracked::assume_new(),
    }
}

type CpuLock = LockCell<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>;

/// The verified kernel's object of cpu `cpu_id`, the value of its lock cell in the cpu-cell static (the lock word comes
/// first in the `repr(C)` cell). The trap layer reads only `current_thread` of its own cpu through it, outside steps
/// (`syscalls::sync_current_frame`).
pub fn verified_cpu(cpu_id: usize) -> *const Cpu {
    assert!(cpu_id < NUM_CPUS);
    let value_offset = size_of::<SpinWord>().next_multiple_of(align_of::<Cpu>());
    (<CpuLock as TokenCellBase>::cell_base() + cpu_id * size_of::<CpuLock>() + value_offset) as *const Cpu
}

/// Physical address of the VT-d root table: one 4K page past the root-table lock cell, which lies in the identity-mapped
/// kernel image.
pub fn iommu_root_table() -> u64 {
    (irt_cell_base() + VTD_TABLE_SIZE) as u64
}

/// Builds the verified kernel in [`KERNEL`].
pub unsafe fn init_kernel(boot_info: &BootInfo) {
    let kernel_ptr = (&raw mut KERNEL) as usize;
    log::info!("KernelK: {} bytes at {:#x}; page lock {} bytes", size_of::<KernelK>(), kernel_ptr, size_of::<PageLock>());
    assert!(kernel_ptr % PAGE_SIZE == 0);
    assert!(align_of::<KernelK>() <= PAGE_SIZE);
    assert!(boot_info.pages.len() == NUM_PAGES);

    // 1. Classify every page.
    let kinds = kinds();
    for (i, (addr, ty)) in boot_info.pages.iter().enumerate() {
        assert!(*addr as usize == i * PAGE_SIZE, "page list out of order at {}", i);
        kinds[i] = match ty {
            PhysicalMemoryType::Available => Kind::Free,
            PhysicalMemoryType::Domain => Kind::DomainSpare,
            _ => Kind::Unavailable,
        };
    }
    // BAR slots, and dom0's page table with its IO leaves.
    let bar_pages = check_bar_slots(boot_info);
    let dom0_pml4 = boot_info.dom0_pml4 as usize;
    let (tables, leaves, io_leaves) = walk_dom0(boot_info);
    for k in kinds.iter_mut() {
        if *k == Kind::DomainSpare {
            *k = Kind::Free;
        }
    }
    // Page 0, and the AP trampoline (arguments at 0x6fe0, code from 0x7000) with room to spare.
    for kind in kinds[..16].iter_mut() {
        assert!(*kind == Kind::Free || *kind == Kind::Unavailable, "low page holds {:?}", kind);
        *kind = Kind::Unavailable;
    }

    // The default page table must only hold the kernel prefix.
    let kernel_pml4 = boot_info.pml4 as usize;
    for l4i in KERNEL_MEM_END_L4INDEX..512 {
        assert!(entry(kernel_pml4, l4i) & PTE_PRESENT == 0, "kernel PML4 has a user entry {}", l4i);
    }

    // 2. The free 1G block first, so that the boot singletons and the free 2M blocks stay below it.
    let free_1g_blocks = take_1g();

    // Boot singletons.
    let mut cursor_2m = PAGES_PER_2M;
    let root_container = take_2m(&mut cursor_2m);
    let pcid_allocator = take_2m(&mut cursor_2m);
    let mut cursor = 1;
    let layout = BootKernelLayout {
        kernel_ptr,
        root_container,
        pcid_allocator,
        allocator_4k: take_4k(&mut cursor),
        allocator_2m: take_4k(&mut cursor),
        allocator_1g: take_4k(&mut cursor),
        scheduler: take_4k(&mut cursor),
        cpu_set: take_4k(&mut cursor),
        root_process: take_4k(&mut cursor),
        cpu_pagetable: take_4k(&mut cursor),
        root_thread: take_4k(&mut cursor),
        root_endpoint: take_4k(&mut cursor),
        iommu_table: take_4k(&mut cursor),
        iommu_l4: take_4k(&mut cursor),
        cpu_cr3: dom0_pml4,
    };
    for _ in 0..BOOT_FREE_2M_BLOCKS {
        let head = take_2m(&mut cursor_2m) / PAGE_SIZE;
        kinds[head] = Kind::Free2m;
        kinds[head + 1..head + PAGES_PER_2M].fill(Kind::Merged2m);
    }
    check_bar_pages(boot_info);

    // 3. Page lock cells, written in place at their final address, each holding its page's parked free-list node.
    let page_base = page_cells_base();
    let node_base = (&raw mut PAGE_FREE_LIST_NODES) as usize;
    let page_value_offset = size_of::<SpinWord>().next_multiple_of(align_of::<Page>());
    let mut free_4k_pool: FreePool = LinkedList::new(Some(0), Some(root_container));
    let mut free_2m_pool: FreePool = LinkedList::new(Some(0), Some(root_container));
    let mut free_1g_pool: FreePool = LinkedList::new(Some(0), Some(root_container));
    let mut free_count = 0usize;
    for i in 0..NUM_PAGES {
        let addr = i * PAGE_SIZE;
        let (state, ref_count) = match kinds[i] {
            Kind::Unavailable => (PageState::Unavailable, 0),
            Kind::Free => (PageState::Free4k { allocator_ptr: Ghost::assume_new(), state: FreePageAllocatorState::GlobalList }, 0),
            Kind::Free2m => (PageState::Free2m { allocator_ptr: Ghost::assume_new(), state: FreePageAllocatorState::GlobalList }, 0),
            Kind::Merged2m => (PageState::Merged2m, 0),
            Kind::Free1g => (PageState::Free1g { allocator_ptr: Ghost::assume_new(), state: FreePageAllocatorState::GlobalList }, 0),
            Kind::Merged1g => (PageState::Merged1g, 0),
            Kind::Dom0Table => (
                PageState::Allocated4k {
                    state: Allocated4KPageState::PageTable { pagetable_root: layout.cpu_pagetable, table_type: PT_TYPE },
                },
                0,
            ),
            Kind::Dom0Leaf => (PageState::Mapped4k, 1),
            Kind::Singleton => (singleton_state(&layout, addr).expect("unclassified singleton page"), 0),
            Kind::DomainSpare => unreachable!(),
        };
        let lock_ptr = (page_base + i * size_of::<PageLock>()) as *mut PageLock;
        let node_addr = node_base + i * size_of::<Node<PageIndex>>();
        ptr::write(node_addr as *mut Node<PageIndex>, Node { value: 0, next: None, prev: None });
        let node = ExternalNode::new_parked(node_addr, Tracked::assume_new());
        let page = new_page(addr, state, ref_count, root_container, node);
        ptr::write(lock_ptr, LockCell::new_unlocked(page, (), Ghost::assume_new()));
        if matches!(kinds[i], Kind::Free | Kind::Free2m | Kind::Free1g) {
            let page = &mut *((lock_ptr as usize + page_value_offset) as *mut Page);
            assert!(page.addr == addr, "LockCell value offset mismatch");
            let (node_addr, mut node_perm) = page.free_list_node_storage.take();
            node_update_value(node_addr, &mut node_perm, addr);
            match kinds[i] {
                Kind::Free => {
                    free_4k_pool.push_tail(node_addr, node_perm);
                    free_count += 1;
                }
                Kind::Free2m => free_2m_pool.push_tail(node_addr, node_perm),
                _ => free_1g_pool.push_tail(node_addr, node_perm),
            }
        }
    }
    let page_array = PageLockedArray::from_token_cells(TokenCells { perms: Tracked::assume_new() });
    log::info!(
        "pages: {} free, {} free 2M blocks, {} free 1G blocks, {} dom0 tables, {} dom0 RAM leaves; {} BAR slots, {} BAR pages in the page array (Unavailable), {} dom0 4K IO leaves",
        free_count, BOOT_FREE_2M_BLOCKS, free_1g_blocks, tables, leaves, boot_info.bar_slots.len(), bar_pages, io_leaves
    );

    // 4. PCID needflush locks, written in place; cell `(cpu, pcid)` is cell `cpu * PCID_MAX + pcid`.
    let needflush_base = pcid_needflush_cells_base();
    for k in 0..NUM_CPUS * PCID_MAX {
        let lock_ptr = (needflush_base + k * size_of::<NeedFlushLock>()) as *mut NeedFlushLock;
        ptr::write(lock_ptr, LockCell::new_unlocked(PcidNeedFlush::new(Ghost::assume_new(), Ghost::assume_new()), (), Ghost::assume_new()));
    }
    let pcid_needflush = PcidNeedFlushArray::from_token_cells(Tracked::assume_new());

    // 5. Default page table and the per-cpu hardware cr3/pcid words.
    let default_pagetable = ReadOnlyNode::new(PageTable::new(Some(KERNEL_DEFAULT_PCID), Ghost::assume_new(), kernel_pml4, Tracked::assume_new(), KERNEL_MEM_END_L4INDEX, 0));
    let cpu_hw_cr3_pcid: CpuHwCr3PcidArray = core::array::from_fn(|cpu_id| AtomicPcidCr3::new(cpu_id, kernel_pml4, KERNEL_DEFAULT_PCID));

    // 6. The root thread's first frame.
    let dom0 = boot_info.dom0.as_ref().expect("no dom0");
    let mut initial_regs = Registers::zeroed();
    initial_regs.rip = dom0.entry_point as u64;
    initial_regs.rsp = dom0.virt_start.add(dom0.reserved_size - 0x1000) as u64;
    initial_regs.cs = GlobalDescriptorTable::USER_CS as u64;
    initial_regs.ss = GlobalDescriptorTable::USER_SS as u64;
    initial_regs.flags = 0x202;
    if let Some(payload) = &boot_info.payload {
        initial_regs.rdi = payload.base as u64;
        initial_regs.rsi = payload.size as u64;
    }

    // 7. The cpu objects and the empty CPU TLB and IOTLB models.
    let cpu_array = Cpu::new_boot_array(layout.root_container, default_pagetable.borrow().cr3);
    let cpu_tlb = CpuTLB::new_empty();
    let iommu_tlb = IommuTLB::new_empty();

    // 8. The BAR table, in its static: one entry per slot of `boot_info.bar_slots` (checked by `check_bar_slots`), with
    // its B/D/F, BAR index and exact byte range.
    let empty = PciBarEntry { bdf: (0, 0, 0), bar: 0, base: 0, size: 0 };
    let mut bar_entries = Array { ar: [empty; PCI_BAR_TABLE_CAPACITY] };
    for (entry, slot) in bar_entries.ar.iter_mut().zip(boot_info.bar_slots.iter()) {
        let (b, d, f) = bdf_text(slot.bdf);
        *entry = PciBarEntry { bdf: (b as usize, d as usize, f as usize), bar: slot.bar as usize, base: slot.base as usize, size: slot.size as usize };
    }
    let pci_bars: &'static PciBarTable = (*(&raw mut PCI_BAR_TABLE)).write(PciBarTable::new(bar_entries, boot_info.bar_slots.len()));

    // Ghost arguments, in order: the kernel's L4 entries, dom0's 4K manifest (every present user leaf `walk_dom0`
    // checked, RAM and IO, at its VA, owned by the root container), every page pointer, and the boot table reverse maps;
    // the BAR table sits between the manifest and the page pointers. Every PCI function starts unowned.
    let _ = finish_init_from_boot(
        layout, KERNEL_MEM_END_L4INDEX, &initial_regs, page_array, pcid_needflush, cpu_hw_cr3_pcid, default_pagetable, cpu_array, cpu_tlb, iommu_tlb,
        free_4k_pool, free_2m_pool, free_1g_pool,
        Ghost::assume_new(), Ghost::assume_new(), pci_bars, Ghost::assume_new(), Ghost::assume_new(),
        Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(),
        Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(),
        Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(),
        Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(),
        Tracked::assume_new(),
    );
    // The cpu objects lie where `verified_cpu` looks: every one belongs to the root container, and only cpu 0 is Idle.
    for cpu_id in 0..NUM_CPUS {
        let cpu = &*verified_cpu(cpu_id);
        assert!(cpu.owning_container() == root_container && cpu.current_thread().is_none(), "cpu {} object misplaced", cpu_id);
        assert!(matches!(cpu.state(), CpuState::Idle) == (cpu_id == 0), "cpu {} object misplaced", cpu_id);
    }
    log::info!("VeriFlat kernel initialized: root container {:#x}, root thread {:#x}", root_container, layout.root_thread);
}
