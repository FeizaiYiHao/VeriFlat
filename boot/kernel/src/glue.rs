//! Boot glue: turns the loader handoff into the runtime image that the ghost preconditions of
//! `finish_init_from_boot` describe, then calls it.
//!
//! Everything here is trusted. It classifies every physical page, picks the pages of the boot
//! singletons and the free 2M blocks, writes the page array and the PCID-needflush array in place
//! at their final `KernelK` offsets, threads every free page's intrusive node into the global 4K
//! pool and every free 2M head's node into the global 2M pool at that final address, and hands
//! the rest to the verified initializer.

use core::mem::{align_of, offset_of, size_of, MaybeUninit};
use core::ptr;

use astd::boot::{BootInfo, PhysicalMemoryType, MAX_PAGES};
use veriflat_monolith::*;
use vstd::prelude::{Ghost, Tracked};

use crate::gdt::GlobalDescriptorTable;

const _: () = assert!(MAX_PAGES == NUM_PAGES);

const PAGE_SIZE: usize = 4096;
const PAGES_PER_2M: usize = 512;
/// Free 2M blocks handed to the 2M allocator; they are the root container's 2M quota, and each
/// new container costs two.
const BOOT_FREE_2M_BLOCKS: usize = 4;
const PTE_PRESENT: u64 = 1;
const PTE_HUGE: u64 = 1 << 7;
const PTE_ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;

type PageLock = RwLock<Page, (), (), NO_KILL_STATE>;
type NeedFlushLock = RwLock<PcidNeedFlush, (), Option<CpuId>, NO_KILL_STATE>;
type FreePool = LinkedList<PagePtr, ALLOCATOR_GLOBAL_POOL_MAJOR>;

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
}

static mut KINDS: [Kind; NUM_PAGES] = [Kind::Unavailable; NUM_PAGES];

/// Storage of the verified kernel object, written by `finish_init_from_boot`. It lives in the
/// identity-mapped kernel image, so its address is also its physical address (the IOMMU root
/// table inside it must be page aligned).
#[repr(C, align(4096))]
struct KernelSlot(MaybeUninit<KernelK>);

static mut KERNEL: KernelSlot = KernelSlot(MaybeUninit::uninit());

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

/// Marks the dom0 page-table closure and its user leaves.
unsafe fn walk_dom0(dom0_pml4: usize) -> (usize, usize) {
    let mut tables = 0;
    let mut leaves = 0;
    let mut mark_table = |addr: u64| {
        let kinds = kinds();
        let i = index_of(addr);
        assert!(kinds[i] == Kind::Unavailable, "dom0 table page {:#x} is {:?}", addr, kinds[i]);
        kinds[i] = Kind::Dom0Table;
        tables += 1;
    };
    mark_table(dom0_pml4 as u64);
    for l4i in KERNEL_MEM_END_L4INDEX..512 {
        let e4 = entry(dom0_pml4, l4i);
        if e4 & PTE_PRESENT == 0 {
            continue;
        }
        let l3 = (e4 & PTE_ADDR_MASK) as usize;
        mark_table(l3 as u64);
        for l3i in 0..512 {
            let e3 = entry(l3, l3i);
            if e3 & PTE_PRESENT == 0 {
                continue;
            }
            assert!(e3 & PTE_HUGE == 0, "dom0 uses a 1G page");
            let l2 = (e3 & PTE_ADDR_MASK) as usize;
            mark_table(l2 as u64);
            for l2i in 0..512 {
                let e2 = entry(l2, l2i);
                if e2 & PTE_PRESENT == 0 {
                    continue;
                }
                assert!(e2 & PTE_HUGE == 0, "dom0 uses a 2M page");
                let l1 = (e2 & PTE_ADDR_MASK) as usize;
                mark_table(l1 as u64);
                for l1i in 0..512 {
                    let e1 = entry(l1, l1i);
                    if e1 & PTE_PRESENT == 0 {
                        continue;
                    }
                    let leaf = e1 & PTE_ADDR_MASK;
                    let kinds = kinds();
                    let i = index_of(leaf);
                    assert!(kinds[i] == Kind::DomainSpare, "dom0 leaf {:#x} is {:?}", leaf, kinds[i]);
                    kinds[i] = Kind::Dom0Leaf;
                    leaves += 1;
                }
            }
        }
    }
    (tables, leaves)
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

fn new_page(addr: usize, state: PageState, ref_count: usize, owning_container: usize) -> Page {
    Page {
        addr,
        state,
        is_io_page: false,
        ref_count,
        owning_container,
        mappings: Ghost::assume_new(),
        iommu_mappings: Ghost::assume_new(),
        free_list_node_storage: ExternalNode::new(0),
        free_list: 0,
        perm_4k: Tracked::assume_new(),
        perm_2m: Tracked::assume_new(),
        perm_1g: Tracked::assume_new(),
    }
}

/// Physical address of the VT-d root table inside [`KERNEL`] (the kernel image is identity mapped).
pub fn iommu_root_table() -> u64 {
    (&raw const KERNEL) as u64 + veriflat_monolith::kernel::init::KERNEL_IRT_OFFSET as u64
}

/// Builds the verified kernel in [`KERNEL`].
pub unsafe fn init_kernel(boot_info: &BootInfo) {
    let kernel_ptr = (&raw mut KERNEL) as usize;
    log::info!("KernelK: {} bytes at {:#x}; page lock {} bytes", size_of::<KernelK>(), kernel_ptr, size_of::<PageLock>());
    assert!(kernel_ptr % PAGE_SIZE == 0);
    assert!(align_of::<KernelK>() <= PAGE_SIZE);
    assert!(size_of::<PageLockedArray>() == NUM_PAGES * size_of::<PageLock>());
    assert!(size_of::<PcidNeedFlushArray>() == NUM_CPUS * PCID_MAX * size_of::<NeedFlushLock>());
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
    let dom0_pml4 = boot_info.dom0_pml4 as usize;
    let (tables, leaves) = walk_dom0(dom0_pml4);
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

    // 2. Boot singletons.
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

    // 3. Page array, written in place at its final address so free-page node addresses stay valid.
    let page_base = kernel_ptr + offset_of!(KernelK, pg_arr);
    let page_value_offset = size_of::<RwLockInner>().next_multiple_of(align_of::<Page>());
    let mut free_4k_pool: FreePool = LinkedList::new(Some(0), Some(root_container));
    let mut free_2m_pool: FreePool = LinkedList::new(Some(0), Some(root_container));
    let mut free_count = 0usize;
    for i in 0..NUM_PAGES {
        let addr = i * PAGE_SIZE;
        let (state, ref_count) = match kinds[i] {
            Kind::Unavailable => (PageState::Unavailable, 0),
            Kind::Free => (PageState::Free4k { allocator_ptr: Ghost::assume_new(), state: FreePageAllocatorState::GlobalList }, 0),
            Kind::Free2m => (PageState::Free2m { allocator_ptr: Ghost::assume_new(), state: FreePageAllocatorState::GlobalList }, 0),
            Kind::Merged2m => (PageState::Merged2m, 0),
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
        ptr::write(lock_ptr, RwLock::new_unlocked(new_page(addr, state, ref_count, root_container), (), Ghost::assume_new()));
        if kinds[i] == Kind::Free || kinds[i] == Kind::Free2m {
            let page = &mut *((lock_ptr as usize + page_value_offset) as *mut Page);
            assert!(page.addr == addr, "RwLock value offset mismatch");
            let (node_addr, mut node_perm) = page.free_list_node_storage.take();
            node_update_value(node_addr, &mut node_perm, addr);
            if kinds[i] == Kind::Free {
                free_4k_pool.push_tail(node_addr, node_perm);
                free_count += 1;
            } else {
                free_2m_pool.push_tail(node_addr, node_perm);
            }
        }
    }
    let page_array: PageLockedArray = ptr::read(page_base as *const PageLockedArray);
    log::info!("pages: {} free, {} free 2M blocks, {} dom0 tables, {} dom0 leaves", free_count, BOOT_FREE_2M_BLOCKS, tables, leaves);

    // 4. PCID needflush array, written in place.
    let needflush_base = kernel_ptr + offset_of!(KernelK, pcid_needflush);
    for k in 0..NUM_CPUS * PCID_MAX {
        let lock_ptr = (needflush_base + k * size_of::<NeedFlushLock>()) as *mut NeedFlushLock;
        ptr::write(lock_ptr, RwLock::new_unlocked(PcidNeedFlush::new(Ghost::assume_new(), Ghost::assume_new()), (), Ghost::assume_new()));
    }
    let pcid_needflush: PcidNeedFlushArray = ptr::read(needflush_base as *const PcidNeedFlushArray);

    // 5. Default page table and the published per-cpu contexts.
    let default_pagetable = ReadOnlyNode::new(
        PageTable::new(Some(KERNEL_DEFAULT_PCID), Ghost::assume_new(), kernel_pml4, Tracked::assume_new(), KERNEL_MEM_END_L4INDEX, 0),
        Ghost::assume_new(),
    );
    let cpu_published: CpuPublishedArray =
        core::array::from_fn(|_| AtomicPcidCr3::new(kernel_pml4, KERNEL_DEFAULT_PCID, Ghost::assume_new()));

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

    let free_1g_pool: FreePool = LinkedList::new(Some(0), Some(root_container));
    let _ = finish_init_from_boot(
        layout, KERNEL_MEM_END_L4INDEX, &initial_regs, page_array, pcid_needflush, cpu_published, default_pagetable,
        free_4k_pool, free_2m_pool, free_1g_pool,
        Ghost::assume_new(), Ghost::assume_new(), Ghost::assume_new(), Ghost::assume_new(),
        Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(),
        Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(),
        Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(),
        Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(),
        Tracked::assume_new(),
    );
    log::info!("VeriFlat kernel initialized: root container {:#x}, root thread {:#x}", root_container, layout.root_thread);
}
