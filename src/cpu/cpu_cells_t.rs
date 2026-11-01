use vstd::prelude::*;
use vstd::simple_pptr::*;
use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use crate::*;

/// Memory of the cpu locks. Only raw addresses reach it; the cpu array's points-to tokens own its cells.
struct CpuCells(UnsafeCell<MaybeUninit<[RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>; NUM_CPUS]>>);

// Every access goes through a cell's lock guard or its owning token.
unsafe impl Sync for CpuCells {}

static CPU_CELLS: CpuCells = CpuCells(UnsafeCell::new(MaybeUninit::uninit()));

// Layout contract: every cpu lock cell starts and ends on a cache-line boundary, so one cpu's switch-time stores never
// share a line with the next cpu's lock word.
const _: () = assert!(core::mem::align_of::<RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>>() % 64 == 0);
const _: () = assert!(core::mem::size_of::<RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>>() % 64 == 0);

verus! {
/// Address of the first cpu lock cell.
pub uninterp spec fn cpu_cells_base_spec() -> usize;

/// TCB: the address of the first cpu lock cell.
#[verifier::external_body]
pub fn cpu_cells_base() -> (ret: usize)
    ensures
        ret == cpu_cells_base_spec(),
{
    CPU_CELLS.0.get() as usize
}

impl TokenCellBase for RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE> {
    open spec fn cell_base_spec() -> usize { cpu_cells_base_spec() }
    fn cell_base() -> (ret: usize) { cpu_cells_base() }
}

/// TCB: write `lock` into cpu lock cell `i` and mint the cell's points-to token; init only, once per cell.
#[verifier::external_body]
pub(crate) fn cpu_cell_init(i: usize, lock: RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>) -> (ret: Tracked<PointsTo<RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>>>)
    requires
        i < NUM_CPUS,
    ensures
        ret.view().addr() == lock_cell_addr::<RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>>(cpu_cells_base_spec(), i as int),
        ret.view().is_init(),
        ret.view().value() == lock,
{
    unsafe { (CPU_CELLS.0.get() as *mut RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>).add(i).write(lock); }
    Tracked::assume_new()
}
}
