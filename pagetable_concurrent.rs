use vstd::prelude::*;
verus! {

pub enum SpinLockState {
    Some { thread_id:LockThreadId,lock_id: LockToken },
    None,
}
pub struct L2PageEntryGhost {
    pub addr: PAddr,
    pub perm: PageEntryPerm,
    pub lock_state: SpinLockState
}

// TCB L2PageEntry acts like a spin lock.
pub struct L2PageEntry{
    pub ar: usize,
    pub spec_entry: L2PageEntryGhost,
}
pub struct PageTableHigher {
    pub cr3: PageTableRoot,
    pub pcid: Pcid,
    pub kernel_l4_end: usize,
    pub l4_table: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
    pub l3_rev_map: Ghost<Map<PageMapPtr, (L4Index)>>,
    pub l3_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
}

impl PageTableHigher{
    pub spec fn page_closure() -> Set<PagePtr>; 
}

pub struct PageEntryL2{
    pub l2_rev: (L4Index, L3Index),
    pub l2_entry: L2PageEntry,
    pub l1_rev_map: Ghost<Map<PageMapPtr, (L4Index, L3Index, L2Index)>>,
    pub l1_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>,
}
pub struct PageEntryL2Map{
    ar: Array<PagetableL2, 512>
}
pub struct PagetableLower{
    ar: UnlockedMap<PagePtr: PointsTo<PageEntryL2Map>>,
}
impl PagetableLower{
    pub spec fn page_closure() -> Set<PagePtr>; // UnlockedMap dom + their l1_tables.dom
}
pub struct PagetableConcurrent{
    higher: RwLock<PageTableHigher>,
    lower_map: PagetableLower, 
}

///
/// PagetableConcurrent 的接口，懒得想了。。。
///

pub ghost enum SpinLockStateU { Unlocked, Locked }
pub ghost struct PageTableConcurrentU {
    pub lock_state: LockStateU,
    pub split_lock_map: Map<VAddr, Some(SpinLockStateU)>, // each 2M aligned VA is one entry if the L2 entry exists, it's Some.
    pub mapping_4k: Map<VAddr, MapEntry>,
    pub mapping_2m: Map<VAddr, MapEntry>,
    pub mapping_1g: Map<VAddr, MapEntry>,
}

} // verus!
