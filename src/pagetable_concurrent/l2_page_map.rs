use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;
use core::sync::atomic::*;
use super::l2_entry_lock_t::l2_entry_store_release;

/// PDE bit 9 (AVL) is the 2M-window spin lock. Hardware walks ignore it and `usize2page_entry` drops it, so a
/// locked word decodes to the same entry.
pub const L2_ENTRY_LOCK_MASK: usize = 0x200;

/// Two L2 words that the kernel cannot tell apart: they decode to the same entry. Hardware may set the A/D bits of
/// a published word and the lock bit belongs to the entry's locking thread; decoding ignores all three.
pub open spec fn l2_word_hw_equiv(a: usize, b: usize) -> bool { usize2page_entry(a) == usize2page_entry(b) }

/// One entry of an L2 page-table page; its word doubles as the spin lock of the entry's 2M window.
///
/// `entry` is the decoded word and `locking_thread` the holder of the lock bit; the TCB word primitives keep both in
/// step with `word`. `l1` owns the L1 page of a non-huge entry: the page it links, or, once `hide_l1_page` cleared the
/// present bit, the page that waits in the locked window for `unlink_hidden_l1_page`. Only the TCB primitives of
/// `l2_entry_lock_t` see `word`: it changes only through `l2_entry_lock`, `l2_entry_unlock` and
/// `l2_entry_store_release`, and `l1` moves only through `l2_entry_take_l1*` and `l2_entry_put_l1*`.
#[repr(C)]
pub struct L2EntryLock {
    pub(super) word: AtomicUsize,
    l1: Tracked<Option<PointsTo<PageMap>>>,
    entry: Ghost<PageEntry>,
    locking_thread: Ghost<RwLockState>,
}

/// Concrete L2 page-table page whose 512 entries double as the 2M-window spin locks.
#[repr(C)]
pub struct L2PageMap {
    pub(super) ar: [L2EntryLock; 512],
    addr: Ghost<PageMapPtr>,
}

impl L2EntryLock {
    pub closed spec fn view(&self) -> PageEntry { self.entry.view() }
    pub closed spec fn locking_thread(&self) -> RwLockState { self.locking_thread.view() }
    pub closed spec fn l1(&self) -> Option<PointsTo<PageMap>> { self.l1.view() }

    /// A kernel-present entry holds a valid frame, an owned L1 page sits at the address of its non-huge entry, and the
    /// window lock is never read-held.
    pub open spec fn inv(&self) -> bool {
        &&& self.view().perm.kernel_present ==> mem_valid(self.view().addr)
        &&& self.l1() is Some ==> self.l1()->Some_0.addr() == self.view().addr && !self.view().perm.ps
        &&& !(self.locking_thread() is Read)
    }

    /// TCB: acquire-load of the entry word; pairs with the release stores and CAS of other threads. The loaded word
    /// may differ from the recorded one only in bits that decoding ignores.
    #[verifier::external_body]
    fn load_acquire(&self) -> (w: usize)
        ensures
            usize2page_entry(w) == self.view(),
    {
        self.word.load(Ordering::Acquire)
    }

    pub fn get(&self) -> (e: PageEntry)
        ensures
            e == self.view(),
    {
        usize2page_entry(self.load_acquire())
    }

    /// The L1 page slot of this entry, for reading.
    pub fn borrow_l1(&self) -> (r: &Tracked<Option<PointsTo<PageMap>>>)
        ensures
            r.view() == self.l1(),
    {
        &self.l1
    }
}

/// The window lock of a free L2 entry passes to `lctx`'s thread under `lock_perm`; the entry and its L1 page stay.
pub open spec fn window_wlock_ensures(old: L2EntryLock, new: L2EntryLock, lock_id: LockId, lctx: &LocalContext, lock_perm: LockPerm) -> bool {
    &&& new.locking_thread() == RwLockState::Write { thread_id: lctx.thread_id(), lock_id: lock_perm.lock_id() }
    &&& new.view() == old.view()
    &&& new.l1() == old.l1()
    &&& old.locking_thread() is None
    &&& lock_perm.state() is WriteLock
    &&& lock_perm.ordering_lock_id() == lock_id
    &&& lock_perm.thread_id() == lctx.thread_id()
}

/// The window lock of an L2 entry is released; the entry and its L1 page stay.
pub open spec fn window_wunlock_ensures(old: L2EntryLock, new: L2EntryLock) -> bool {
    &&& new.locking_thread() is None
    &&& new.view() == old.view()
    &&& new.l1() == old.l1()
}

impl L2PageMap {
    pub closed spec fn addr(&self) -> PageMapPtr { self.addr.view() }
    pub closed spec fn entry_lock(&self, i: L2Index) -> L2EntryLock { self.ar.view().spec_index(i as int) }

    pub open spec fn wf(&self) -> bool { forall|i: L2Index| #![trigger self.entry_lock(i)] pei_valid(i) ==> self.entry_lock(i).inv() }

    pub fn borrow_entry_lock(&self, i: L2Index) -> (r: &L2EntryLock)
        requires
            pei_valid(i),
        ensures
            *r == self.entry_lock(i),
    {
        &self.ar[i]
    }
}

/// Publish `value` in entry `i` of the L2 page at `pptr` while this thread holds the entry's lock; the stored word
/// keeps the lock bit.
pub fn l2_entry_set_published_locked(pptr: &PPtr<L2PageMap>, Tracked(perm): Tracked<&mut PointsTo<L2PageMap>>, i: L2Index, Tracked(lp): Tracked<&LockPerm>, value: PageEntry,
    Tracked(lctx): Tracked<&mut LocalContext>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        pei_valid(i),
        old(perm).value().entry_lock(i).locking_thread() == (RwLockState::Write { thread_id: lp.thread_id(), lock_id: lp.lock_id() }),
        mem_valid(value.addr),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().addr() == old(perm).value().addr(),
        forall|j: L2Index| #![trigger final(perm).value().entry_lock(j)] j != i ==> final(perm).value().entry_lock(j) == old(perm).value().entry_lock(j),
        final(perm).value().entry_lock(i).view() == value,
        final(perm).value().entry_lock(i).locking_thread() == old(perm).value().entry_lock(i).locking_thread(),
        final(perm).value().entry_lock(i).l1() == old(perm).value().entry_lock(i).l1(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
{
    proof { lctx.enter_kernel_view_release(); }
    let u = page_entry2usize(&value);
    let w = u | L2_ENTRY_LOCK_MASK;
    assert({
        &&& w & MEM_MASK as usize == u & MEM_MASK as usize
        &&& (w & PAGE_ENTRY_PRESENT_MASK as usize != 0) == (u & PAGE_ENTRY_PRESENT_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_PS_MASK as usize != 0) == (u & PAGE_ENTRY_PS_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_WRITE_MASK as usize != 0) == (u & PAGE_ENTRY_WRITE_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_EXECUTE_MASK as usize != 0) == (u & PAGE_ENTRY_EXECUTE_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_USER_MASK as usize != 0) == (u & PAGE_ENTRY_USER_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_KERNEL_PRESENT_MASK as usize != 0) == (u & PAGE_ENTRY_KERNEL_PRESENT_MASK as usize != 0)
        &&& w & L2_ENTRY_LOCK_MASK != 0
    }) by (bit_vector)
        requires
            w == u | L2_ENTRY_LOCK_MASK,
    ;
    l2_entry_store_release(pptr, Tracked(&mut *perm), i, w);
}

/// Publish `value` in entry `i` of the L2 page at `pptr` while no thread holds the entry's lock (the caller holds the table's big
/// lock in write mode); the stored word keeps the lock bit clear.
pub fn l2_entry_set_published_unlocked(pptr: &PPtr<L2PageMap>, Tracked(perm): Tracked<&mut PointsTo<L2PageMap>>, i: L2Index, value: PageEntry, Tracked(lctx): Tracked<&mut LocalContext>)
    requires
        pptr.addr() == old(perm).addr(),
        old(perm).is_init(),
        pei_valid(i),
        old(perm).value().entry_lock(i).locking_thread() is None,
        mem_valid(value.addr),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        final(perm).addr() == old(perm).addr(),
        final(perm).is_init(),
        final(perm).value().addr() == old(perm).value().addr(),
        forall|j: L2Index| #![trigger final(perm).value().entry_lock(j)] j != i ==> final(perm).value().entry_lock(j) == old(perm).value().entry_lock(j),
        final(perm).value().entry_lock(i).view() == value,
        final(perm).value().entry_lock(i).locking_thread() == old(perm).value().entry_lock(i).locking_thread(),
        final(perm).value().entry_lock(i).l1() == old(perm).value().entry_lock(i).l1(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
{
    proof { lctx.enter_kernel_view_release(); }
    let u = page_entry2usize(&value);
    let w = u & !L2_ENTRY_LOCK_MASK;
    assert({
        &&& w & MEM_MASK as usize == u & MEM_MASK as usize
        &&& (w & PAGE_ENTRY_PRESENT_MASK as usize != 0) == (u & PAGE_ENTRY_PRESENT_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_PS_MASK as usize != 0) == (u & PAGE_ENTRY_PS_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_WRITE_MASK as usize != 0) == (u & PAGE_ENTRY_WRITE_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_EXECUTE_MASK as usize != 0) == (u & PAGE_ENTRY_EXECUTE_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_USER_MASK as usize != 0) == (u & PAGE_ENTRY_USER_MASK as usize != 0)
        &&& (w & PAGE_ENTRY_KERNEL_PRESENT_MASK as usize != 0) == (u & PAGE_ENTRY_KERNEL_PRESENT_MASK as usize != 0)
        &&& w & L2_ENTRY_LOCK_MASK == 0
    }) by (bit_vector)
        requires
            w == u & !L2_ENTRY_LOCK_MASK,
    ;
    l2_entry_store_release(pptr, Tracked(&mut *perm), i, w);
}

/// TCB: retype a free 4K page into an L2 page whose 512 entries are empty, unlocked and own no L1 page.
#[verifier::external_body]
pub fn page_perm_to_l2_page_map(pg_ptr: PagePtr, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: Tracked<PointsTo<L2PageMap>>)
    requires
        page_perm.is_init(),
        page_perm.addr() == pg_ptr,
    ensures
        ret.view().addr() == pg_ptr,
        ret.view().is_init(),
        ret.view().value().addr() == pg_ptr,
        ret.view().value().wf(),
        forall|i: L2Index| #![trigger ret.view().value().entry_lock(i)] pei_valid(i) ==> {
            &&& ret.view().value().entry_lock(i).view().is_empty()
            &&& ret.view().value().entry_lock(i).locking_thread() is None
            &&& ret.view().value().entry_lock(i).l1() is None
        },
{
    unsafe { core::ptr::write_bytes(pg_ptr as *mut u8, 0u8, PAGE_SZ_4K); }
    Tracked::assume_new()
}

/// TCB: an unlocked L2 page that its page table no longer links, that owns no L1 page, and that no usable
/// paging-structure cache names is an ordinary 4K page again; its bytes stay as they are, and the next retype zeroes
/// them. The inverse of `page_perm_to_l2_page_map`.
#[verifier::external_body]
pub fn l2_page_map_to_page_perm(Tracked(perm): Tracked<PointsTo<L2PageMap>>, cpu_tlb: &CpuTLB, cpu_arr: &CpuLockedArray, needflush: &PcidNeedFlushArray) -> (ret: Tracked<PagePerm4k>)
    requires
        perm.is_init(),
        perm.value().addr() == perm.addr(),
        forall|i: L2Index| #![trigger perm.value().entry_lock(i)] pei_valid(i) ==> perm.value().entry_lock(i).locking_thread() is None && perm.value().entry_lock(i).l1() is None,
        table_page_unreferenced_by_structure_caches(*cpu_tlb, *cpu_arr, *needflush, perm.addr()),
    ensures
        ret.view().is_init(),
        ret.view().addr() == perm.addr(),
{
    let _ = (cpu_tlb, cpu_arr, needflush);
    Tracked::assume_new()
}
} // verus!
