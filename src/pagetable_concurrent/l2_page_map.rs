use vstd::prelude::*;
verus! {
use crate::*;
use vstd::simple_pptr::*;
use core::sync::atomic::*;

/// PDE bit 9 (AVL) is the 2M-window spin lock. Hardware walks ignore it and `usize2page_entry` drops it, so a
/// locked word decodes to the same entry.
pub const L2_ENTRY_LOCK_MASK: usize = 0x200;

pub ghost enum SpinLockState {
    Some { thread_id: LockThreadId, lock_id: LockToken },
    None,
}

/// Two L2 words that the kernel cannot tell apart: they decode to the same entry. Hardware may set the A/D bits of
/// a published word and the lock bit belongs to `L2LockGhost`; decoding ignores all three.
pub open spec fn l2_word_hw_equiv(a: usize, b: usize) -> bool { usize2page_entry(a) == usize2page_entry(b) }

/// Concrete L2 page-table page whose 512 entries double as the 2M-window spin locks.
///
/// Every word is atomic, so all accesses go through `&self`. The decoded contents live in the separate
/// `L2PageGhost` token and the window-lock owners in the `L2LockGhost` token; both carry the page address.
/// Fields stay private: published writes go only through `set_published_locked` under the window lock, and the
/// lock bit only through `lock`/`unlock`.
#[repr(C)]
pub struct L2PageMap {
    ar: [AtomicUsize; 512],
    addr: Ghost<PageMapPtr>,
}

/// Raw words and decoded entries of one `L2PageMap`. The lock bit of `words` is not tracked here.
pub tracked struct L2PageGhost {
    ghost addr: PageMapPtr,
    ghost words: Seq<usize>,
    ghost spec_seq: Seq<PageEntry>,
}

/// Owner of each window lock bit of one `L2PageMap`. Only `lock`/`unlock` change it.
pub tracked struct L2LockGhost {
    ghost addr: PageMapPtr,
    ghost lock_states: Seq<SpinLockState>,
}

impl L2PageGhost {
    pub closed spec fn addr(&self) -> PageMapPtr { self.addr }

    pub closed spec fn wf(&self) -> bool {
        &&& self.words.len() == 512
        &&& self.spec_seq.len() == 512
        &&& forall|i: usize| #![trigger usize2page_entry(self.words.spec_index(i as int))] pei_valid(i) ==> (usize2page_entry(self.words.spec_index(i as int)) =~= self.spec_seq.spec_index(i as int))
        &&& forall|i: usize| #![trigger self.spec_seq.spec_index(i as int).perm.kernel_present] pei_valid(i) && self.spec_seq.spec_index(i as int).perm.kernel_present ==> mem_valid(self.spec_seq.spec_index(i as int).addr)
    }

    pub closed spec fn view(&self) -> Seq<PageEntry> { self.spec_seq }

    pub open spec fn spec_index(&self, index: usize) -> PageEntry
        recommends
            pei_valid(index),
    {
        self.view().spec_index(index as int)
    }

    pub open spec fn is_empty(&self) -> bool
        recommends
            self.wf(),
    {
        forall|i: usize| #![trigger self.spec_index(i)] pei_valid(i) ==> self.spec_index(i).is_empty()
    }
}

impl L2LockGhost {
    pub closed spec fn addr(&self) -> PageMapPtr { self.addr }
    pub closed spec fn wf(&self) -> bool { self.lock_states.len() == 512 }

    pub closed spec fn lock_state(&self, index: usize) -> SpinLockState
        recommends
            pei_valid(index),
    {
        self.lock_states.spec_index(index as int)
    }

    pub open spec fn locked(&self, index: usize) -> bool { self.lock_state(index) is Some }

    pub open spec fn locked_by_thread(&self, index: usize, thread_id: LockThreadId) -> bool {
        &&& self.lock_state(index) is Some
        &&& self.lock_state(index)->Some_thread_id == thread_id
    }

    pub open spec fn locked_by(&self, index: usize, lctx: &LocalContext) -> bool { self.locked_by_thread(index, lctx.thread_id()) }

    pub open spec fn lock_perm_match(&self, index: usize, lock_perm: &LockPerm) -> bool {
        &&& self.lock_state(index) is Some
        &&& self.lock_state(index)->Some_thread_id == lock_perm.thread_id()
        &&& self.lock_state(index)->Some_lock_id == lock_perm.lock_id()
    }
}

impl L2PageMap {
    pub closed spec fn addr(&self) -> PageMapPtr { self.addr.view() }

    pub fn get(&self, Tracked(g): Tracked<&L2PageGhost>, index: usize) -> (ret: PageEntry)
        requires
            g.wf(),
            g.addr() == self.addr(),
            pei_valid(index),
        ensures
            ret =~= g.spec_index(index),
    {
        usize2page_entry(self.load_word_acquire(Tracked(g), index))
    }

    /// TCB: acquire-load of one entry word; pairs with the release stores and CAS of other threads. The loaded word
    /// may differ from the recorded one only in bits that decoding ignores.
    #[verifier::external_body]
    fn load_word_acquire(&self, Tracked(g): Tracked<&L2PageGhost>, index: usize) -> (ret: usize)
        requires
            g.addr() == self.addr(),
            g.wf(),
            pei_valid(index),
        ensures
            l2_word_hw_equiv(ret, g.words.spec_index(index as int)),
    {
        self.ar[index].load(Ordering::Acquire)
    }

    /// TCB: release-store of one entry word. The stored lock bit must match the recorded lock owner, so a store
    /// never takes or drops a window lock.
    #[verifier::external_body]
    fn store_word_release(&self, Tracked(g): Tracked<&mut L2PageGhost>, Tracked(lk): Tracked<&L2LockGhost>, index: usize, word: usize)
        requires
            old(g).addr() == self.addr(),
            old(g).wf(),
            lk.addr() == self.addr(),
            lk.wf(),
            pei_valid(index),
            (word & L2_ENTRY_LOCK_MASK != 0) == lk.locked(index),
        ensures
            final(g).addr == old(g).addr,
            final(g).words =~= old(g).words.update(index as int, word),
            final(g).spec_seq == old(g).spec_seq,
    {
        self.ar[index].store(word, Ordering::Release)
    }

    /// TCB: spin until this thread owns the window lock bit of entry `index`; the bit is free when this thread takes it.
    #[verifier::external_body]
    pub(super) fn lock(&self, Tracked(lk): Tracked<&mut L2LockGhost>, index: usize, Tracked(lctx): Tracked<&mut LocalContext>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>) -> (ret: Tracked<LockPerm>)
        requires
            old(lk).wf(),
            old(lk).addr() == self.addr(),
            pei_valid(index),
            !old(lk).locked_by(index, old(lctx)),
            old(lctx).kernel_view_locking_state() is Acquire,
            old(lctx).lock_id_acyclic(lock_id.view()),
        ensures
            final(lk).wf(),
            final(lk).addr() == old(lk).addr(),
            old(lk).lock_state(index) is None,
            forall|i: usize| #![trigger final(lk).lock_state(i)] pei_valid(i) && i != index ==> final(lk).lock_state(i) == old(lk).lock_state(i),
            final(lk).lock_state(index) == (SpinLockState::Some { thread_id: final(lctx).thread_id(), lock_id: ret.view().lock_id() }),
            ret.view().state() is WriteLock,
            ret.view().ordering_lock_id() == lock_id.view(),
            ret.view().thread_id() == final(lctx).thread_id(),
            lock_ensures(old(lctx), final(lctx), lock_id.view(), obj_id.view()),
    {
        let slot = &self.ar[index];
        loop {
            let v = slot.load(Ordering::Relaxed);
            if v & L2_ENTRY_LOCK_MASK == 0 && slot.compare_exchange_weak(v, v | L2_ENTRY_LOCK_MASK, Ordering::Acquire, Ordering::Relaxed).is_ok() { break; }
            core::hint::spin_loop();
        }
        Tracked::assume_new()
    }

    /// TCB: release the window lock bit of entry `index`; the entry otherwise stays as published.
    #[verifier::external_body]
    pub(super) fn unlock(&self, Tracked(lk): Tracked<&mut L2LockGhost>, index: usize, Tracked(lctx): Tracked<&mut LocalContext>, lp: Tracked<LockPerm>, lock_id: Ghost<LockId>, obj_id: Ghost<KernelObjId>)
        requires
            old(lk).wf(),
            old(lk).addr() == self.addr(),
            pei_valid(index),
            old(lk).locked_by(index, old(lctx)),
            lp.view().state() is WriteLock,
            lp.view().thread_id() == old(lctx).thread_id(),
            old(lk).lock_perm_match(index, &lp.view()),
            old(lctx).lock_entry_contains(lock_id.view(), obj_id.view()),
        ensures
            final(lk).wf(),
            final(lk).addr() == old(lk).addr(),
            forall|i: usize| #![trigger final(lk).lock_state(i)] pei_valid(i) && i != index ==> final(lk).lock_state(i) == old(lk).lock_state(i),
            final(lk).lock_state(index) is None,
            unlock_ensures(old(lctx), final(lctx), obj_id.view(), lock_id.view()),
    {
        self.ar[index].fetch_and(!L2_ENTRY_LOCK_MASK, Ordering::Release);
    }

    /// Publish a new entry while this thread holds the window lock of `index`; the stored word keeps the lock bit.
    pub(super) fn set_published_locked(&self, Tracked(g): Tracked<&mut L2PageGhost>, Tracked(lk): Tracked<&L2LockGhost>, index: usize, value: PageEntry, Tracked(lctx): Tracked<&mut LocalContext>)
        requires
            old(g).wf(),
            old(g).addr() == self.addr(),
            lk.wf(),
            lk.addr() == self.addr(),
            pei_valid(index),
            lk.locked_by(index, old(lctx)),
            mem_valid(value.addr),
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
            final(g).wf(),
            final(g).addr() == old(g).addr(),
            final(g).view() =~= old(g).view().update(index as int, value),
            forall|i: usize| #![trigger final(g).spec_index(i)] pei_valid(i) && i != index ==> final(g).spec_index(i) =~= old(g).spec_index(i),
            final(g).spec_index(index) =~= value,
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
        self.store_word_release(Tracked(&mut *g), Tracked(lk), index, w);
        proof { g.spec_seq = g.spec_seq.update(index as int, value); }
    }
}

/// TCB: retype a free 4K page into an all-empty L2 page and mint its two ghost tokens. Windows `lo..=hi` start locked by this
/// thread with the ordering ids of windows `(l4i, l3i, lo..=hi)` of `root`; every other window starts unlocked. Their lock bits
/// are set before the page is published. No `lock_id_acyclic` is needed: the page is reachable only through the L3 entry that
/// this thread publishes under the big write lock, so no thread can wait on these windows before that lock is downgraded.
#[verifier::external_body]
pub fn page_perm_to_l2_page_map(page_ptr: PagePtr, Tracked(page_perm): Tracked<PagePerm4k>, lo: L2Index, hi: L2Index, Tracked(lctx): Tracked<&mut LocalContext>,
    Ghost(root): Ghost<RwLockPageTableRoot>, Ghost(l4i): Ghost<L4Index>, Ghost(l3i): Ghost<L3Index>)
    -> (ret: (PageMapPtr, Tracked<PointsTo<L2PageMap>>, Tracked<L2PageGhost>, Tracked<L2LockGhost>, Tracked<Map<L2Index, LockPerm>>))
    requires
        page_perm.is_init(),
        page_perm.addr() == page_ptr,
        pei_valid(lo) && pei_valid(hi) && lo <= hi,
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        ret.0 == page_ptr,
        ret.1.view().addr() == ret.0,
        ret.1.view().is_init(),
        ret.1.view().value().addr() == ret.0,
        ret.2.view().addr() == ret.0,
        ret.2.view().wf(),
        forall|i: usize|
            #![trigger ret.2.view().spec_index(i).is_empty()]
            #![trigger ret.2.view().spec_index(i).perm.present]
            #![trigger ret.2.view().spec_index(i).perm.ps]
            #![trigger ret.2.view().spec_index(i).perm.kernel_present]
            pei_valid(i) ==> ret.2.view().spec_index(i).is_empty(),
        ret.3.view().addr() == ret.0,
        ret.3.view().wf(),
        forall|i: usize| #![trigger ret.3.view().lock_state(i)] pei_valid(i) && !(lo <= i <= hi) ==> ret.3.view().lock_state(i) is None,
        forall|i: usize| #![trigger ret.4.view().dom().contains(i)] ret.4.view().dom().contains(i) == (lo <= i <= hi),
        forall|i: usize| #![trigger ret.4.view().index(i)] #![trigger ret.3.view().lock_state(i)] lo <= i <= hi ==> {
            &&& ret.3.view().lock_state(i) == (SpinLockState::Some { thread_id: final(lctx).thread_id(), lock_id: ret.4.view().index(i).lock_id() })
            &&& ret.4.view().index(i).state() is WriteLock
            &&& ret.4.view().index(i).ordering_lock_id() == window_lock_id(root, l4i, l3i, i)
            &&& ret.4.view().index(i).thread_id() == final(lctx).thread_id()
        },
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Acquire,
        nonwindow_typed_lock_maps_unchanged(old(lctx), final(lctx)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().dom().contains((p, w))]
            final(lctx).pagetable_window_lock_map().dom().contains((p, w)) == (old(lctx).pagetable_window_lock_map().dom().contains((p, w))
                || (p == root && w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i && lo <= spec_v2l2index(w.va) <= hi)),
        forall|p: RwLockPageTableRoot, w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((p, w))]
            old(lctx).pagetable_window_lock_map().dom().contains((p, w)) && !(p == root && w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i && lo <= spec_v2l2index(w.va) <= hi)
                ==> final(lctx).pagetable_window_lock_map().index((p, w)) == old(lctx).pagetable_window_lock_map().index((p, w)),
        forall|w: WindowVa| #![trigger final(lctx).pagetable_window_lock_map().index((root, w))]
            w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i && lo <= spec_v2l2index(w.va) <= hi
                ==> final(lctx).pagetable_window_lock_map().index((root, w)) == (TypedHeldLock { lock_id: window_lock_id_of(root, w), mode: TypedLockMode::Write }),
{
    unsafe {
        core::ptr::write_bytes(page_ptr as *mut u8, 0u8, PAGE_SZ_4K);
        core::slice::from_raw_parts_mut((page_ptr as *mut usize).add(lo), hi - lo + 1).fill(L2_ENTRY_LOCK_MASK);
    }
    (page_ptr, Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new(), Tracked::assume_new())
}

/// TCB: an unlocked L2 page that its page table no longer links is an ordinary 4K page again; its bytes stay
/// as they are. The inverse of `page_perm_to_l2_page_map`.
#[verifier::external_body]
pub fn l2_page_map_to_page_perm(page_map_ptr: PageMapPtr, Tracked(perm): Tracked<PointsTo<L2PageMap>>, Tracked(g): Tracked<L2PageGhost>, Tracked(lk): Tracked<L2LockGhost>) -> (ret: Tracked<PagePerm4k>)
    requires
        perm.addr() == page_map_ptr,
        perm.is_init(),
        g.addr() == page_map_ptr,
        g.wf(),
        lk.addr() == page_map_ptr,
        forall|i: usize| #![trigger lk.lock_state(i)] pei_valid(i) ==> lk.lock_state(i) is None,
    ensures
        ret.view().is_init(),
        ret.view().addr() == page_map_ptr,
{
    Tracked::assume_new()
}
} // verus!
