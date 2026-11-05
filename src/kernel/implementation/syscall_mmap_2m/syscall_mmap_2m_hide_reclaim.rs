use vstd::prelude::*;
use crate::*;
use super::syscall_mmap_2m_spec::*;
use super::syscall_mmap_2m_trace::*;

verus! {
/// Whether the L2 entry of the 2M window of `va` in the read-held page table `pagetable_ptr` links an L1 page.
fn mmap_2m_window_links_l1(krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&LocalContext>, pagetable_perm: Tracked<&LockPerm>) -> (ret: bool)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        spec_va_2m_valid(va),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == lctx.thread_id(),
        krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
    ensures ret == whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l2(spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va)) is Some,
{
    proof {
        spec_va_2m_valid_index_roundtrip(va);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    }
    let indices = va2index(va);
    let pt = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), pagetable_perm);
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    pt.get_entry_l2(Tracked(lower), indices.0, indices.1, indices.2, &l3).is_some()
}

/// The L2 page and the L2 entry word of the held 2M window of `va` in the read-held page table `pagetable_ptr`.
fn mmap_2m_window_l2_word(krnl: &KernelK, pagetable_ptr: RwLockPageTableRoot, va: VAddr, Tracked(lctx): Tracked<&LocalContext>, pagetable_perm: Tracked<&LockPerm>)
    -> (ret: (PageMapPtr, PageEntry))
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        krnl.pt_mp.dom().contains(pagetable_ptr),
        spec_va_2m_valid(va),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).kernel_l4_end() <= spec_v2l4index(va),
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va)) is Some,
        whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).window_view(window_of(va)).lock_state is Write,
        typed_lock_map_contains_mode(lctx.pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_perm.view().state() is ReadLock,
        pagetable_perm.view().thread_id() == lctx.thread_id(),
        krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(lctx.thread_id(), pagetable_perm.view().lock_id()),
    ensures
        ({
            let table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
            &&& ret.0 == table.spec_resolve_mapping_l3(spec_v2l4index(va), spec_v2l3index(va))->0.addr
            &&& ret.1 == table.window_view(window_of(va)).l2_entry
            &&& ret.1.perm.kernel_present && !ret.1.perm.present && !ret.1.perm.ps ==> table.lower.l2_entry_hides_l1(ret.0, spec_v2l2index(va))
            &&& table.window_view(window_of(va)).l1_table is Some ==> !ret.1.perm.ps && (ret.1.perm.present || ret.1.perm.kernel_present)
        }),
{
    let ghost table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    proof {
        spec_va_2m_valid_index_roundtrip(va);
        pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        krnl.pt_mp.typed_lock_map_aligned_read_at(lctx.pagetable_lock_map(), lctx.thread_id(), pagetable_ptr);
        pagetable_hidden_l1_only_when_locked_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        table.higher.spec_resolve_mapping_l3_some_implies_spec_held_l3_eq(spec_v2l4index(va), spec_v2l3index(va));
    }
    let indices = va2index(va);
    let pt = krnl.pt_mp.borrow_typed(pagetable_ptr, Ghost(lctx.pagetable_lock_map()), Tracked(lctx), pagetable_perm);
    let tracked lower = krnl.pt_lower.borrow().tracked_borrow(pagetable_ptr);
    let l4 = pt.get_entry_l4(indices.0).unwrap();
    let l3 = pt.get_entry_l3(indices.0, indices.1, &l4).unwrap();
    let word = pt.get_l2_entry_word_write_held(Tracked(lower), indices.0, indices.1, indices.2, &l3);
    (l3.addr, word)
}

/// Hide the L1 page that each held 2M window of `va_range` in the read-held page table `pagetable_ptr` links: such a window
/// keeps its empty L1 page behind a non-present L2 entry and lists every CPU stale. Records no step and returns whether any
/// window hid its page; when none did, nothing changed.
pub(super) fn mmap_2m_hide_linked_l1_range(
    krnl: &mut KernelK, va_range: &VaRange2M, pagetable_ptr: RwLockPageTableRoot, Ghost(t4k): Ghost<WholePageTable<PT_TYPE>>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(window_perms): Tracked<&Map<WindowVa, LockPerm>>,
) -> (hidden: bool)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, old(lctx).cpu_id()),
        old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
        old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        va_range.wf(),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus is None,
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            let v = va_range.view()[j];
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& window_of(v).va == v
            &&& old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(v)))
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_of(v)), TypedLockMode::Write)
            &&& window_perms.dom().contains(window_of(v))
            &&& table.window_view(window_of(v)).lock_state == (RwLockState::Write { thread_id: window_perms.index(window_of(v)).thread_id(), lock_id: window_perms.index(window_of(v)).lock_id() })
            &&& table.kernel_l4_end() <= spec_v2l4index(v)
            &&& table.spec_resolve_mapping_l3(spec_v2l4index(v), spec_v2l3index(v)) is Some
            &&& !table.lower.l2_entry_hides_l1(table.window_l2_page(spec_v2l4index(v), spec_v2l3index(v)), spec_v2l2index(v))
            &&& !table.mapping_2m().dom().contains(v)
            &&& forall|l1i: L1Index| #![trigger t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(v), spec_v2l3index(v), spec_v2l2index(v), l1i)))]
                pei_valid(l1i) ==> !t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(v), spec_v2l3index(v), spec_v2l2index(v), l1i)))
        },
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
    ensures
        final(steps).view() == old(steps).view(),
        final(steps).snapshot_k() == *final(krnl),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
        final(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
        held_locks_order_below(final(krnl), final(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        forall|c: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(c)] old(lctx).cpu_lock_map().dom().contains(c) ==> final(krnl).cpu_arr.spec_index(c).view() == old(krnl).cpu_arr.spec_index(c).view(),
        forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t)
            ==> (old(krnl).thrd_mp.dom().contains(t) ==> final(krnl).thrd_mp.dom().contains(t)) && final(krnl).thrd_mp.spec_index(t) == old(krnl).thrd_mp.spec_index(t),
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        !hidden ==> *final(krnl) == *old(krnl) && *final(lctx) == *old(lctx),
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))
            ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus is None
                || whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus == Some(Set::range(0usize, NUM_CPUS)),
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            let v = va_range.view()[j];
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.window_view(window_of(v)).lock_state == pre.window_view(window_of(v)).lock_state
            &&& !(post.window_view(window_of(v)).l2_entry.perm.present && !post.window_view(window_of(v)).l2_entry.perm.ps)
            &&& !hidden ==> post.window_view(window_of(v)).l1_table is None
            &&& !post.mapping_2m().dom().contains(v)
            &&& post.window_view(window_of(v)).l1_table is Some && !post.window_view(window_of(v)).l2_entry.perm.present
                ==> forall|l1i: L1Index| #![trigger post.window_view(window_of(v)).l1_table->Some_0.value().spec_index(l1i)] pei_valid(l1i) ==> !post.window_view(window_of(v)).l1_table->Some_0.value().spec_index(l1i).perm.kernel_present
        },
{
    let ghost t0 = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let mut hidden = false;
    let mut i: usize = 0;
    while i < va_range.len
        invariant
            steps.view() == old(steps).view(),
            steps.snapshot_k() == *krnl,
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            index_valid(NUM_CPUS, old(lctx).cpu_id()),
            old(lctx).cpu_lock_map().dom().contains(old(lctx).cpu_id()),
            old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int] is InStep,
            krnl.cpu_op.view().view()[old(lctx).cpu_id() as int] == old(krnl).cpu_op.view().view()[old(lctx).cpu_id() as int],
            krnl.cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view() == old(krnl).cpu_hw_cr3_pcid[old(lctx).cpu_id() as int].view(),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            forall|c: CpuId| #![trigger old(lctx).cpu_lock_map().dom().contains(c)] old(lctx).cpu_lock_map().dom().contains(c) ==> krnl.cpu_arr.spec_index(c).view() == old(krnl).cpu_arr.spec_index(c).view(),
            forall|t: RwLockThreadPtr| #![trigger old(lctx).thread_lock_map().dom().contains(t)] old(lctx).thread_lock_map().dom().contains(t)
                ==> (old(krnl).thrd_mp.dom().contains(t) ==> krnl.thrd_mp.dom().contains(t)) && krnl.thrd_mp.spec_index(t) == old(krnl).thrd_mp.spec_index(t),
            krnl.pt_mp.dom().contains(pagetable_ptr),
            krnl.pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            pagetable_lock_perm.state() is ReadLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            t0 == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr),
            forall|w: WindowVa, u: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                    && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                    &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                    &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
                },
            forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
                let v = va_range.view()[j];
                &&& forall|l1i: L1Index| #![trigger t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(v), spec_v2l3index(v), spec_v2l2index(v), l1i)))]
                    pei_valid(l1i) ==> !t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(v), spec_v2l3index(v), spec_v2l2index(v), l1i)))
            },
            va_range.wf(),
            i <= va_range.len,
            !hidden ==> *krnl == *old(krnl) && *lctx == *old(lctx),
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))
                ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus is None
                    || whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus == Some(Set::range(0usize, NUM_CPUS)),
            forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
                let v = va_range.view()[j];
                let cur = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& window_of(v).va == v
                &&& old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(v)))
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_of(v)), TypedLockMode::Write)
                &&& window_perms.dom().contains(window_of(v))
                &&& t0.window_view(window_of(v)).lock_state == (RwLockState::Write { thread_id: window_perms.index(window_of(v)).thread_id(), lock_id: window_perms.index(window_of(v)).lock_id() })
                &&& cur.window_view(window_of(v)).lock_state == t0.window_view(window_of(v)).lock_state
                &&& t0.kernel_l4_end() <= spec_v2l4index(v)
                &&& t0.spec_resolve_mapping_l3(spec_v2l4index(v), spec_v2l3index(v)) is Some
                &&& !t0.lower.l2_entry_hides_l1(t0.window_l2_page(spec_v2l4index(v), spec_v2l3index(v)), spec_v2l2index(v))
                &&& !cur.mapping_2m().dom().contains(v)
                &&& cur.window_view(window_of(v)).l1_table is Some && !cur.window_view(window_of(v)).l2_entry.perm.present
                    ==> forall|l1i: L1Index| #![trigger cur.window_view(window_of(v)).l1_table->Some_0.value().spec_index(l1i)] pei_valid(l1i) ==> !cur.window_view(window_of(v)).l1_table->Some_0.value().spec_index(l1i).perm.kernel_present
            },
            forall|j: int| #![trigger va_range.view()[j]] 0 <= j < i ==> {
                let v = va_range.view()[j];
                let cur = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& !(cur.window_view(window_of(v)).l2_entry.perm.present && !cur.window_view(window_of(v)).l2_entry.perm.ps)
                &&& !hidden ==> cur.window_view(window_of(v)).l1_table is None
            },
        decreases va_range.len - i,
    {
        let va = va_range.index(i);
        let ghost table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        proof {
            assert(table.higher == t0.higher);
            spec_va_2m_valid_index_roundtrip(va);
            assert(spec_va_2m_valid(va) ==> spec_va_4k_valid(va)) by (bit_vector);
            assert forall|l1i: L1Index| #![trigger table.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), l1i)))]
                pei_valid(l1i) implies !table.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), l1i))) by {
                spec_va_4k_index_roundtrip_at(spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), l1i)), spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), l1i);
                assert(old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(va))));
            };
        }
        let links = mmap_2m_window_links_l1(krnl, pagetable_ptr, va, Tracked(&*lctx), Tracked(pagetable_lock_perm));
        if links {
            hide_empty_l1_in_window(krnl, pagetable_ptr, va, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(pagetable_lock_perm), Tracked(window_perms.tracked_borrow(window_of(va))));
            proof {
                kernel_snapshot_k_equal_implies_nonlock_fields_unchanged(&*steps, &*krnl);
                krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
            }
            hidden = true;
        } else {
            proof {
                if !hidden {
                    let p = table.window_l2_page(spec_v2l4index(va), spec_v2l3index(va));
                    pagetable_perms_wf_map(krnl.pt_mp); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr); pagetable_lower_wf_at(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                    table.higher.wf_l4_at(spec_v2l4index(va));
                    table.l3_links_l2_wf_at(table.spec_resolve_mapping_l4(spec_v2l4index(va))->0.addr, spec_v2l3index(va));
                    table.wf_l2_at(p, spec_v2l2index(va));
                }
            }
        }
        i = i + 1;
    }
    hidden
}

/// Flush every CPU's TLB for the caller's page table `pagetable_ptr`, whose held 2M windows of `va_range` hide their empty
/// L1 pages, then return each hidden L1 page to the 4K pool of its owner, the caller's container. Records the flush steps,
/// the release of the container's cpu set, if visible, and one quota credit per returned page; afterwards no window of
/// the range owns an L1 page or lists a stale CPU.
pub(super) fn mmap_2m_flush_and_reclaim_hidden_l1_range(
    krnl: &mut KernelK, va_range: &VaRange2M, cpu_id: CpuId, thrd_ptr: RwLockThreadPtr, prc_ptr: RwLockProcessPtr, ctn_ptr: RwLockContainerPtr, pagetable_ptr: RwLockPageTableRoot,
    Ghost(phase): Ghost<Mmap2mPhase>, Ghost(t4k): Ghost<WholePageTable<PT_TYPE>>, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(steps): Tracked<&mut KernelSteps>, Tracked(cpu_lock_perm): Tracked<&LockPerm>,
    Tracked(pagetable_lock_perm): Tracked<&LockPerm>, Tracked(window_perms): Tracked<&Map<WindowVa, LockPerm>>,
)
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(steps).snapshot_k() == *old(krnl),
        index_valid(NUM_CPUS, cpu_id),
        cpu_id == old(lctx).cpu_id(),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
        cpu_lock_perm.state() is WriteLock,
        cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread()->Write_lock_id,
        old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
        old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
        old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_pcid),
        old(krnl).thrd_mp.dom().contains(thrd_ptr),
        !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
        old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range: *va_range, mapped: 0, directory: Mmap2mDirectory::None, phase }),
        !(phase is Fill),
        held_locks_order_below(old(krnl), old(lctx), ALLOCATOR_CACHE_4K_MAJOR),
        old(lctx).page_lock_map().dom().is_empty(),
        old(lctx).scheduler_lock_map().dom().is_empty(),
        old(lctx).cpu_set_lock_map().dom().is_empty(),
        old(krnl).pt_mp.dom().contains(pagetable_ptr),
        typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
        pagetable_lock_perm.state() is ReadLock,
        pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
        old(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        va_range.wf(),
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))
            ==> whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus is None
                || whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus == Some(Set::range(0usize, NUM_CPUS)),
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            let v = va_range.view()[j];
            let table = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            &&& window_of(v).va == v
            &&& old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(v)))
            &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_of(v)), TypedLockMode::Write)
            &&& window_perms.dom().contains(window_of(v))
            &&& table.window_view(window_of(v)).lock_state == (RwLockState::Write { thread_id: window_perms.index(window_of(v)).thread_id(), lock_id: window_perms.index(window_of(v)).lock_id() })
            &&& table.kernel_l4_end() <= spec_v2l4index(v)
            &&& table.spec_resolve_mapping_l3(spec_v2l4index(v), spec_v2l3index(v)) is Some
            &&& !(table.window_view(window_of(v)).l2_entry.perm.present && !table.window_view(window_of(v)).l2_entry.perm.ps)
            &&& !table.mapping_2m().dom().contains(v)
            &&& table.window_view(window_of(v)).l1_table is Some && !table.window_view(window_of(v)).l2_entry.perm.present
                ==> forall|l1i: L1Index| #![trigger table.window_view(window_of(v)).l1_table->Some_0.value().spec_index(l1i)] pei_valid(l1i) ==> !table.window_view(window_of(v)).l1_table->Some_0.value().spec_index(l1i).perm.kernel_present
            &&& forall|l1i: L1Index| #![trigger t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(v), spec_v2l3index(v), spec_v2l2index(v), l1i)))]
                pei_valid(l1i) ==> !t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(v), spec_v2l3index(v), spec_v2l2index(v), l1i)))
        },
    ensures
        final(steps).snapshot_k() == *final(krnl),
        old(steps).view().len() <= final(steps).view().len() <= old(steps).view().len() + NUM_CPUS + 1 + va_range.len,
        forall|j: int| #![trigger final(steps).view()[j]] 0 <= j < old(steps).view().len() ==> final(steps).view()[j] == old(steps).view()[j],
        forall|j: int| #![trigger final(steps).view()[j]] old(steps).view().len() <= j < final(steps).view().len() ==> mmap_2m_range_step(final(steps).view()[j], cpu_id),
        final(krnl).inv(),
        final(lctx).kernel_view_locking_state() is Acquire,
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        typed_lock_maps_unchanged(old(lctx), final(lctx)),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        final(krnl).cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
        final(krnl).cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
        final(krnl).cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
        held_threads_unchanged(old(krnl).thrd_mp, final(krnl).thrd_mp, old(lctx)),
        final(krnl).pt_mp.dom().contains(pagetable_ptr),
        final(krnl).pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
        final(krnl).pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
        forall|w: WindowVa, u: VAddr|
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
            #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
            old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                &&& whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
            },
        forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))
            ==> whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus is None,
        forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
            let v = va_range.view()[j];
            let pre = whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr);
            let post = whole_pagetable(final(krnl).pt_mp, final(krnl).pt_lower.view(), pagetable_ptr);
            &&& post.window_view(window_of(v)).lock_state == pre.window_view(window_of(v)).lock_state
            &&& post.window_view(window_of(v)).l1_table is None
            &&& !post.mapping_2m().dom().contains(v)
        },
{
    let ghost t0 = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let ghost start = old(steps).view().len() as int;
    assert(krnl.prc_mp.dom().contains(prc_ptr) && krnl.prc_mp.view().spec_index(prc_ptr).is_init() && krnl.prc_mp.view().spec_index(prc_ptr).addr() == prc_ptr) by {
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_perms_wf_at(krnl.prc_mp, prc_ptr);
    };
    let process = krnl.prc_mp.borrow_rodata(prc_ptr).borrow();
    let cr3 = process.cr3;
    let pcid = process.pcid;
    proof {
        thread_perms_wf_at(krnl.thrd_mp, thrd_ptr); thread_cpu_wf_cpu_at(krnl.thrd_mp, krnl.cpu_arr, cpu_id);
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_cpu_wf_at(krnl.prc_mp, krnl.cpu_arr, cpu_id); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        process_perms_wf_at(krnl.prc_mp, prc_ptr); process_pcid_allocator_wf_process_at(krnl.ctn_mp, krnl.prc_mp, krnl.pcid_allc_mp, prc_ptr); pagetable_perms_wf_at(krnl.pt_mp, pagetable_ptr);
        krnl.pt_mp.spec_index(pagetable_ptr).view().table_pages_wf_cr3_at();
        container_process_wf_process_at(krnl.ctn_mp, krnl.prc_mp, prc_ptr);
    }
    let ghost flush_lctx = *lctx;
    flush_pagetable_tlbs(krnl, pagetable_ptr, cr3, pcid, cpu_id, thrd_ptr, false, Tracked(&mut *lctx), Tracked(&mut *steps), Tracked(cpu_lock_perm), Tracked(pagetable_lock_perm));
    proof {
        process_thread_wf_thread_at(old(krnl).prc_mp, old(krnl).thrd_mp, thrd_ptr); process_pagetable_wf_process_at(old(krnl).prc_mp, old(krnl).pt_mp, prc_ptr);
        mmap_2m_tlb_flush_range_steps_from_k(&*steps, old(steps).view(), start, old(krnl), &flush_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable_ptr, *va_range, phase);
    }
    let ghost flushed_snap = steps.snapshot_k();
    let ghost flushed_pre = *krnl;
    let ghost flushed_before = steps.view();
    proof {
        let cs = krnl.ctn_mp.spec_index(ctn_ptr).view_rodata().view().cpu_set;
        process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
        mmap_2m_flushed_step_from_k(&flushed_snap, &flushed_pre, &flush_lctx, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable_ptr, *va_range, phase);
        if flushed_snap.cpu_set_mp.spec_index(cs).lock_state_u() == krnl.cpu_set_mp.spec_index(cs).lock_state_u() {
            krnl.kernel_step_boundary_nonlock_fields_unchanged(&mut *lctx, &mut *steps);
        } else { krnl.kernel_step_boundary_user_view_changed(&mut *lctx, &mut *steps); }
        mmap_2m_flushed_range_steps_from_u(&*steps, flushed_before, start, kernel_k_to_kernel_u(flushed_snap), kernel_k_to_kernel_u(flushed_pre), cpu_id);
    }
    let ghost t1 = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
    let ghost reclaim_start = steps.view().len();
    let mut i: usize = 0;
    while i < va_range.len
        invariant
            steps.snapshot_k() == *krnl,
            start == old(steps).view().len() as int,
            old(steps).view().len() <= reclaim_start <= old(steps).view().len() + NUM_CPUS + 1,
            !thread_is_dangling(old(krnl).thrd_mp.spec_index(thrd_ptr)),
            reclaim_start <= steps.view().len() <= reclaim_start + i,
            forall|j: int| #![trigger steps.view()[j]] 0 <= j < old(steps).view().len() ==> steps.view()[j] == old(steps).view()[j],
            forall|j: int| #![trigger steps.view()[j]] old(steps).view().len() <= j < steps.view().len() ==> mmap_2m_range_step(steps.view()[j], cpu_id),
            krnl.inv(),
            lctx.kernel_view_locking_state() is Acquire,
            typed_lock_maps_aligned(krnl, lctx),
            typed_lock_maps_unchanged(old(lctx), lctx),
            lctx.cpu_id() == old(lctx).cpu_id(),
            lctx.thread_id() == old(lctx).thread_id(),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id == old(lctx).cpu_id(),
            typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), cpu_id, TypedLockMode::Write),
            old(krnl).cpu_op.view().view()[cpu_id as int] is InStep,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().state is Running,
            old(krnl).cpu_arr.spec_index(cpu_id).view().view().view().current_thread == Some(thrd_ptr),
            krnl.cpu_op.view().view()[cpu_id as int] == old(krnl).cpu_op.view().view()[cpu_id as int],
            krnl.cpu_hw_cr3_pcid[cpu_id as int].view() == old(krnl).cpu_hw_cr3_pcid[cpu_id as int].view(),
            krnl.cpu_arr.spec_index(cpu_id).view().view() == old(krnl).cpu_arr.spec_index(cpu_id).view().view(),
            krnl.cpu_arr.spec_index(cpu_id).view().locking_thread() == old(krnl).cpu_arr.spec_index(cpu_id).view().locking_thread(),
            krnl.cpu_arr.spec_index(cpu_id).view().being_killed() == old(krnl).cpu_arr.spec_index(cpu_id).view().being_killed(),
            held_threads_unchanged(old(krnl).thrd_mp, krnl.thrd_mp, old(lctx)),
            old(krnl).thrd_mp.dom().contains(thrd_ptr),
            typed_lock_map_contains_mode(old(lctx).thread_lock_map(), thrd_ptr, TypedLockMode::Write),
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_proc == prc_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().owning_container == ctn_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().proc_pagetable_ptr == pagetable_ptr,
            old(krnl).thrd_mp.spec_index(thrd_ptr).view().syscall_progress.view() == Some(SyscallProgress::Mmap2m { range: *va_range, mapped: 0, directory: Mmap2mDirectory::None, phase }),
            !(phase is Fill),
            held_locks_order_below(krnl, lctx, ALLOCATOR_CACHE_4K_MAJOR),
            old(lctx).page_lock_map().dom().is_empty(),
            old(lctx).scheduler_lock_map().dom().is_empty(),
            old(lctx).cpu_set_lock_map().dom().is_empty(),
            krnl.pt_mp.dom().contains(pagetable_ptr),
            krnl.pt_mp.spec_index(pagetable_ptr).view() == old(krnl).pt_mp.spec_index(pagetable_ptr).view(),
            typed_lock_map_contains_mode(old(lctx).pagetable_lock_map(), pagetable_ptr, TypedLockMode::Read),
            pagetable_lock_perm.state() is ReadLock,
            pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
            krnl.pt_mp.spec_index(pagetable_ptr).locking_thread()->Read_reader_map.contains_pair(old(lctx).thread_id(), pagetable_lock_perm.lock_id()),
            t0 == whole_pagetable(old(krnl).pt_mp, old(krnl).pt_lower.view(), pagetable_ptr),
            forall|w: WindowVa, u: VAddr|
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u)]
                #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)), t4k.mapping_4k().dom().contains(u)]
                old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w)) && spec_v2l4index(u) == spec_v2l4index(w.va) && spec_v2l3index(u) == spec_v2l3index(w.va)
                    && spec_v2l2index(u) == spec_v2l2index(w.va) ==> {
                    &&& whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().dom().contains(u) == t4k.mapping_4k().dom().contains(u)
                    &&& t4k.mapping_4k().dom().contains(u) ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).mapping_4k().spec_index(u) == t4k.mapping_4k().spec_index(u)
                },
            va_range.wf(),
            i <= va_range.len,
            forall|w: WindowVa| #![trigger old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))] old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, w))
                ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).window_view(w).stale_cpus is None,
            forall|j: int| #![trigger va_range.view()[j]] 0 <= j < va_range.len ==> {
                let v = va_range.view()[j];
                let cur = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                &&& window_of(v).va == v
                &&& old(lctx).pagetable_window_lock_map().dom().contains((pagetable_ptr, window_of(v)))
                &&& typed_lock_map_contains_mode(old(lctx).pagetable_window_lock_map(), (pagetable_ptr, window_of(v)), TypedLockMode::Write)
                &&& window_perms.dom().contains(window_of(v))
                &&& t0.window_view(window_of(v)).lock_state == (RwLockState::Write { thread_id: window_perms.index(window_of(v)).thread_id(), lock_id: window_perms.index(window_of(v)).lock_id() })
                &&& cur.window_view(window_of(v)).lock_state == t0.window_view(window_of(v)).lock_state
                &&& t0.kernel_l4_end() <= spec_v2l4index(v)
                &&& t0.spec_resolve_mapping_l3(spec_v2l4index(v), spec_v2l3index(v)) is Some
                &&& !cur.mapping_2m().dom().contains(v)
                &&& forall|l1i: L1Index| #![trigger t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(v), spec_v2l3index(v), spec_v2l2index(v), l1i)))]
                    pei_valid(l1i) ==> !t4k.mapping_4k().dom().contains(spec_index2va((spec_v2l4index(v), spec_v2l3index(v), spec_v2l2index(v), l1i)))
            },
            forall|j: int| #![trigger va_range.view()[j]] 0 <= j < i ==> whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr).window_view(window_of(va_range.view()[j])).l1_table is None,
            forall|j: int| #![trigger va_range.view()[j]] i <= j < va_range.len ==> {
                let cur = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
                let v = va_range.view()[j];
                &&& !(cur.window_view(window_of(v)).l2_entry.perm.present && !cur.window_view(window_of(v)).l2_entry.perm.ps)
                &&& cur.window_view(window_of(v)).l1_table is Some && !cur.window_view(window_of(v)).l2_entry.perm.present
                    ==> forall|l1i: L1Index| #![trigger cur.window_view(window_of(v)).l1_table->Some_0.value().spec_index(l1i)] pei_valid(l1i) ==> !cur.window_view(window_of(v)).l1_table->Some_0.value().spec_index(l1i).perm.kernel_present
            },
        decreases va_range.len - i,
    {
        let va = va_range.index(i);
        let ghost table = whole_pagetable(krnl.pt_mp, krnl.pt_lower.view(), pagetable_ptr);
        proof {
            assert(table.higher == t0.higher);
            spec_va_2m_valid_index_roundtrip(va);
            assert(spec_va_2m_valid(va) ==> spec_va_4k_valid(va)) by (bit_vector);
        }
        let (l2_ptr, word) = mmap_2m_window_l2_word(krnl, pagetable_ptr, va, Tracked(&*lctx), Tracked(pagetable_lock_perm));
        if word.perm.kernel_present && !word.perm.present && !word.perm.ps {
            proof {
                assert(table.window_view(window_of(va)).l1_table is Some && !table.window_view(window_of(va)).l2_entry.perm.present);
                assert(old(lctx).thread_lock_map().dom().contains(thrd_ptr));
                process_thread_wf_thread_at(krnl.prc_mp, krnl.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(krnl.prc_mp, krnl.pt_mp, prc_ptr);
            }
            proof { assert(old(lctx).cpu_lock_map().dom().contains(cpu_id)); }
            let ghost before = steps.view();
            let (owner, reclaim_entry, reclaim_lctx) = reclaim_hidden_l1_page_in_window(krnl, pagetable_ptr, va, l2_ptr, word.addr, cpu_id, Tracked(&mut *lctx), Tracked(&mut *steps),
                Tracked(pagetable_lock_perm), Tracked(window_perms.tracked_borrow(window_of(va))));
            proof {
                assert(owner == ctn_ptr);
                process_thread_wf_thread_at(reclaim_entry@.prc_mp, reclaim_entry@.thrd_mp, thrd_ptr); process_pagetable_wf_process_at(reclaim_entry@.prc_mp, reclaim_entry@.pt_mp, prc_ptr);
                container_thread_wf_thread_at(reclaim_entry@.ctn_mp, reclaim_entry@.thrd_mp, thrd_ptr);
                assert forall|j: int| #![trigger steps.view()[j]] 0 <= j < before.len() implies steps.view()[j] == before[j] by { assert(steps.view().drop_last()[j] == steps.view()[j]); };
                assert(steps.view() =~= before.push(steps.view().last()));
                mmap_2m_l1_reclaim_range_steps_from_k(&*steps, before, start, &reclaim_entry@, &reclaim_lctx@, cpu_id, prc_ptr, thrd_ptr, ctn_ptr, pagetable_ptr, *va_range, phase);
            }
        }
        i = i + 1;
    }
}
} // verus!
