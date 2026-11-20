//! Round 3: who holds the pagetable lock and the 2M window locks of a process in a traced behaviour, and which steps a cpu
//! inside `mmap_4k` or `unmap_4k` has enabled. Explicit-index style.
use vstd::prelude::*;
use crate::*;
use crate::trace::*;
use veriflat_map_4k::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;
use veriflat_syscall_new_thread::syscall_new_endpoint::syscall_new_endpoint_spec::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;

verus! {
/// `c` is inside `mmap_4k` past its enter step or inside `unmap_4k`: its cpu is write-locked and its running thread records
/// `Mmap4k` or `Unmap4k` progress.
pub open spec fn table_op(u: KernelU, c: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, c)
    &&& u.cpu_array[c as int].lock_state is WriteLocked
    &&& u.cpu_array[c as int].current_thread is Some
    &&& cur_thread(u, c).syscall_progress is Some
    &&& cur_thread(u, c).syscall_progress->Some_0 is Mmap4k || cur_thread(u, c).syscall_progress->Some_0 is Unmap4k
}

pub open spec fn table_progress(u: KernelU, c: CpuId) -> SyscallProgress { cur_thread(u, c).syscall_progress->Some_0 }

/// The process whose pagetable `c` maps or unmaps in.
pub open spec fn table_proc(u: KernelU, c: CpuId) -> RwLockProcessPtr { cur_thread(u, c).owning_proc }

/// `c` is in the fill phase of `mmap_4k`.
pub open spec fn table_filling(u: KernelU, c: CpuId) -> bool { table_progress(u, c) is Mmap4k && table_progress(u, c)->Mmap4k_phase is Fill }

/// The range `c` records.
pub open spec fn table_range(u: KernelU, c: CpuId) -> VaRange4K {
    let prog = table_progress(u, c);
    if prog is Mmap4k { prog->Mmap4k_range } else if prog is Unmap4k { prog->Unmap4k_range }
    else if prog is NewProcess { prog->NewProcess_0.range } else { prog->Share4k_origin->NewProcess_0.range }
}

/// `x` is inside `new_process`: its cpu is write-locked and its running thread records the creation or the share into the
/// child that follows it. It read-holds its process's page table and write-holds the 2M windows of its range there, and
/// once published the child's page table and the child windows of its range.
pub open spec fn table_sharer(u: KernelU, x: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, x)
    &&& u.cpu_array[x as int].lock_state is WriteLocked
    &&& u.cpu_array[x as int].current_thread is Some
    &&& cur_thread(u, x).syscall_progress is Some
    &&& table_progress(u, x) is NewProcess || (table_progress(u, x) is Share4k && table_progress(u, x)->Share4k_origin is NewProcess)
}

/// The child sharer `x` has published, if any.
pub open spec fn sharer_child(u: KernelU, x: CpuId) -> Option<RwLockProcessPtr> {
    if table_progress(u, x) is Share4k { table_progress(u, x)->Share4k_origin->NewProcess_0.child } else { None }
}

pub open spec fn table_present(u: KernelU, p: RwLockProcessPtr) -> bool { u.process_map.dom().contains(p) && u.process_map[p].pagetable is Some }

pub open spec fn table_lock(u: KernelU, p: RwLockProcessPtr) -> LockStateU { u.process_map[p].pagetable->Some_0.lock_state }

pub open spec fn table_windows(u: KernelU, p: RwLockProcessPtr) -> Map<WindowVa, LockStateU> { u.process_map[p].pagetable->Some_0.pagetable_window_locks }

/// What the lock invariants read of process `p`.
pub open spec fn table_view(u: KernelU, p: RwLockProcessPtr) -> (bool, LockStateU, Map<WindowVa, LockStateU>) { (table_present(u, p), table_lock(u, p), table_windows(u, p)) }

/// Window `w` of process `p` is not read-locked, and a cpu write-holding it is inside `mmap_4k` or `unmap_4k` on `p`, or
/// inside `new_process` on `p` or its published child, with `w` among the 2M windows of its recorded range.
pub open spec fn window_held_by_op(u: KernelU, p: RwLockProcessPtr, w: WindowVa) -> bool {
    let x = table_windows(u, p)[w]->WriteLocked_writer;
    &&& !(table_windows(u, p)[w] is ReadLocked)
    &&& table_windows(u, p)[w] is WriteLocked ==> {
        &&& table_op(u, x) && table_proc(u, x) == p || table_sharer(u, x) && (table_proc(u, x) == p || sharer_child(u, x) == Some(p))
        &&& va_range_2m_windows(table_range(u, x)).contains(w)
    }
}

/// `x` is inside `kill_process` at a reclaim or quota stage, where it write-holds its target's page table.
pub open spec fn table_killer(u: KernelU, x: CpuId) -> bool {
    &&& index_valid(NUM_CPUS, x)
    &&& u.cpu_array[x as int].lock_state is WriteLocked
    &&& u.cpu_array[x as int].current_thread is Some
    &&& cur_thread(u, x).syscall_progress is Some
    &&& {
        let prog = cur_thread(u, x).syscall_progress->Some_0;
        ||| prog is KillProcess && (prog->KillProcess_stage is Reclaim || prog->KillProcess_stage is Quota)
        ||| prog is ThreadExitReclaim || prog is ThreadExitQuota
    }
}

/// The target whose page table killer `x` holds.
pub open spec fn table_killer_proc(u: KernelU, x: CpuId) -> RwLockProcessPtr {
    if cur_thread(u, x).syscall_progress->Some_0 is KillProcess { cur_thread(u, x).syscall_progress->Some_0->KillProcess_process } else { cur_thread(u, x).owning_proc }
}

/// Lock holder consistency of process `p`: the writer of its pagetable fills it or reclaims it inside `kill_process`,
/// every reader maps or unmaps in it outside the fill phase, and every window holds `window_held_by_op`.
pub open spec fn table_locks_held_by_ops_at(u: KernelU, p: RwLockProcessPtr) -> bool {
    &&& table_lock(u, p) is WriteLocked ==> {
        let x = table_lock(u, p)->WriteLocked_writer;
        ||| table_op(u, x) && table_proc(u, x) == p && table_filling(u, x)
        ||| table_killer(u, x) && table_killer_proc(u, x) == p
        ||| table_sharer(u, x) && sharer_child(u, x) == Some(p)
    }
    &&& forall|x: CpuId| #![trigger table_lock(u, p).readers().contains(x)] table_lock(u, p).readers().contains(x) ==> reader_ok(u, p, x)
    &&& forall|w: WindowVa| #![trigger table_windows(u, p).dom().contains(w)] table_windows(u, p).dom().contains(w) ==> window_held_by_op(u, p, w)
}

/// A reader `x` of the pagetable of `p` maps or unmaps in it outside the fill phase, or shares from it inside `new_process`.
pub open spec fn reader_ok(u: KernelU, p: RwLockProcessPtr, x: CpuId) -> bool {
    table_op(u, x) && table_proc(u, x) == p && !table_filling(u, x) || table_sharer(u, x) && table_proc(u, x) == p
}

/// What sharer `c` holds of the pagetables: its recorded range is well formed and non-empty, it read-holds its process's
/// pagetable and write-holds every existing 2M window of its range there, and once it has published the child it write-holds
/// the child's pagetable, another process.
pub open spec fn sharer_holds_tables(u: KernelU, c: CpuId) -> bool {
    let p = table_proc(u, c);
    let ch = sharer_child(u, c)->Some_0;
    &&& table_range(u, c).wf() && table_range(u, c).len > 0
    &&& table_present(u, p) && table_lock(u, p).read_held_by(c)
    &&& op_holds_range_windows(u, c)
    &&& sharer_child(u, c) is Some ==> ch != p && table_present(u, ch) && table_lock(u, ch) == (LockStateU::WriteLocked { writer: c })
}

/// The pages sharer `c` has shared: none before it publishes the child.
pub open spec fn sharer_shared(u: KernelU, c: CpuId) -> int { if table_progress(u, c) is Share4k { table_progress(u, c)->Share4k_shared as int } else { 0 } }

/// The pages sharer `c` has still to share are mapped in its process and, once the child is published, not in the child.
pub open spec fn sharer_vas(u: KernelU, c: CpuId) -> bool {
    let r = table_range(u, c);
    let ch = sharer_child(u, c)->Some_0;
    &&& forall|k: int| #![trigger r.view()[k]] sharer_shared(u, c) <= k < r.len ==> table_mapping(u, c).dom().contains(r.view()[k])
    &&& sharer_child(u, c) is Some ==> forall|k: int| #![trigger r.view()[k]] sharer_shared(u, c) <= k < r.len
        ==> !u.process_map[ch].pagetable->Some_0.mapping_4k.dom().contains(r.view()[k])
}

/// Every sharer write-holds the process of the child it has published.
pub open spec fn sharer_children_held(u: KernelU) -> bool {
    forall|c: CpuId| #![trigger table_sharer(u, c)] table_sharer(u, c) && sharer_child(u, c) is Some
        ==> u.process_map[sharer_child(u, c)->Some_0].lock_state == (LockStateU::WriteLocked { writer: c })
}

/// The cpu inside keeps its thread write-locked and a well-formed non-empty range, and its progress is in range: at most
/// every page done, no directory recorded once every page is mapped, 4K quota left for a leaf of every unmapped page, and
/// the flush recorded only once every page is cleared.
pub open spec fn table_op_shape(u: KernelU, c: CpuId) -> bool {
    let prog = table_progress(u, c);
    &&& cur_thread(u, c).lock_state is WriteLocked
    &&& table_range(u, c).wf() && table_range(u, c).len > 0
    &&& prog is Mmap4k ==> prog->Mmap4k_mapped <= prog->Mmap4k_range.len && (prog->Mmap4k_mapped == prog->Mmap4k_range.len ==> prog->Mmap4k_directory is None)
    &&& prog is Mmap4k ==> cur_thread(u, c).quota_4k >= prog->Mmap4k_range.len - prog->Mmap4k_mapped
    &&& prog is Mmap4k && prog->Mmap4k_phase is Fill ==> prog->Mmap4k_mapped == 0
    &&& prog is Unmap4k ==> prog->Unmap4k_unmapped <= prog->Unmap4k_range.len && (prog->Unmap4k_flushed ==> prog->Unmap4k_unmapped == prog->Unmap4k_range.len)
}

/// The cpu inside holds its process's pagetable, for writing while filling and for reading otherwise, write-holds every
/// existing 2M window of its range, and outside the fill phase every such window exists.
pub open spec fn table_op_holds_locks(u: KernelU, c: CpuId) -> bool {
    &&& table_present(u, table_proc(u, c))
    &&& table_filling(u, c) ==> table_lock(u, table_proc(u, c)) == (LockStateU::WriteLocked { writer: c })
    &&& !table_filling(u, c) ==> table_lock(u, table_proc(u, c)).read_held_by(c)
    &&& op_holds_range_windows(u, c)
    &&& !table_filling(u, c) ==> pagetable_range_windows_exist(table_windows(u, table_proc(u, c)), table_range(u, c))
}

/// `c` write-holds every existing 2M window of its range.
pub open spec fn op_holds_range_windows(u: KernelU, c: CpuId) -> bool {
    forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u, c)).contains(w)] va_range_2m_windows(table_range(u, c)).contains(w)
        && table_windows(u, table_proc(u, c)).dom().contains(w) ==> table_windows(u, table_proc(u, c))[w] == (LockStateU::WriteLocked { writer: c })
}

/// The 4K mapping of the pagetable `c` works on.
pub open spec fn table_mapping(u: KernelU, c: CpuId) -> Map<VAddr, MapEntry> { u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k }

/// The pages `c` has still to map are unmapped, and those it has still to clear are mapped to RAM.
pub open spec fn table_op_vas(u: KernelU, c: CpuId) -> bool {
    let prog = table_progress(u, c);
    &&& prog is Mmap4k ==> forall|k: int| #![trigger prog->Mmap4k_range.view()[k]] prog->Mmap4k_mapped <= k < prog->Mmap4k_range.len
        ==> !table_mapping(u, c).dom().contains(prog->Mmap4k_range.view()[k])
    &&& prog is Unmap4k ==> forall|k: int| #![trigger prog->Unmap4k_range.view()[k]] prog->Unmap4k_unmapped <= k < prog->Unmap4k_range.len
        ==> table_mapping(u, c).dom().contains(prog->Unmap4k_range.view()[k]) && !table_mapping(u, c)[prog->Unmap4k_range.view()[k]].is_io
}

/// VA progress of every cpu inside.
pub open spec fn table_ops_vas(u: KernelU) -> bool {
    &&& forall|c: CpuId| #![trigger table_op(u, c)] table_op(u, c) ==> table_op_vas(u, c)
    &&& forall|c: CpuId| #![trigger table_sharer(u, c)] table_sharer(u, c) ==> sharer_vas(u, c)
}

/// Pagetable lock consistency: every pagetable and window lock is held only by cpus inside `mmap_4k` or `unmap_4k` on its
/// process, and every such cpu holds its pagetable in the mode of its phase.
pub open spec fn pagetable_locks_consistent(u: KernelU) -> bool {
    &&& forall|p: RwLockProcessPtr| #![trigger table_present(u, p)] table_present(u, p) ==> table_locks_held_by_ops_at(u, p)
    &&& forall|c: CpuId| #![trigger table_op(u, c)] table_op(u, c) ==> table_op_holds_locks(u, c) && table_op_shape(u, c)
    &&& forall|c: CpuId| #![trigger table_sharer(u, c)] table_sharer(u, c) ==> sharer_holds_tables(u, c)
}

/// No cpu is inside `mmap_4k` past its enter step or inside `unmap_4k`, and every pagetable and window is unlocked.
pub open spec fn pagetables_quiescent(u: KernelU) -> bool {
    &&& forall|c: CpuId| #![trigger table_op(u, c)] !table_op(u, c)
    &&& forall|p: RwLockProcessPtr| #![trigger table_present(u, p)] table_present(u, p) ==> {
        &&& table_lock(u, p) is Unlocked
        &&& forall|w: WindowVa| #![trigger table_windows(u, p).dom().contains(w)] table_windows(u, p).dom().contains(w) ==> table_windows(u, p)[w] is Unlocked
    }
}

/// `c` has the same status inside, process, phase, range, and child in `u` and `u2`.
pub open spec fn table_status_same(u: KernelU, u2: KernelU, c: CpuId) -> bool {
    &&& table_sharer(u2, c) == table_sharer(u, c)
    &&& table_sharer(u, c) ==> table_proc(u2, c) == table_proc(u, c) && table_range(u2, c) == table_range(u, c) && sharer_child(u2, c) == sharer_child(u, c)
    &&& table_op(u2, c) == table_op(u, c)
    &&& table_op(u, c) ==> table_proc(u2, c) == table_proc(u, c) && table_filling(u2, c) == table_filling(u, c) && table_range(u2, c) == table_range(u, c)
    &&& table_killer(u2, c) == table_killer(u, c)
    &&& table_killer(u, c) ==> table_killer_proc(u2, c) == table_killer_proc(u, c)
}

pub open spec fn other_cpu_unchanged(u: KernelU, u2: KernelU, x: CpuId) -> bool { table_status_same(u, u2, x) && (table_op(u, x) ==> table_op_shape(u2, x) == table_op_shape(u, x)) }

/// A step of `d` leaves every other cpu's status and shape alone.
pub open spec fn others_unchanged(u: KernelU, u2: KernelU, d: CpuId) -> bool { forall|x: CpuId| #![trigger other_cpu_unchanged(u, u2, x)] x != d ==> other_cpu_unchanged(u, u2, x) }

/// Window `w` of `p` after a step of `d` keeps its value, or is new on the table `d` fills or on the child `d` shares into,
/// held by `d` exactly when its range covers `w`.
pub open spec fn window_kept_or_new(u: KernelU, u2: KernelU, d: CpuId, p: RwLockProcessPtr, w: WindowVa) -> bool {
    ||| table_windows(u, p).dom().contains(w) && table_windows(u2, p)[w] == table_windows(u, p)[w]
    ||| !table_windows(u, p).dom().contains(w) && (table_op(u, d) && table_filling(u, d) && table_proc(u, d) == p || table_sharer(u, d) && sharer_child(u, d) == Some(p))
        && table_windows(u2, p)[w] == (if va_range_2m_windows(table_range(u, d)).contains(w) { LockStateU::WriteLocked { writer: d } } else { LockStateU::Unlocked })
}

/// A quiescent state, as after boot, has consistent pagetable locks.
pub proof fn pagetables_quiescent_implies_locks_consistent(u: KernelU)
    requires pagetables_quiescent(u), forall|c: CpuId| #![trigger table_sharer(u, c)] !table_sharer(u, c),
    ensures pagetable_locks_consistent(u), table_ops_vas(u),
{
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u, p)] table_present(u, p) implies table_locks_held_by_ops_at(u, p) by {
        assert forall|w: WindowVa| #![trigger table_windows(u, p).dom().contains(w)] table_windows(u, p).dom().contains(w) implies window_held_by_op(u, p, w) by {};
    };
}


/// The same cpu entry and running thread give the same status and shape.
pub proof fn cpu_slice_same_implies_other_cpu_unchanged(u: KernelU, u2: KernelU, x: CpuId)
    requires u2.cpu_array[x as int] == u.cpu_array[x as int], u.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x) == cur_thread(u, x),
    ensures other_cpu_unchanged(u, u2, x),
{}

/// A step whose lock reads are unchanged but for windows that stay or are new on the table of `d`, while `d` keeps its
/// status and shape, keeps pagetable lock consistency.
pub proof fn table_frame_implies_locks_consistent_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), table_status_same(u, u2, d), table_op(u, d) ==> table_op_shape(u2, d),
        forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) == table_present(u, p)
            && (table_present(u, p) ==> table_lock(u2, p) == table_lock(u, p) && table_windows(u, p).dom().subset_of(table_windows(u2, p).dom())),
        forall|p: RwLockProcessPtr, w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)]
            table_present(u2, p) && table_windows(u2, p).dom().contains(w) ==> window_kept_or_new(u, u2, d, p, w),
    ensures pagetable_locks_consistent(u2),
{
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        assert(table_locks_held_by_ops_at(u, p));
        let lk = table_lock(u, p);
        if lk is WriteLocked && lk->WriteLocked_writer != d { assert(other_cpu_unchanged(u, u2, lk->WriteLocked_writer)); }
        assert forall|x: CpuId| #![trigger table_lock(u2, p).readers().contains(x)] table_lock(u2, p).readers().contains(x)
            implies reader_ok(u2, p, x) by {
            assert(table_lock(u, p).readers().contains(x));
            if x != d { assert(other_cpu_unchanged(u, u2, x)); }
        };
        assert forall|w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)] table_windows(u2, p).dom().contains(w) implies window_held_by_op(u2, p, w) by {
            assert(window_kept_or_new(u, u2, d, p, w));
            if table_windows(u, p).dom().contains(w) {
                assert(window_held_by_op(u, p, w));
                let x = table_windows(u, p)[w]->WriteLocked_writer;
                if table_windows(u, p)[w] is WriteLocked && x != d { assert(other_cpu_unchanged(u, u2, x)); }
            }
        };
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_holds_locks(u2, c) && table_op_shape(u2, c) by {
        if c != d { assert(other_cpu_unchanged(u, u2, c)); }
        assert(table_op(u, c) && table_op_holds_locks(u, c));
        let p = table_proc(u, c);
        let rc = table_range(u, c);
        assert(table_present(u2, p));
        assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)]
            va_range_2m_windows(table_range(u2, c)).contains(w) && table_windows(u2, p).dom().contains(w) implies table_windows(u2, p)[w] == (LockStateU::WriteLocked { writer: c }) by {
            assert(window_kept_or_new(u, u2, d, p, w) && va_range_2m_windows(rc).contains(w));
            if !table_windows(u, p).dom().contains(w) && c != d { if table_op(u, d) { assert(table_op_holds_locks(u, d)); } else { assert(sharer_holds_tables(u, d)); } }
        };
        if !table_filling(u2, c) {
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)] va_range_2m_windows(table_range(u2, c)).contains(w)
                implies table_windows(u2, p).dom().contains(w) by { assert(va_range_2m_windows(rc).contains(w) && table_windows(u, p).dom().contains(w)); };
        }
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_holds_tables(u2, c) by {
        if c != d { assert(other_cpu_unchanged(u, u2, c)); }
        assert(table_sharer(u, c) && sharer_holds_tables(u, c));
        let p = table_proc(u, c);
        assert(table_present(u2, p));
        if sharer_child(u, c) is Some { assert(table_present(u2, sharer_child(u, c)->Some_0)); }
        assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)] va_range_2m_windows(table_range(u2, c)).contains(w)
            && table_windows(u2, p).dom().contains(w) implies table_windows(u2, p)[w] == (LockStateU::WriteLocked { writer: c }) by {
            assert(window_kept_or_new(u, u2, d, p, w));
            if !table_windows(u, p).dom().contains(w) {
                if table_op(u, d) { assert(table_op_holds_locks(u, d)); } else { assert(sharer_holds_tables(u, d)); }
            } else { assert(va_range_2m_windows(table_range(u, c)).contains(w)); }
        };
    };
}

/// A step that keeps every lock read keeps pagetable lock consistency while `d` keeps its status and shape.
pub proof fn table_views_same_implies_locks_consistent_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), table_status_same(u, u2, d), table_op(u, d) ==> table_op_shape(u2, d),
        forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] table_view(u2, p) == table_view(u, p),
    ensures pagetable_locks_consistent(u2),
{
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) == table_present(u, p)
        && (table_present(u, p) ==> table_lock(u2, p) == table_lock(u, p) && table_windows(u, p).dom().subset_of(table_windows(u2, p).dom())) by {
        assert(table_view(u2, p) == table_view(u, p));
    };
    assert forall|p: RwLockProcessPtr, w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)]
        table_present(u2, p) && table_windows(u2, p).dom().contains(w) implies window_kept_or_new(u, u2, d, p, w) by {
        assert(table_view(u2, p) == table_view(u, p));
    };
    table_frame_implies_locks_consistent_kept(u, u2, d);
}

/// Process `p`, whose lock reads a step keeps, keeps its holders while its holder `d` keeps its status.
pub proof fn table_view_same_implies_held_by_ops_kept(u: KernelU, u2: KernelU, d: CpuId, p: RwLockProcessPtr)
    requires
        table_locks_held_by_ops_at(u, p), table_view(u2, p) == table_view(u, p), others_unchanged(u, u2, d), !table_killer(u, d),
        table_op(u, d) && table_proc(u, d) == p || table_sharer(u, d) && (table_proc(u, d) == p || sharer_child(u, d) == Some(p)) ==> table_status_same(u, u2, d),
    ensures table_locks_held_by_ops_at(u2, p),
{
    let lk = table_lock(u, p);
    if lk is WriteLocked && lk->WriteLocked_writer != d { assert(other_cpu_unchanged(u, u2, lk->WriteLocked_writer)); }
    assert forall|x: CpuId| #![trigger table_lock(u2, p).readers().contains(x)] table_lock(u2, p).readers().contains(x)
        implies reader_ok(u2, p, x) by {
        assert(table_lock(u, p).readers().contains(x));
        if x != d { assert(other_cpu_unchanged(u, u2, x)); }
    };
    assert forall|w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)] table_windows(u2, p).dom().contains(w) implies window_held_by_op(u2, p, w) by {
        assert(table_windows(u, p).dom().contains(w) && window_held_by_op(u, p, w));
        let x = table_windows(u, p)[w]->WriteLocked_writer;
        if table_windows(u, p)[w] is WriteLocked && x != d { assert(other_cpu_unchanged(u, u2, x)); }
    };
}

/// A cpu inside on a process other than `p0`, whose lock reads a step keeps, keeps its holds and shape.
pub proof fn other_table_op_kept(u: KernelU, u2: KernelU, d: CpuId, c: CpuId, p0: RwLockProcessPtr)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), c != d, table_op(u2, c), table_proc(u2, c) != p0,
        forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] p != p0 && u.process_map.dom().contains(p) ==> table_view(u2, p) == table_view(u, p),
    ensures table_op(u, c), table_op_holds_locks(u, c), table_op_holds_locks(u2, c), table_op_shape(u2, c),
{
    assert(other_cpu_unchanged(u, u2, c));
    assert(table_op(u, c) && table_op_holds_locks(u, c));
    assert(table_view(u2, table_proc(u, c)) == table_view(u, table_proc(u, c)));
}

/// An enter step of `d` into `p0` for range `r`, filling or reading, keeps pagetable lock consistency.
proof fn table_enter_implies_locks_consistent_kept(u: KernelU, u2: KernelU, d: CpuId, p0: RwLockProcessPtr, r: VaRange4K, fill: bool)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), !table_killer(u, d), !table_op(u, d), !table_sharer(u, d),
        table_op(u2, d), table_proc(u2, d) == p0, table_filling(u2, d) == fill, table_range(u2, d) == r, table_op_shape(u2, d),
        forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] p != p0 ==> table_view(u2, p) == table_view(u, p),
        table_present(u, p0), table_present(u2, p0),
        fill ==> table_lock(u, p0) is Unlocked && table_lock(u2, p0) == (LockStateU::WriteLocked { writer: d }),
        !fill ==> !(table_lock(u, p0) is WriteLocked) && table_lock(u2, p0) == table_lock(u, p0).with_reader(d),
        pagetable_range_windows_unlocked(table_windows(u, p0), r), !fill ==> pagetable_range_windows_exist(table_windows(u, p0), r),
        table_windows(u2, p0) == pagetable_window_locks_after_locking_range(table_windows(u, p0), r, d),
    ensures pagetable_locks_consistent(u2),
{
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        if p != p0 {
            assert(table_view(u2, p) == table_view(u, p));
            table_view_same_implies_held_by_ops_kept(u, u2, d, p);
        } else {
            assert(table_locks_held_by_ops_at(u, p0));
            assert forall|x: CpuId| #![trigger table_lock(u2, p0).readers().contains(x)] table_lock(u2, p0).readers().contains(x)
                implies reader_ok(u2, p0, x) by {
                if x != d {
                    assert(table_lock(u, p0).readers().contains(x));
                    assert(other_cpu_unchanged(u, u2, x));
                }
            };
            assert forall|w: WindowVa| #![trigger table_windows(u2, p0).dom().contains(w)] table_windows(u2, p0).dom().contains(w) implies window_held_by_op(u2, p0, w) by {
                assert(table_windows(u, p0).dom().contains(w));
                if !va_range_2m_windows(r).contains(w) {
                    assert(window_held_by_op(u, p0, w));
                    if table_windows(u, p0)[w] is WriteLocked { assert(other_cpu_unchanged(u, u2, table_windows(u, p0)[w]->WriteLocked_writer)); }
                }
            };
        }
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_holds_locks(u2, c) && table_op_shape(u2, c) by {
        if c == d {
            if !fill {
                assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, d)).contains(w)] va_range_2m_windows(table_range(u2, d)).contains(w)
                    implies table_windows(u2, p0).dom().contains(w) by { assert(va_range_2m_windows(r).contains(w)); };
            }
        } else if table_proc(u2, c) != p0 {
            other_table_op_kept(u, u2, d, c, p0);
        } else {
            assert(other_cpu_unchanged(u, u2, c));
            assert(table_op(u, c) && table_op_holds_locks(u, c));
            if !table_filling(u, c) { assert(table_lock(u, p0).readers().contains(c)); }
            let rc = table_range(u, c);
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)] va_range_2m_windows(table_range(u2, c)).contains(w)
                && table_windows(u2, p0).dom().contains(w) implies table_windows(u2, p0)[w] == (LockStateU::WriteLocked { writer: c }) by {
                assert(va_range_2m_windows(rc).contains(w));
                if va_range_2m_windows(r).contains(w) { assert(table_windows(u, p0)[w] is Unlocked); }
            };
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)] va_range_2m_windows(table_range(u2, c)).contains(w)
                implies table_windows(u2, p0).dom().contains(w) by { assert(va_range_2m_windows(rc).contains(w)); };
        }
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_holds_tables(u2, c) by {
        assert(other_cpu_unchanged(u, u2, c));
        assert(table_sharer(u, c) && sharer_holds_tables(u, c));
        let p = table_proc(u, c);
        let rc = table_range(u, c);
        if p != p0 { assert(table_view(u2, p) == table_view(u, p)); }
        else {
            assert(table_lock(u, p0).readers().contains(c));
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)] va_range_2m_windows(table_range(u2, c)).contains(w)
                && table_windows(u2, p0).dom().contains(w) implies table_windows(u2, p0)[w] == (LockStateU::WriteLocked { writer: c }) by {
                assert(va_range_2m_windows(rc).contains(w));
                if va_range_2m_windows(r).contains(w) { assert(table_windows(u, p0)[w] is Unlocked); }
            };
        }
        if sharer_child(u, c) is Some { assert(table_view(u2, sharer_child(u, c)->Some_0) == table_view(u, sharer_child(u, c)->Some_0)); }
    };
}

/// The downgrade step of `d` in `p0`, all of whose range windows exist, keeps pagetable lock consistency.
proof fn table_downgrade_implies_locks_consistent_kept(u: KernelU, u2: KernelU, d: CpuId, p0: RwLockProcessPtr)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), !table_killer(u, d), table_op(u, d), table_filling(u, d), table_proc(u, d) == p0,
        table_op(u2, d), !table_filling(u2, d), table_proc(u2, d) == p0, table_range(u2, d) == table_range(u, d), table_op_shape(u2, d),
        forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] p != p0 ==> table_view(u2, p) == table_view(u, p),
        table_present(u2, p0), table_windows(u2, p0) == table_windows(u, p0), table_lock(u2, p0) == table_lock(u, p0).with_reader(d),
        pagetable_range_windows_exist(table_windows(u, p0), table_range(u, d)),
    ensures pagetable_locks_consistent(u2),
{
    assert(table_op_holds_locks(u, d));
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        if p != p0 {
            assert(table_view(u2, p) == table_view(u, p));
            table_view_same_implies_held_by_ops_kept(u, u2, d, p);
        } else {
            assert(table_locks_held_by_ops_at(u, p0));
            assert forall|x: CpuId| #![trigger table_lock(u2, p0).readers().contains(x)] table_lock(u2, p0).readers().contains(x)
                implies reader_ok(u2, p0, x) by {};
            assert forall|w: WindowVa| #![trigger table_windows(u2, p0).dom().contains(w)] table_windows(u2, p0).dom().contains(w) implies window_held_by_op(u2, p0, w) by {
                assert(window_held_by_op(u, p0, w));
                let x = table_windows(u, p0)[w]->WriteLocked_writer;
                if table_windows(u, p0)[w] is WriteLocked && x != d { assert(other_cpu_unchanged(u, u2, x)); }
            };
        }
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_holds_locks(u2, c) && table_op_shape(u2, c) by {
        if c == d {
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, d)).contains(w)] va_range_2m_windows(table_range(u2, d)).contains(w)
                implies table_windows(u2, p0).dom().contains(w) by { assert(va_range_2m_windows(table_range(u, d)).contains(w)); };
        } else if table_proc(u2, c) != p0 {
            other_table_op_kept(u, u2, d, c, p0);
        } else {
            assert(other_cpu_unchanged(u, u2, c));
            assert(table_op(u, c) && table_op_holds_locks(u, c));
        }
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_holds_tables(u2, c) by {
        assert(other_cpu_unchanged(u, u2, c));
        assert(table_sharer(u, c) && sharer_holds_tables(u, c));
        assert(table_view(u2, table_proc(u, c)) == table_view(u, table_proc(u, c)));
        if sharer_child(u, c) is Some { assert(table_view(u2, sharer_child(u, c)->Some_0) == table_view(u, sharer_child(u, c)->Some_0)); }
    };
}

/// The exit step of `d` from `p0` outside the fill phase keeps pagetable lock consistency.
proof fn table_exit_implies_locks_consistent_kept(u: KernelU, u2: KernelU, d: CpuId, p0: RwLockProcessPtr)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), !table_killer(u, d), table_op(u, d), !table_filling(u, d), table_proc(u, d) == p0, !table_op(u2, d),
        !table_sharer(u2, d),
        forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] p != p0 ==> table_view(u2, p) == table_view(u, p),
        table_present(u2, p0), table_lock(u2, p0) == table_lock(u, p0).without_reader(d),
        table_windows(u2, p0) == pagetable_window_locks_after_unlocking_range(table_windows(u, p0), table_range(u, d)),
    ensures pagetable_locks_consistent(u2),
{
    assert(table_op_holds_locks(u, d));
    let rs = table_lock(u, p0).readers();
    let rd = table_range(u, d);
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        if p != p0 {
            assert(table_view(u2, p) == table_view(u, p));
            table_view_same_implies_held_by_ops_kept(u, u2, d, p);
        } else {
            assert(table_locks_held_by_ops_at(u, p0));
            assert forall|x: CpuId| #![trigger table_lock(u2, p0).readers().contains(x)] table_lock(u2, p0).readers().contains(x)
                implies reader_ok(u2, p0, x) by {
                assert(rs.contains(x) && x != d);
                assert(table_lock(u, p0).readers().contains(x));
                assert(other_cpu_unchanged(u, u2, x));
            };
            assert forall|w: WindowVa| #![trigger table_windows(u2, p0).dom().contains(w)] table_windows(u2, p0).dom().contains(w) implies window_held_by_op(u2, p0, w) by {
                assert(table_windows(u, p0).dom().contains(w));
                if !va_range_2m_windows(rd).contains(w) {
                    assert(window_held_by_op(u, p0, w));
                    if table_windows(u, p0)[w] is WriteLocked { assert(other_cpu_unchanged(u, u2, table_windows(u, p0)[w]->WriteLocked_writer)); }
                }
            };
        }
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_holds_locks(u2, c) && table_op_shape(u2, c) by {
        if table_proc(u2, c) != p0 {
            other_table_op_kept(u, u2, d, c, p0);
        } else {
            assert(other_cpu_unchanged(u, u2, c));
            assert(table_op(u, c) && table_op_holds_locks(u, c));
            assert(rs.contains(c) && rs.remove(d).contains(c));
            assert(!rs.remove(d).is_empty());
            let rc = table_range(u, c);
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)] va_range_2m_windows(table_range(u2, c)).contains(w)
                && table_windows(u2, p0).dom().contains(w) implies table_windows(u2, p0)[w] == (LockStateU::WriteLocked { writer: c }) by {
                assert(va_range_2m_windows(rc).contains(w));
                if va_range_2m_windows(rd).contains(w) { assert(table_windows(u, p0)[w] == (LockStateU::WriteLocked { writer: d })); }
            };
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)] va_range_2m_windows(table_range(u2, c)).contains(w)
                implies table_windows(u2, p0).dom().contains(w) by { assert(va_range_2m_windows(rc).contains(w)); };
        }
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_holds_tables(u2, c) by {
        assert(other_cpu_unchanged(u, u2, c));
        assert(table_sharer(u, c) && sharer_holds_tables(u, c));
        let p = table_proc(u, c);
        let rc = table_range(u, c);
        if p != p0 { assert(table_view(u2, p) == table_view(u, p)); }
        else {
            assert(rs.contains(c) && rs.remove(d).contains(c));
            assert(!rs.remove(d).is_empty());
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, c)).contains(w)] va_range_2m_windows(table_range(u2, c)).contains(w)
                && table_windows(u2, p0).dom().contains(w) implies table_windows(u2, p0)[w] == (LockStateU::WriteLocked { writer: c }) by {
                assert(va_range_2m_windows(rc).contains(w));
                if va_range_2m_windows(rd).contains(w) { assert(table_windows(u, p0)[w] == (LockStateU::WriteLocked { writer: d })); }
            };
        }
        if sharer_child(u, c) is Some { assert(table_view(u2, sharer_child(u, c)->Some_0) == table_view(u, sharer_child(u, c)->Some_0)); }
    };
}

/// Every traced step keeps pagetable lock consistency.
pub proof fn traced_step_implies_pagetable_locks_consistent_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), traced_label(l), labeled_step(l, u, u2, d), pagetable_locks_consistent(u),
    ensures
        pagetable_locks_consistent(u2),
        forall|p: RwLockProcessPtr| #![trigger table_windows(u2, p)]
            table_present(u, p) ==> table_present(u2, p) && table_windows(u, p).dom().subset_of(table_windows(u2, p).dom()),
{
    reveal(kernel_u_cpu_ownership_wf);
    assert forall|x: CpuId| #![trigger other_cpu_unchanged(u, u2, x)] x != d implies other_cpu_unchanged(u, u2, x) by {
        if index_valid(NUM_CPUS, x) {
            traced_other_step_implies_cpu_slice_unchanged(u, u2, l, d, x);
            cpu_slice_same_implies_other_cpu_unchanged(u, u2, x);
        }
    };
    let pd = cur_thread(u, d).owning_proc;
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); table_views_same_implies_locks_consistent_kept(u, u2, d); },
        StepLabel::NewEndpointFinish => {
            reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed);
            table_views_same_implies_locks_consistent_kept(u, u2, d);
        },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); table_views_same_implies_locks_consistent_kept(u, u2, d); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); table_views_same_implies_locks_consistent_kept(u, u2, d); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); table_views_same_implies_locks_consistent_kept(u, u2, d); },
        StepLabel::Mmap4kLeaf => {
            reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step);
            assert(table_op(u, d));
            assert(table_op_shape(u, d));
            table_views_same_implies_locks_consistent_kept(u, u2, d);
        },
        StepLabel::Unmap4kLeaf => {
            reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step);
            assert(table_op(u, d));
            assert(table_op_shape(u, d));
            table_views_same_implies_locks_consistent_kept(u, u2, d);
        },
        StepLabel::Unmap4kTlbFlush => {
            reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared);
            table_views_same_implies_locks_consistent_kept(u, u2, d);
        },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_va_flush_step); table_views_same_implies_locks_consistent_kept(u, u2, d); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); table_views_same_implies_locks_consistent_kept(u, u2, d); },
        StepLabel::Unmap4kRefund => {
            reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_refund_step); reveal(kernel_u_container_quota_4k_increased);
            table_views_same_implies_locks_consistent_kept(u, u2, d);
        },
        StepLabel::Mmap4kEnter { range, phase } => {
            reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step);
            table_enter_implies_locks_consistent_kept(u, u2, d, pd, range, phase is Fill);
        },
        StepLabel::Unmap4kEnter { range } => {
            reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step);
            table_enter_implies_locks_consistent_kept(u, u2, d, pd, range, false);
        },
        StepLabel::Mmap4kDowngrade => {
            reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step);
            assert(table_op(u, d));
            assert(table_op_shape(u, d));
            table_downgrade_implies_locks_consistent_kept(u, u2, d, pd);
        },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); table_exit_implies_locks_consistent_kept(u, u2, d, pd); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); table_exit_implies_locks_consistent_kept(u, u2, d, pd); },
        StepLabel::Mmap4kDirectory => {
            reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step);
            assert(table_op(u, d));
            assert(table_op_shape(u, d));
            let old_w = table_windows(u, pd);
            let new_w = table_windows(u2, pd);
            if cur_thread(u2, d).syscall_progress->Some_0->Mmap4k_directory is L3 {
                if !table_filling(u, d) { assert(table_op_holds_locks(u, d)); assert(false); }
                assert(!new_w.dom().subset_of(old_w.dom()));
                let w0 = choose|w0: WindowVa| new_w.dom().contains(w0) && !old_w.dom().contains(w0);
                assert(new_w == pagetable_window_locks_after_new_l2_page(old_w, spec_v2l4index(w0.va), spec_v2l3index(w0.va), table_range(u, d), d));
            }
            assert(old_w.dom().subset_of(new_w.dom()));
            assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) == table_present(u, p)
                && (table_present(u, p) ==> table_lock(u2, p) == table_lock(u, p) && table_windows(u, p).dom().subset_of(table_windows(u2, p).dom())) by {};
            assert forall|p: RwLockProcessPtr, w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)]
                table_present(u2, p) && table_windows(u2, p).dom().contains(w) implies window_kept_or_new(u, u2, d, p, w) by {};
            table_frame_implies_locks_consistent_kept(u, u2, d);
        },
        _ => {},
    }
    assert forall|p: RwLockProcessPtr| #![trigger table_windows(u2, p)]
        table_present(u, p) implies table_present(u2, p) && table_windows(u, p).dom().subset_of(table_windows(u2, p).dom()) by {
        assert(table_view(u2, p).0 == table_present(u2, p));
    };
}

/// Every cpu other than `d` keeps its cpu entry and running thread.
pub open spec fn others_slices_same(u: KernelU, u2: KernelU, d: CpuId) -> bool {
    forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && x != d
        ==> u2.cpu_array[x as int] == u.cpu_array[x as int] && (u.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x) == cur_thread(u, x))
}

/// A step that changes no 4K mapping keeps the VA progress of every cpu inside but `d`, and of `d` when given.
pub proof fn table_mappings_same_implies_vas_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        table_ops_vas(u), others_slices_same(u, u2, d), table_op(u2, d) ==> table_op_vas(u2, d), table_sharer(u2, d) ==> sharer_vas(u2, d),
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k,
    ensures table_ops_vas(u2),
{
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_vas(u2, c) by {
        if c != d {
            assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
            assert(table_sharer(u, c));
            assert(sharer_vas(u, c) && table_progress(u2, c) == table_progress(u, c) && table_proc(u2, c) == table_proc(u, c));
            assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k);
            let r = table_range(u, c);
            assert forall|k: int| #![trigger r.view()[k]] sharer_shared(u2, c) <= k < r.len implies table_mapping(u2, c).dom().contains(r.view()[k]) by {
                assert(table_mapping(u, c).dom().contains(r.view()[k]));
            };
            if sharer_child(u, c) is Some {
                let ch = sharer_child(u, c)->Some_0;
                assert(u2.process_map[ch].pagetable->Some_0.mapping_4k == u.process_map[ch].pagetable->Some_0.mapping_4k);
                assert forall|k: int| #![trigger r.view()[k]] sharer_shared(u2, c) <= k < r.len implies !u2.process_map[ch].pagetable->Some_0.mapping_4k.dom().contains(r.view()[k]) by {
                    assert(!u.process_map[ch].pagetable->Some_0.mapping_4k.dom().contains(r.view()[k]));
                };
            }
            assert(sharer_vas(u2, c));
        } else { assert(sharer_vas(u2, d)); }
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_vas(u2, c) by {
        if c != d {
            assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
            assert(table_op(u, c));
            assert(table_op_vas(u, c));
            assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k);
        }
    };
}

/// The next page index of `c`: mapped pages inside `mmap_4k`, cleared pages inside `unmap_4k`.
pub open spec fn table_index(u: KernelU, c: CpuId) -> usize {
    if table_progress(u, c) is Mmap4k { table_progress(u, c)->Mmap4k_mapped } else { table_progress(u, c)->Unmap4k_unmapped }
}

/// A leaf step of `d`, mapping (`map`) or clearing the next VA of its range, keeps the VA progress of every other cpu
/// inside: another cpu on the same table never has that VA in its range, since both hold its 2M window.
proof fn table_leaf_implies_vas_kept(u: KernelU, u2: KernelU, d: CpuId, map: bool)
    requires
        pagetable_locks_consistent(u), table_ops_vas(u), others_slices_same(u, u2, d), table_op(u, d), !table_filling(u, d),
        table_index(u, d) < table_range(u, d).len, map == table_progress(u, d) is Mmap4k,
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] p != table_proc(u, d)
            ==> u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k,
        map ==> u2.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k.dom()
            == u.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k.dom().insert(table_range(u, d).view()[table_index(u, d) as int]),
        !map ==> u2.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k.dom()
            == u.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k.dom().remove(table_range(u, d).view()[table_index(u, d) as int]),
        forall|va: VAddr| #![trigger u2.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k[va]] va != table_range(u, d).view()[table_index(u, d) as int]
            ==> u2.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k[va] == u.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k[va],
        table_op(u2, d) ==> table_op_vas(u2, d), !table_sharer(u2, d),
    ensures table_ops_vas(u2),
{
    assert(table_op_holds_locks(u, d) && table_op_shape(u, d));
    let p0 = table_proc(u, d);
    let rd = table_range(u, d);
    let v = rd.view()[table_index(u, d) as int];
    va_range_2m_windows_contains_window_of_first_n_pages(rd, rd.len as int);
    assert(va_range_2m_windows(rd).contains(window_of(v)));
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_vas(u2, c) by {
        assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
        assert(table_sharer(u, c));
        assert(sharer_vas(u, c) && sharer_holds_tables(u, c));
        let p = table_proc(u, c);
        let rc = table_range(u, c);
        if p != p0 { assert(u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k); }
        else if !map {
            va_range_2m_windows_contains_window_of_first_n_pages(rc, rc.len as int);
            assert forall|k: int| #![trigger rc.view()[k]] 0 <= k < rc.len implies rc.view()[k] != v by {
                if rc.view()[k] == v {
                    assert(va_range_2m_windows(rc).contains(window_of(v)));
                    assert(table_windows(u, p0).dom().contains(window_of(v)));
                    assert(table_windows(u, p0)[window_of(v)] == (LockStateU::WriteLocked { writer: d }));
                }
            };
        }
        if sharer_child(u, c) is Some {
            let ch = sharer_child(u, c)->Some_0;
            assert(u2.process_map[ch].pagetable->Some_0.mapping_4k == u.process_map[ch].pagetable->Some_0.mapping_4k);
        }
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_vas(u2, c) by {
        if c != d {
            assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
            assert(table_op(u, c));
            assert(table_op_vas(u, c));
            assert(table_op_holds_locks(u, c));
            assert(table_op_shape(u, c));
            if table_proc(u, c) != p0 { assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k); }
            else {
                let rc = table_range(u, c);
                va_range_2m_windows_contains_window_of_first_n_pages(rc, rc.len as int);
                assert forall|k: int| #![trigger rc.view()[k]] 0 <= k < rc.len implies rc.view()[k] != v by {
                    if rc.view()[k] == v {
                        assert(va_range_2m_windows(rc).contains(window_of(v)));
                        assert(table_windows(u, p0).dom().contains(window_of(v)));
                        assert(table_windows(u, p0)[window_of(v)] == (LockStateU::WriteLocked { writer: d }));
                    }
                };
            }
        }
    };
}

/// Every traced step keeps the VA progress of every cpu inside.
pub proof fn traced_step_implies_table_ops_vas_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), traced_label(l), labeled_step(l, u, u2, d), pagetable_locks_consistent(u), table_ops_vas(u),
    ensures table_ops_vas(u2),
{
    reveal(kernel_u_cpu_ownership_wf);
    assert forall|x: CpuId| #![trigger u2.cpu_array[x as int]] index_valid(NUM_CPUS, x) && x != d
        implies u2.cpu_array[x as int] == u.cpu_array[x as int] && (u.cpu_array[x as int].current_thread is Some ==> cur_thread(u2, x) == cur_thread(u, x)) by {
        traced_other_step_implies_cpu_slice_unchanged(u, u2, l, d, x);
    };
    if table_op(u, d) { assert(table_op_vas(u, d) && table_op_shape(u, d)); }
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::NewEndpointFinish => {
            reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed);
            table_mappings_same_implies_vas_kept(u, u2, d);
        },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Mmap4kEnter { range, phase } => { reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Unmap4kEnter { range } => { reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Mmap4kDirectory => { reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Unmap4kTlbFlush => {
            reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared);
            table_mappings_same_implies_vas_kept(u, u2, d);
        },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_va_flush_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Unmap4kRefund => {
            reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_refund_step); reveal(kernel_u_container_quota_4k_increased);
            table_mappings_same_implies_vas_kept(u, u2, d);
        },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); table_mappings_same_implies_vas_kept(u, u2, d); },
        StepLabel::Mmap4kLeaf => {
            reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step);
            let rd = table_range(u, d);
            let m = table_index(u, d) as int;
            assert forall|k: int| #![trigger rd.view()[k]] m + 1 <= k < rd.len implies !table_mapping(u2, d).dom().contains(rd.view()[k]) by { assert(rd.view()[k] != rd.view()[m]); };
            table_leaf_implies_vas_kept(u, u2, d, true);
        },
        StepLabel::Unmap4kLeaf => {
            reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step);
            let rd = table_range(u, d);
            let m = table_index(u, d) as int;
            assert forall|k: int| #![trigger rd.view()[k]] m + 1 <= k < rd.len
                implies table_mapping(u2, d).dom().contains(rd.view()[k]) && !table_mapping(u2, d)[rd.view()[k]].is_io by { assert(rd.view()[k] != rd.view()[m]); };
            table_leaf_implies_vas_kept(u, u2, d, false);
        },
        _ => {},
    }
}

/// Pagetable lock consistency and VA progress at `i` hold at every later index of a traced behaviour.
pub proof fn traced_behavior_implies_table_invariants_kept(b: Execution<Snap>, i: nat, k: nat)
    requires traced_behavior(b), i <= k, pagetable_locks_consistent(b(i).u), table_ops_vas(b(i).u),
    ensures pagetable_locks_consistent(b(k).u), table_ops_vas(b(k).u),
    decreases k - i,
{
    if k > i {
        let j = (k - 1) as nat;
        traced_behavior_implies_table_invariants_kept(b, i, j);
        assert(traced_step(b(j), b(j + 1)));
        traced_step_implies_table_ops_vas_kept(b(j).u, b(k).u, b(j).label, b(j).cpu);
        traced_step_implies_pagetable_locks_consistent_kept(b(j).u, b(k).u, b(j).label, b(j).cpu);
    }
}

/// Who can block a waiter on process `p`: a write hold on the pagetable belongs to a cpu filling it or to a killer
/// reclaiming it, a read hold to a cpu mapping or unmapping in it outside the fill phase, and a held window `w` to a cpu
/// inside `mmap_4k` or `unmap_4k` on `p` whose recorded range covers `w`.
pub proof fn pagetable_locks_consistent_implies_blockers_inside(u: KernelU, p: RwLockProcessPtr, x: CpuId, w: WindowVa)
    requires pagetable_locks_consistent(u), table_present(u, p),
    ensures
        table_lock(u, p) is WriteLocked ==> table_op(u, table_lock(u, p)->WriteLocked_writer) && table_proc(u, table_lock(u, p)->WriteLocked_writer) == p
            && table_filling(u, table_lock(u, p)->WriteLocked_writer)
            || table_killer(u, table_lock(u, p)->WriteLocked_writer) && table_killer_proc(u, table_lock(u, p)->WriteLocked_writer) == p
            || table_sharer(u, table_lock(u, p)->WriteLocked_writer) && sharer_child(u, table_lock(u, p)->WriteLocked_writer) == Some(p),
        table_lock(u, p).readers().contains(x) ==> table_op(u, x) && table_proc(u, x) == p && !table_filling(u, x) || table_sharer(u, x) && table_proc(u, x) == p,
        table_windows(u, p).dom().contains(w) && !(table_windows(u, p)[w] is Unlocked) ==> ({
            let h = table_windows(u, p)[w]->WriteLocked_writer;
            &&& table_windows(u, p)[w] is WriteLocked
            &&& table_op(u, h) && table_proc(u, h) == p || table_sharer(u, h) && (table_proc(u, h) == p || sharer_child(u, h) == Some(p))
            &&& va_range_2m_windows(table_range(u, h)).contains(w)
        }),
{
    assert(table_locks_held_by_ops_at(u, p));
    if table_windows(u, p).dom().contains(w) { assert(window_held_by_op(u, p, w)); }
}

/// Never blocked inside `unmap_4k`: the leaf step is enabled while pages remain, the flush steps once every page is
/// cleared, and the refund and exit steps, with the read hold on the pagetable that exiting drops, once the flush is recorded.
pub proof fn table_invariants_implies_unmap_4k_never_blocked(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), pagetable_locks_consistent(u), table_ops_vas(u), in_unmap_4k(u, c),
    ensures
        traced_next_pre(u, c),
        ({
            let prog = cur_thread(u, c).syscall_progress->Some_0;
            &&& prog->Unmap4k_unmapped < prog->Unmap4k_range.len && !prog->Unmap4k_flushed ==> unmap_4k_leaf_step_pre(u, c)
            &&& prog->Unmap4k_unmapped == prog->Unmap4k_range.len && !prog->Unmap4k_flushed ==> unmap_4k_flush_step_pre(u, c)
            &&& prog->Unmap4k_flushed ==> unmap_4k_refund_step_pre(u, c) && table_lock(u, table_proc(u, c)).read_held_by(c)
        }),
{
    reveal(kernel_u_cpu_ownership_wf); reveal(kernel_u_thread_ownership_wf);
    reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_refund_step_pre);
    assert(table_op(u, c) && table_op_holds_locks(u, c) && table_op_shape(u, c) && table_op_vas(u, c));
    assert(u.thread_map.dom().contains(u.cpu_array[c as int].current_thread->Some_0));
    let prog = cur_thread(u, c).syscall_progress->Some_0;
    if prog->Unmap4k_unmapped < prog->Unmap4k_range.len { assert(table_mapping(u, c).dom().contains(prog->Unmap4k_range.view()[prog->Unmap4k_unmapped as int])); }
}

/// The enabled steps inside `mmap_4k`: a held cpu can release, and a cpu reading or filled can map its next page while pages
/// remain and exit once every page is mapped. In the fill phase the downgrade step is enabled once every window of the range
/// exists, and a directory step while one is missing and the thread has more 4K quota than pages remain.
pub proof fn table_invariants_implies_mmap_4k_never_blocked_steps(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), pagetable_locks_consistent(u), table_ops_vas(u), in_mmap_4k(u, c),
    ensures ({
        let t = cur_thread(u, c);
        let prog = t.syscall_progress->Some_0;
        &&& t.syscall_progress is None ==> mmap_4k_release_step_pre(u, c)
        &&& t.syscall_progress is Some && !(prog->Mmap4k_phase is Fill) ==> traced_next_pre(u, c)
        &&& t.syscall_progress is Some && !(prog->Mmap4k_phase is Fill) && prog->Mmap4k_mapped < prog->Mmap4k_range.len ==> mmap_4k_leaf_step_pre(u, c)
        &&& t.syscall_progress is Some && !(prog->Mmap4k_phase is Fill) && prog->Mmap4k_mapped == prog->Mmap4k_range.len ==> mmap_4k_exit_step_pre(u, c)
        &&& t.syscall_progress is Some && prog->Mmap4k_phase is Fill && pagetable_range_windows_exist(table_windows(u, table_proc(u, c)), prog->Mmap4k_range)
            ==> mmap_4k_downgrade_step_pre(u, c)
        &&& t.syscall_progress is Some && prog->Mmap4k_phase is Fill && !pagetable_range_windows_exist(table_windows(u, table_proc(u, c)), prog->Mmap4k_range)
            && t.quota_4k > prog->Mmap4k_range.len ==> mmap_4k_directory_step_pre(u, c)
    }),
{
    reveal(kernel_u_cpu_ownership_wf);
    reveal(mmap_4k_release_step_pre); reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_directory_step_pre);
    assert(u.thread_map.dom().contains(u.cpu_array[c as int].current_thread->Some_0));
    if cur_thread(u, c).syscall_progress is Some {
        assert(table_op(u, c));
        assert(table_op_holds_locks(u, c));
        assert(table_op_shape(u, c));
        assert(table_op_vas(u, c));
        let prog = cur_thread(u, c).syscall_progress->Some_0;
        if prog->Mmap4k_mapped < prog->Mmap4k_range.len { assert(!table_mapping(u, c).dom().contains(prog->Mmap4k_range.view()[prog->Mmap4k_mapped as int])); }
    }
}
} // verus!
