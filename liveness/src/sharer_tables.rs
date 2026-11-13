//! Round 9: the pagetable lock invariants across the steps of a cpu inside `new_process`. Entering read-holds its
//! process's pagetable and write-holds the existing 2M windows of its range there, publishing adds the child with its
//! pagetable write-held, a directory step adds windows to the child, a leaf step maps one page of the range into the child,
//! and finishing drops every hold. The directory step reuses `table_frame_implies_locks_consistent_kept`.
use vstd::prelude::*;
use crate::*;
use crate::pagetable_locks::*;
use veriflat_map_4k::*;

verus! {
/// The enter step of `d` into `new_process` on `p0` for range `r` keeps pagetable lock consistency: it read-locks the
/// pagetable, which no cpu fills, and write-locks the windows of `r`, which are free.
pub proof fn sharer_enter_implies_locks_consistent_kept(u: KernelU, u2: KernelU, d: CpuId, p0: RwLockProcessPtr, r: VaRange4K)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), !table_killer(u, d), !table_op(u, d), !table_sharer(u, d), !table_op(u2, d),
        !table_killer(u2, d), table_sharer(u2, d), table_proc(u2, d) == p0, table_range(u2, d) == r, sharer_child(u2, d) is None, r.wf(), r.len > 0,
        forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] p != p0 ==> table_view(u2, p) == table_view(u, p),
        table_present(u, p0), table_present(u2, p0), !(table_lock(u, p0) is WriteLocked), table_lock(u2, p0) == table_lock(u, p0).with_reader(d),
        pagetable_range_windows_unlocked(table_windows(u, p0), r), table_windows(u2, p0) == pagetable_window_locks_after_locking_range(table_windows(u, p0), r, d),
    ensures pagetable_locks_consistent(u2),
{
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        if p != p0 {
            assert(table_view(u2, p) == table_view(u, p));
            table_view_same_implies_held_by_ops_kept(u, u2, d, p);
        } else {
            assert(table_locks_held_by_ops_at(u, p0));
            assert forall|x: CpuId| #![trigger table_lock(u2, p0).readers().contains(x)] table_lock(u2, p0).readers().contains(x) implies reader_ok(u2, p0, x) by {
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
        if table_proc(u2, c) != p0 {
            other_table_op_kept(u, u2, d, c, p0);
        } else {
            assert(other_cpu_unchanged(u, u2, c));
            assert(table_op(u, c) && table_op_holds_locks(u, c));
            assert(table_lock(u, p0).readers().contains(c));
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
        if c == d {
            assert forall|w: WindowVa| #![trigger va_range_2m_windows(table_range(u2, d)).contains(w)] va_range_2m_windows(table_range(u2, d)).contains(w)
                && table_windows(u2, p0).dom().contains(w) implies table_windows(u2, p0)[w] == (LockStateU::WriteLocked { writer: d }) by {};
        } else {
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
        }
    };
}

/// The publish step of `d` adds child `ch`, a new process with its pagetable write-held by `d` and no window, and keeps
/// pagetable lock consistency.
pub proof fn sharer_publish_implies_locks_consistent_kept(u: KernelU, u2: KernelU, d: CpuId, ch: RwLockProcessPtr)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), table_sharer(u, d), table_sharer(u2, d), !table_op(u2, d), !table_killer(u2, d),
        table_proc(u2, d) == table_proc(u, d), table_range(u2, d) == table_range(u, d), sharer_child(u, d) is None, sharer_child(u2, d) == Some(ch),
        !u.process_map.dom().contains(ch), u2.process_map.dom() == u.process_map.dom().insert(ch),
        forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] p != ch && u.process_map.dom().contains(p) ==> table_view(u2, p) == table_view(u, p),
        table_present(u2, ch), table_lock(u2, ch) == (LockStateU::WriteLocked { writer: d }), table_windows(u2, ch).dom() == Set::<WindowVa>::empty(),
    ensures pagetable_locks_consistent(u2),
{
    assert(sharer_holds_tables(u, d));
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        if p != ch {
            assert(table_view(u2, p) == table_view(u, p));
            assert(table_locks_held_by_ops_at(u, p));
            let lk = table_lock(u, p);
            if lk is WriteLocked && lk->WriteLocked_writer != d { assert(other_cpu_unchanged(u, u2, lk->WriteLocked_writer)); }
            assert forall|x: CpuId| #![trigger table_lock(u2, p).readers().contains(x)] table_lock(u2, p).readers().contains(x) implies reader_ok(u2, p, x) by {
                assert(table_lock(u, p).readers().contains(x));
                if x != d { assert(other_cpu_unchanged(u, u2, x)); }
            };
            assert forall|w: WindowVa| #![trigger table_windows(u2, p).dom().contains(w)] table_windows(u2, p).dom().contains(w) implies window_held_by_op(u2, p, w) by {
                assert(table_windows(u, p).dom().contains(w) && window_held_by_op(u, p, w));
                let x = table_windows(u, p)[w]->WriteLocked_writer;
                if table_windows(u, p)[w] is WriteLocked && x != d { assert(other_cpu_unchanged(u, u2, x)); }
            };
        } else {
            assert forall|w: WindowVa| #![trigger table_windows(u2, ch).dom().contains(w)] table_windows(u2, ch).dom().contains(w) implies window_held_by_op(u2, ch, w) by {
                assert(table_windows(u2, ch).dom().contains(w));
            };
        }
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_holds_locks(u2, c) && table_op_shape(u2, c) by {
        assert(other_cpu_unchanged(u, u2, c));
        assert(table_op(u, c) && table_op_holds_locks(u, c));
        other_table_op_kept(u, u2, d, c, ch);
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_holds_tables(u2, c) by {
        if c != d {
            assert(other_cpu_unchanged(u, u2, c));
            assert(table_sharer(u, c) && sharer_holds_tables(u, c));
            if sharer_child(u, c) is Some { assert(table_view(u2, sharer_child(u, c)->Some_0) == table_view(u, sharer_child(u, c)->Some_0)); }
        }
        assert(table_view(u2, table_proc(u, c)) == table_view(u, table_proc(u, c)));
    };
}

/// The finish step of `d` drops its read hold on `p0` and the windows of its range there, and unlocks child `ch` with
/// its windows; it keeps pagetable lock consistency.
pub proof fn sharer_finish_implies_locks_consistent_kept(u: KernelU, u2: KernelU, d: CpuId, p0: RwLockProcessPtr, ch: RwLockProcessPtr)
    requires
        pagetable_locks_consistent(u), others_unchanged(u, u2, d), table_sharer(u, d), !table_sharer(u2, d), !table_op(u2, d), !table_killer(u2, d),
        table_proc(u, d) == p0, sharer_child(u, d) == Some(ch),
        forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] p != p0 && p != ch ==> table_view(u2, p) == table_view(u, p),
        table_present(u2, p0), table_lock(u2, p0) == table_lock(u, p0).without_reader(d),
        table_windows(u2, p0) == pagetable_window_locks_after_unlocking_range(table_windows(u, p0), table_range(u, d)),
        table_present(u2, ch), table_lock(u2, ch) is Unlocked,
        table_windows(u2, ch) == pagetable_window_locks_after_unlocking_range(table_windows(u, ch), table_range(u, d)),
    ensures pagetable_locks_consistent(u2),
{
    assert(sharer_holds_tables(u, d));
    let rs = table_lock(u, p0).readers();
    let rd = table_range(u, d);
    assert forall|p: RwLockProcessPtr| #![trigger table_present(u2, p)] table_present(u2, p) implies table_locks_held_by_ops_at(u2, p) by {
        if p != p0 && p != ch {
            assert(table_view(u2, p) == table_view(u, p));
            table_view_same_implies_held_by_ops_kept(u, u2, d, p);
        } else if p == p0 {
            assert(table_locks_held_by_ops_at(u, p0));
            assert forall|x: CpuId| #![trigger table_lock(u2, p0).readers().contains(x)] table_lock(u2, p0).readers().contains(x) implies reader_ok(u2, p0, x) by {
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
        } else {
            assert forall|w: WindowVa| #![trigger table_windows(u2, ch).dom().contains(w)] table_windows(u2, ch).dom().contains(w) implies window_held_by_op(u2, ch, w) by {
                assert(table_windows(u, ch).dom().contains(w));
                if !va_range_2m_windows(rd).contains(w) {
                    assert(window_held_by_op(u, ch, w));
                    if table_windows(u, ch)[w] is WriteLocked {
                        let x = table_windows(u, ch)[w]->WriteLocked_writer;
                        if table_op(u, x) { assert(table_op_holds_locks(u, x)); } else { assert(sharer_holds_tables(u, x)); }
                    }
                }
            };
        }
    };
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_holds_locks(u2, c) && table_op_shape(u2, c) by {
        assert(other_cpu_unchanged(u, u2, c));
        assert(table_op(u, c) && table_op_holds_locks(u, c));
        let p = table_proc(u, c);
        if p != p0 {
            assert(table_view(u2, p) == table_view(u, p));
        } else {
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

/// The publish step of `d` keeps VA progress: no mapping changes, and the new child maps nothing.
pub proof fn sharer_publish_implies_vas_kept(u: KernelU, u2: KernelU, d: CpuId, ch: RwLockProcessPtr)
    requires
        pagetable_locks_consistent(u), table_ops_vas(u), others_slices_same(u, u2, d), table_sharer(u, d), table_sharer(u2, d), !table_op(u2, d),
        table_progress(u, d) is NewProcess, sharer_child(u2, d) == Some(ch), !u.process_map.dom().contains(ch), table_proc(u2, d) == table_proc(u, d),
        table_range(u2, d) == table_range(u, d), sharer_shared(u2, d) == 0,
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] u.process_map.dom().contains(p)
            ==> u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k,
        u2.process_map[ch].pagetable->Some_0.mapping_4k.dom() == Set::<VAddr>::empty(),
    ensures table_ops_vas(u2),
{
    assert(sharer_holds_tables(u, d) && sharer_vas(u, d));
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_vas(u2, c) by {
        assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
        assert(table_op(u, c) && table_op_vas(u, c) && table_op_holds_locks(u, c));
        assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k);
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_vas(u2, c) by {
        if c != d {
            assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
            assert(table_sharer(u, c));
            assert(sharer_vas(u, c) && sharer_holds_tables(u, c));
            if sharer_child(u, c) is Some {
                let cc = sharer_child(u, c)->Some_0;
                assert(u2.process_map[cc].pagetable->Some_0.mapping_4k == u.process_map[cc].pagetable->Some_0.mapping_4k);
            }
        } else {
            assert(sharer_shared(u, d) == 0 && table_present(u, table_proc(u, d)));
            assert forall|k: int| #![trigger table_range(u2, d).view()[k]] 0 <= k < table_range(u2, d).len
                implies !u2.process_map[ch].pagetable->Some_0.mapping_4k.dom().contains(table_range(u2, d).view()[k]) by {};
        }
        assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k);
    };
}

/// A leaf step of `d` maps the next page of its range into its child and keeps VA progress: no other cpu works on the
/// child, which `d` write-holds.
pub proof fn sharer_leaf_implies_vas_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires
        pagetable_locks_consistent(u), table_ops_vas(u), others_slices_same(u, u2, d), table_sharer(u, d), table_sharer(u2, d), !table_op(u2, d),
        sharer_child(u, d) is Some, sharer_child(u2, d) == sharer_child(u, d), table_proc(u2, d) == table_proc(u, d), table_range(u2, d) == table_range(u, d),
        0 <= sharer_shared(u, d) < table_range(u, d).len, sharer_shared(u2, d) == sharer_shared(u, d) + 1,
        forall|p: RwLockProcessPtr| #![trigger u2.process_map[p]] p != sharer_child(u, d)->Some_0
            ==> u2.process_map[p].pagetable->Some_0.mapping_4k == u.process_map[p].pagetable->Some_0.mapping_4k,
        u2.process_map[sharer_child(u, d)->Some_0].pagetable->Some_0.mapping_4k.dom()
            == u.process_map[sharer_child(u, d)->Some_0].pagetable->Some_0.mapping_4k.dom().insert(table_range(u, d).view()[sharer_shared(u, d)]),
    ensures table_ops_vas(u2),
{
    let ch = sharer_child(u, d)->Some_0;
    let rd = table_range(u, d);
    let m = sharer_shared(u, d);
    assert(sharer_holds_tables(u, d) && sharer_vas(u, d));
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) implies table_op_vas(u2, c) by {
        assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
        assert(table_op(u, c) && table_op_vas(u, c) && table_op_holds_locks(u, c));
        assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k);
    };
    assert forall|c: CpuId| #![trigger table_sharer(u2, c)] table_sharer(u2, c) implies sharer_vas(u2, c) by {
        if c != d {
            assert(u2.cpu_array[c as int] == u.cpu_array[c as int]);
            assert(table_sharer(u, c));
            assert(sharer_vas(u, c) && sharer_holds_tables(u, c));
            assert(u2.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, c)].pagetable->Some_0.mapping_4k);
            if sharer_child(u, c) is Some {
                let cc = sharer_child(u, c)->Some_0;
                assert(u2.process_map[cc].pagetable->Some_0.mapping_4k == u.process_map[cc].pagetable->Some_0.mapping_4k);
            }
        } else {
            assert(u2.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k == u.process_map[table_proc(u, d)].pagetable->Some_0.mapping_4k);
            assert forall|k: int| #![trigger rd.view()[k]] m + 1 <= k < rd.len implies !u2.process_map[ch].pagetable->Some_0.mapping_4k.dom().contains(rd.view()[k]) by {
                assert(rd.view()[k] != rd.view()[m]);
            };
        }
    };
}
} // verus!
