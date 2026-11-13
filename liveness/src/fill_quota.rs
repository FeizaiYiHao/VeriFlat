//! Round 7: the fill phase of `mmap_4k` is never blocked. A filling cpu keeps 4K quota for every page of its range plus two
//! directory pages for every page whose 2M window is missing: an L3 directory adds a missing window of the range, which
//! holds a page of the range, and an L4 directory never follows an L4 one. While a window is missing the quota exceeds the
//! page count, so a directory step is enabled; once every window exists the downgrade step is.
use vstd::prelude::*;
use vstd::set_lib::*;
use crate::*;
use crate::trace::*;
use crate::frame::*;
use crate::pagetable_locks::*;
use veriflat_map_4k::*;
use veriflat_syscall_mmap_4k::syscall_mmap_4k::syscall_mmap_4k_spec::*;
use veriflat_syscall_unmap_4k::syscall_unmap_4k::syscall_unmap_4k_spec::*;
use veriflat_syscall_new_thread::syscall_new_endpoint::syscall_new_endpoint_spec::*;
use veriflat_syscall_alloc_quota::syscall_alloc_quota::syscall_alloc_quota_spec::*;

verus! {
/// The 2M window that page `k` of `r` lies in.
pub open spec fn range_page_window(r: VaRange4K, k: int) -> WindowVa {
    let va = r.view()[k];
    WindowVa { va: spec_index2va((spec_v2l4index(va), spec_v2l3index(va), spec_v2l2index(va), 0usize)) }
}

/// The pages of `r` whose 2M window `m` lacks.
pub open spec fn missing_pages(m: Map<WindowVa, LockStateU>, r: VaRange4K) -> Set<int> {
    set_int_range(0, r.len as int).filter(|k: int| !m.dom().contains(range_page_window(r, k)))
}

/// Filling cpu `c` has 4K quota for every page of its range and two directory pages for every page whose window is missing,
/// less one right after an L4 directory.
pub open spec fn fill_quota_at(u: KernelU, c: CpuId) -> bool {
    let prog = table_progress(u, c);
    cur_thread(u, c).quota_4k + (if prog->Mmap4k_directory is L4 { 1int } else { 0int })
        >= prog->Mmap4k_range.len + 2 * missing_pages(table_windows(u, table_proc(u, c)), prog->Mmap4k_range).len()
}

/// Every filling cpu has its fill quota.
pub open spec fn fill_quota(u: KernelU) -> bool { forall|c: CpuId| #![trigger table_op(u, c)] table_op(u, c) && table_filling(u, c) ==> fill_quota_at(u, c) }

/// `fill_quota` at filling cpu `c`.
pub proof fn fill_quota_implies_fill_quota_at(u: KernelU, c: CpuId)
    requires fill_quota(u), table_op(u, c), table_filling(u, c),
    ensures fill_quota_at(u, c),
{}

/// Every 2M window of `r` holds a page of `r`, the returned one.
pub proof fn range_window_implies_page_in_window(r: VaRange4K, w: WindowVa) -> (k: int)
    requires r.wf(), r.len > 0, va_range_2m_windows(r).contains(w),
    ensures 0 <= k < r.len, range_page_window(r, k) == w,
{
    let first = spec_va2index(r.start);
    let last = r.view()[r.len - 1];
    r.wf_implies_view_index_is_start_plus_offset();
    assert(r.view()[0] == r.start && last == spec_va_add_range(r.start, (r.len - 1) as usize));
    spec_va_4k_valid_index_roundtrip(r.start);
    spec_va_4k_valid_index_roundtrip(last);
    let x = w.va;
    let idx = (spec_v2l4index(x), spec_v2l3index(x), spec_v2l2index(x), 0usize);
    spec_va_2m_valid_index_roundtrip(x);
    spec_index2va_2m_valid(idx.0, idx.1, idx.2);
    if x <= r.start {
        spec_index2va_le_implies_4k_indices_lex_le(idx, first);
        assert(range_page_window(r, 0).va == x);
        0
    } else {
        if last < x { spec_index2va_le_implies_4k_indices_lex_le(spec_va2index(last), idx); }
        let start = r.start;
        assert(x % 4096 == 0 && start % 4096 == 0) by (bit_vector) requires spec_va_2m_valid(x), spec_va_4k_valid(start);
        let page = ((x - r.start) / 4096) as int;
        assert(r.start + page * 4096 == x && 0 <= page < r.len) by (nonlinear_arith)
            requires x % 4096 == 0, r.start % 4096 == 0, r.start < x, x <= r.start + (r.len - 1) * 4096, page == (x - r.start) / 4096;
        assert(r.view()[page] == spec_va_add_range(r.start, page as usize));
        assert(range_page_window(r, page).va == x);
        page
    }
}

/// At most every page of `r` is missing.
pub proof fn missing_pages_len_le_range_len(m: Map<WindowVa, LockStateU>, r: VaRange4K)
    ensures missing_pages(m, r).len() <= r.len,
{
    lemma_int_range(0, r.len as int);
    set_int_range(0, r.len as int).lemma_len_filter(|k: int| !m.dom().contains(range_page_window(r, k)));
}

/// More windows leave no more pages missing, and a new window of `r` holding page `k` leaves fewer.
pub proof fn windows_grown_implies_missing_pages_shrunk(m: Map<WindowVa, LockStateU>, m2: Map<WindowVa, LockStateU>, r: VaRange4K, k: int)
    requires m.dom().subset_of(m2.dom()),
    ensures
        missing_pages(m2, r).len() <= missing_pages(m, r).len(),
        0 <= k < r.len && !m.dom().contains(range_page_window(r, k)) && m2.dom().contains(range_page_window(r, k))
            ==> missing_pages(m2, r).len() < missing_pages(m, r).len(),
{
    lemma_int_range(0, r.len as int);
    let s = missing_pages(m, r);
    let s2 = missing_pages(m2, r);
    assert(s2.subset_of(s));
    lemma_len_subset(s2, s);
    if 0 <= k < r.len && !m.dom().contains(range_page_window(r, k)) && m2.dom().contains(range_page_window(r, k)) {
        assert(s.contains(k) && !s2.contains(k));
        assert(s2.subset_of(s.remove(k)));
        lemma_len_subset(s2, s.remove(k));
    }
}

/// A missing window of `r` leaves some page missing.
pub proof fn window_missing_implies_missing_pages_nonempty(m: Map<WindowVa, LockStateU>, r: VaRange4K)
    requires r.wf(), r.len > 0, !pagetable_range_windows_exist(m, r),
    ensures missing_pages(m, r).len() > 0,
{
    lemma_int_range(0, r.len as int);
    let w = choose|w: WindowVa| #![trigger va_range_2m_windows(r).contains(w)] va_range_2m_windows(r).contains(w) && !m.dom().contains(w);
    let k = range_window_implies_page_in_window(r, w);
    assert(missing_pages(m, r).contains(k));
    assert(missing_pages(m, r).remove(k).len() + 1 == missing_pages(m, r).len());
}

/// The fill quota of the cpu `d` that steps keeps holding.
proof fn traced_own_step_implies_fill_quota_at(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), traced_label(l), labeled_step(l, u, u2, d), pagetable_locks_consistent(u), fill_quota(u), table_op(u2, d), table_filling(u2, d),
    ensures fill_quota_at(u2, d),
{
    reveal(kernel_u_cpu_ownership_wf);
    match l {
        StepLabel::NewEndpointEnter { slot } => { reveal(new_endpoint_enter_step_pre); reveal(new_endpoint_enter_step); },
        StepLabel::NewEndpointFinish => { reveal(new_endpoint_finish_step_pre); reveal(new_endpoint_finish_step); reveal(kernel_u_new_endpoint_changed); },
        StepLabel::AllocQuota4k { alloc_amount } => { reveal(alloc_quota_4k_step_pre); reveal(kernel_u_only_process_quota_4k_changed); },
        StepLabel::Mmap4kHold { range } => { reveal(mmap_4k_hold_step_pre); reveal(mmap_4k_hold_step); },
        StepLabel::Mmap4kRelease => { reveal(mmap_4k_release_step_pre); reveal(mmap_4k_release_step); },
        StepLabel::Mmap4kLeaf => { reveal(mmap_4k_leaf_step_pre); reveal(mmap_4k_leaf_step); },
        StepLabel::Unmap4kLeaf => { reveal(unmap_4k_leaf_step_pre); reveal(unmap_4k_leaf_step); },
        StepLabel::Unmap4kTlbFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_flush_step); reveal(kernel_u_cpu_tlb_cleared); },
        StepLabel::Unmap4kTlbVaFlush => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_tlb_va_flush_step); },
        StepLabel::Unmap4kFlushed => { reveal(unmap_4k_flush_step_pre); reveal(unmap_4k_flushed_step); },
        StepLabel::Unmap4kRefund => { reveal(unmap_4k_refund_step_pre); reveal(kernel_u_container_quota_4k_increased); },
        StepLabel::Unmap4kEnter { range } => { reveal(unmap_4k_enter_step_pre); reveal(unmap_4k_enter_step); },
        StepLabel::Mmap4kDowngrade => { reveal(mmap_4k_downgrade_step_pre); reveal(mmap_4k_downgrade_step); },
        StepLabel::Mmap4kExit => { reveal(mmap_4k_exit_step_pre); reveal(mmap_4k_exit_step); },
        StepLabel::Unmap4kExit => { reveal(unmap_4k_refund_step_pre); reveal(unmap_4k_exit_step); },
        StepLabel::Mmap4kEnter { range, phase } => {
            reveal(mmap_4k_enter_step_pre); reveal(mmap_4k_enter_step);
            missing_pages_len_le_range_len(table_windows(u2, table_proc(u2, d)), range);
        },
        StepLabel::Mmap4kDirectory => {
            reveal(mmap_4k_directory_step_pre); reveal(mmap_4k_directory_step);
            traced_step_implies_pagetable_locks_consistent_kept(u, u2, l, d);
            assert(table_op(u, d) && table_filling(u, d));
            fill_quota_implies_fill_quota_at(u, d);
            let p = table_proc(u, d);
            let r = table_range(u, d);
            assert(table_op_holds_locks(u, d));
            let old_w = table_windows(u, p);
            let new_w = table_windows(u2, p);
            if table_progress(u2, d)->Mmap4k_directory is L3 {
                assert(exists|w0: WindowVa| #![trigger new_w.dom().contains(w0)] new_w.dom().contains(w0) && va_range_2m_windows(r).contains(w0) && !old_w.dom().contains(w0));
                let w0 = choose|w0: WindowVa| #![trigger new_w.dom().contains(w0)] new_w.dom().contains(w0) && va_range_2m_windows(r).contains(w0) && !old_w.dom().contains(w0);
                assert(table_op_shape(u, d));
                let k = range_window_implies_page_in_window(r, w0);
                windows_grown_implies_missing_pages_shrunk(old_w, new_w, r, k);
            } else {
                windows_grown_implies_missing_pages_shrunk(old_w, new_w, r, 0);
            }
        },
        _ => {},
    }
}

/// Every traced step keeps the fill quota.
pub proof fn traced_step_implies_fill_quota_kept(u: KernelU, u2: KernelU, l: StepLabel, d: CpuId)
    requires kernel_u_ownership_wf(u), traced_label(l), labeled_step(l, u, u2, d), pagetable_locks_consistent(u), fill_quota(u),
    ensures fill_quota(u2),
{
    traced_step_implies_pagetable_locks_consistent_kept(u, u2, l, d);
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) && table_filling(u2, c) implies fill_quota_at(u2, c) by {
        if c != d {
            traced_other_step_implies_cpu_slice_unchanged(u, u2, l, d, c);
            assert(table_op(u, c));
            assert(table_filling(u, c));
            assert(table_op_holds_locks(u, c));
            fill_quota_implies_fill_quota_at(u, c);
            let p = table_proc(u, c);
            windows_grown_implies_missing_pages_shrunk(table_windows(u, p), table_windows(u2, p), table_range(u, c), 0);
        } else {
            traced_own_step_implies_fill_quota_at(u, u2, l, d);
        }
    };
}

/// A step that keeps every other cpu and every pagetable view, with `d` outside `mmap_4k` and `unmap_4k` after it, keeps
/// the fill quota.
pub proof fn tables_kept_implies_fill_quota_kept(u: KernelU, u2: KernelU, d: CpuId)
    requires fill_quota(u), others_kept(u, u2, d), forall|p: RwLockProcessPtr| #![trigger table_view(u2, p)] table_view(u2, p) == table_view(u, p), !table_op(u2, d),
    ensures fill_quota(u2),
{
    assert forall|c: CpuId| #![trigger table_op(u2, c)] table_op(u2, c) && table_filling(u2, c) implies fill_quota_at(u2, c) by {
        assert(cpu_kept(u, u2, c));
        assert(table_op(u, c) && table_filling(u, c));
        fill_quota_implies_fill_quota_at(u, c);
        assert(table_view(u2, table_proc(u, c)) == table_view(u, table_proc(u, c)));
    };
}

/// Never blocked inside `mmap_4k`, the fill phase included: with every window of the range in place the downgrade step is
/// enabled, and while one is missing the fill quota exceeds the page count, so a directory step is.
pub proof fn table_invariants_implies_mmap_4k_never_blocked(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), pagetable_locks_consistent(u), table_ops_vas(u), fill_quota(u), in_mmap_4k(u, c),
    ensures traced_next_pre(u, c),
{
    reveal(mmap_4k_release_step_pre);
    table_invariants_implies_mmap_4k_never_blocked_steps(u, c);
    let t = cur_thread(u, c);
    if t.syscall_progress is Some && t.syscall_progress->Some_0->Mmap4k_phase is Fill {
        assert(table_op(u, c) && table_filling(u, c) && table_op_shape(u, c));
        fill_quota_implies_fill_quota_at(u, c);
        let r = table_range(u, c);
        if !pagetable_range_windows_exist(table_windows(u, table_proc(u, c)), r) { window_missing_implies_missing_pages_nonempty(table_windows(u, table_proc(u, c)), r); }
    }
}
} // verus!
