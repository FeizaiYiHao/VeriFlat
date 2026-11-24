//! Lock-order deadlock freedom on the kernel's own `KernelK` and `LocalContext`.
//!
//! `kernel_obj_lock_id` per family (arm; locker whose `lock_id_acyclic` check uses it, under
//! `src/kernel/implementation/locker_unlocker/`; a waiter's wanted id against the K id):
//! - Page `pg_arr.lock_id_by_index`, locker_unlocker_page.rs:85, `=`
//! - Cpu `cpu_arr.lock_id_by_index`, locker_unlocker_cpu.rs:61, `=`
//! - PcidNeedFlush `pcid_needflush.lock_id_by_index`, locker_unlocker_pcid_needflush.rs:48, `=`
//! - CpuOfflineFlag `cpu_offline_mp[f].flags.lock_id_by_index`, locker_unlocker_cpu_offline_flag.rs:82, `=`
//! - Container `ctn_mp.lock_id_by_key`, locker_unlocker_container.rs:174 (`dynamic_container_lock_id` of the requested
//!   owner), `<=`: a waiter spins only on a holder whose recorded owner is at or above the requested one
//!   (`src/locks/lock_inner_t.rs:164`)
//! - Process / Thread / Endpoint / PcidAllocator / CpuSet / PageTable / IommuTable `*_mp.lock_id_by_key`,
//!   locker_unlocker_process.rs:102, _thread.rs:15 and :155, _endpoint.rs:159, _pcid_allocator.rs:111, _cpu_set.rs:41
//!   (and :332, `rlock_cpu_set_unless_killed`, unmarked sets only),
//!   _pagetable.rs:79, _iommu_table.rs:47, `=`
//! - SchedulerShard `sched_mp[s].shards.lock_id_by_index`, locker_unlocker_scheduler.rs:51, `=`
//! - PageTableWindow `window_lock_id_of`, locker_unlocker_pagetable_window.rs:118 and
//!   `src/pagetable_concurrent/pagetable_concurrent_lock.rs:21` (`window_lock_id` of the same window), `=`
//! - IommuRootTable `irt.lock_id()`, locker_unlocker_iommu_root_table.rs:39, `=`
//! - Allocator quota / cache / global pool per size `allc_*_mp[a].{quota.lock_id(), cpu_caches.lock_id_by_index,
//!   global_pool.lock_id()}`, locker_unlocker_quota_ordered.rs:45, _allocator_cache*.rs, _allocator_global_pool*.rs, `=`
//!
//! What these theorems leave to the TCB or to written argument is listed in the crate docs (`lib.rs`).
use vstd::prelude::*;
use crate::*;

verus! {
/// The ordering id `krnl` gives lock object `obj`: in each arm the id the blocking lock primitive of that family checks
/// `lock_id_acyclic` against.
pub open spec fn kernel_obj_lock_id(krnl: &KernelK, obj: KernelObjId) -> LockId {
    match obj {
        KernelObjId::Page(pg_idx) => krnl.pg_arr.lock_id_by_index(pg_idx),
        KernelObjId::Cpu(cpu_id) => krnl.cpu_arr.lock_id_by_index(cpu_id),
        KernelObjId::PcidNeedFlush(cpu_id, pcid) => krnl.pcid_needflush.lock_id_by_index(cpu_id, pcid),
        KernelObjId::CpuOfflineFlag(flags_ptr, cpu_id) => krnl.cpu_offline_mp.spec_index(flags_ptr).flags.lock_id_by_index(cpu_id),
        KernelObjId::Container(ctn_ptr) => krnl.ctn_mp.lock_id_by_key(ctn_ptr),
        KernelObjId::Process(prc_ptr) => krnl.prc_mp.lock_id_by_key(prc_ptr),
        KernelObjId::Thread(thrd_ptr) => krnl.thrd_mp.lock_id_by_key(thrd_ptr),
        KernelObjId::Endpoint(ep_ptr) => krnl.ep_mp.lock_id_by_key(ep_ptr),
        KernelObjId::SchedulerShard(sched_ptr, cpu_id) => krnl.sched_mp.spec_index(sched_ptr).shards.lock_id_by_index(cpu_id),
        KernelObjId::PcidAllocator(allc_ptr) => krnl.pcid_allc_mp.lock_id_by_key(allc_ptr),
        KernelObjId::CpuSet(cpu_set_ptr) => krnl.cpu_set_mp.lock_id_by_key(cpu_set_ptr),
        KernelObjId::PageTable(pagetable_ptr) => krnl.pt_mp.lock_id_by_key(pagetable_ptr),
        KernelObjId::PageTableWindow(root, w) => window_lock_id_of(root, w),
        KernelObjId::IommuTable(iommu_table_ptr) => krnl.it_mp.lock_id_by_key(iommu_table_ptr),
        KernelObjId::IommuRootTable(_) => krnl.irt.lock_id(),
        KernelObjId::AllocatorQuota(PageSize::SZ4k, alloc_ptr) => krnl.allc_4k_mp.spec_index(alloc_ptr).quota.lock_id(),
        KernelObjId::AllocatorQuota(PageSize::SZ2m, alloc_ptr) => krnl.allc_2m_mp.spec_index(alloc_ptr).quota.lock_id(),
        KernelObjId::AllocatorQuota(PageSize::SZ1g, alloc_ptr) => krnl.allc_1g_mp.spec_index(alloc_ptr).quota.lock_id(),
        KernelObjId::AllocatorCache(PageSize::SZ4k, alloc_ptr, cpu_id) => krnl.allc_4k_mp.spec_index(alloc_ptr).cpu_caches.lock_id_by_index(cpu_id),
        KernelObjId::AllocatorCache(PageSize::SZ2m, alloc_ptr, cpu_id) => krnl.allc_2m_mp.spec_index(alloc_ptr).cpu_caches.lock_id_by_index(cpu_id),
        KernelObjId::AllocatorCache(PageSize::SZ1g, alloc_ptr, cpu_id) => krnl.allc_1g_mp.spec_index(alloc_ptr).cpu_caches.lock_id_by_index(cpu_id),
        KernelObjId::AllocatorGlobalPool(PageSize::SZ4k, alloc_ptr) => krnl.allc_4k_mp.spec_index(alloc_ptr).global_pool.lock_id(),
        KernelObjId::AllocatorGlobalPool(PageSize::SZ2m, alloc_ptr) => krnl.allc_2m_mp.spec_index(alloc_ptr).global_pool.lock_id(),
        KernelObjId::AllocatorGlobalPool(PageSize::SZ1g, alloc_ptr) => krnl.allc_1g_mp.spec_index(alloc_ptr).global_pool.lock_id(),
    }
}

/// A context aligned with `krnl` records, for every object it holds, the id `krnl` gives that object.
pub proof fn aligned_held_entry_implies_recorded_id_is_kernel_obj_lock_id(krnl: &KernelK, lctx: &LocalContext, obj: KernelObjId)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, lctx),
        lctx.typed_lock_entry(obj) is Some,
    ensures lctx.typed_lock_entry(obj)->Some_0.lock_id == kernel_obj_lock_id(krnl, obj),
{
    match obj {
        KernelObjId::Page(_) | KernelObjId::Cpu(_) => { reveal(LockedArray::typed_lock_map_aligned); },
        KernelObjId::PcidNeedFlush(_, _) => { reveal(LockedArray2D::typed_lock_map_aligned); },
        KernelObjId::CpuOfflineFlag(_, _) => { reveal(UnLockedMap::typed_flag_lock_map_aligned); },
        KernelObjId::Container(_) => { container_perms_wf_map(krnl.ctn_mp); reveal(LockedMap::typed_lock_map_aligned); },
        KernelObjId::Process(_) => { process_perms_wf_map(krnl.prc_mp); reveal(LockedMap::typed_lock_map_aligned); },
        KernelObjId::Thread(_) => { thread_perms_wf_map(krnl.thrd_mp); reveal(LockedMap::typed_lock_map_aligned); },
        KernelObjId::Endpoint(_) => { endpoint_perms_wf_map(krnl.ep_mp); reveal(LockedMap::typed_lock_map_aligned); },
        KernelObjId::SchedulerShard(_, _) => { reveal(UnLockedMap::typed_shard_lock_map_aligned); },
        KernelObjId::PcidAllocator(_) => { pcid_allocator_perms_wf_map(krnl.pcid_allc_mp); reveal(LockedMap::typed_lock_map_aligned); },
        KernelObjId::CpuSet(_) => { cpu_set_perms_wf_map(krnl.cpu_set_mp); reveal(LockedMap::typed_lock_map_aligned); },
        KernelObjId::PageTable(_) => { pagetable_perms_wf_map(krnl.pt_mp); reveal(LockedMap::typed_lock_map_aligned); },
        KernelObjId::PageTableWindow(_, _) => { reveal(pagetable_window_typed_lock_map_aligned); },
        KernelObjId::IommuTable(_) => { iommu_table_perms_wf_map(krnl.it_mp); reveal(LockedMap::typed_lock_map_aligned); },
        KernelObjId::IommuRootTable(_) => { reveal(iommu_root_table_typed_lock_map_aligned); },
        KernelObjId::AllocatorQuota(_, _) => { reveal(UnLockedMap::typed_quota_lock_map_aligned); },
        KernelObjId::AllocatorCache(_, _, _) => { reveal(UnLockedMap::typed_cache_lock_map_aligned); },
        KernelObjId::AllocatorGlobalPool(_, _) => { reveal(UnLockedMap::typed_global_pool_lock_map_aligned); },
    }
}

/// One waits-for edge: when a waiter wants `obj` at an id not above the id `krnl` gives it, and a holder of `obj` aligned
/// with `krnl` wants `holder_want` under `lock_id_acyclic`, the holder's wanted id is strictly above the waiter's.
pub proof fn aligned_holder_of_ordered_want_implies_holder_want_above(krnl: &KernelK, holder: &LocalContext, obj: KernelObjId, want: LockId, holder_want: LockId)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, holder),
        holder.typed_lock_entry(obj) is Some,
        want.spec_le(kernel_obj_lock_id(krnl, obj)),
        holder.lock_id_acyclic(holder_want),
    ensures holder_want.spec_gt(want),
{
    aligned_held_entry_implies_recorded_id_is_kernel_obj_lock_id(krnl, holder, obj);
    assert(holder_want.spec_gt(kernel_obj_lock_id(krnl, obj))) by { reveal(LocalContext::lock_id_acyclic); };
    if want != kernel_obj_lock_id(krnl, obj) { lock_id_gt_transitive(holder_want, kernel_obj_lock_id(krnl, obj), want); }
}

/// No lock minor is below itself.
pub proof fn lock_minor_lt_self_implies_false(m: LockMinorId)
    ensures !lock_minor_lt(m, m),
    decreases m.len(),
{ if m.len() > 1 { lock_minor_lt_self_implies_false(m.skip(1)); } }

/// Two cpus aligned with one kernel state, each holding the lock the other waits for at an ordered id, contradict.
pub proof fn two_aligned_acquirers_with_ordered_wants_implies_no_wait_cycle(krnl: &KernelK, a: &LocalContext, b: &LocalContext, x: KernelObjId, y: KernelObjId,
    want_x: LockId, want_y: LockId)
    requires
        krnl.inv(),
        typed_lock_maps_aligned(krnl, a),
        typed_lock_maps_aligned(krnl, b),
        a.kernel_view_locking_state() is Acquire,
        b.kernel_view_locking_state() is Acquire,
        b.typed_lock_entry(x) is Some,
        a.typed_lock_entry(y) is Some,
        want_x.spec_le(kernel_obj_lock_id(krnl, x)),
        want_y.spec_le(kernel_obj_lock_id(krnl, y)),
        a.lock_id_acyclic(want_x),
        b.lock_id_acyclic(want_y),
    ensures false,
{
    aligned_holder_of_ordered_want_implies_holder_want_above(krnl, b, x, want_x, want_y);
    aligned_holder_of_ordered_want_implies_holder_want_above(krnl, a, y, want_y, want_x);
    lock_id_gt_transitive(want_x, want_y, want_x);
    lock_minor_lt_self_implies_false(want_x.minor);
}

/// Along a chain of cpus aligned with `krnl`, where each cpu holds the lock the previous one wants at an ordered id, every
/// later cpu's wanted id is strictly above the first cpu's.
pub proof fn aligned_acquirer_chain_with_ordered_wants_implies_want_above_first(krnl: &KernelK, cpus: Seq<LocalContext>, objs: Seq<KernelObjId>,
    wants: Seq<LockId>, k: int)
    requires
        krnl.inv(),
        objs.len() == cpus.len(),
        wants.len() == cpus.len(),
        forall|i: int| #![trigger cpus[i]] 0 <= i < cpus.len() ==> typed_lock_maps_aligned(krnl, &cpus[i]),
        forall|i: int| #![trigger objs[i]] 0 <= i < cpus.len() ==> cpus[if i + 1 == cpus.len() { 0 } else { i + 1 }].typed_lock_entry(objs[i]) is Some,
        forall|i: int| #![trigger objs[i]] 0 <= i < cpus.len() ==> wants[i].spec_le(kernel_obj_lock_id(krnl, objs[i])),
        forall|i: int| #![trigger wants[i]] 0 <= i < cpus.len() ==> cpus[i].lock_id_acyclic(wants[i]),
        1 <= k < cpus.len(),
    ensures wants[k].spec_gt(wants[0]),
    decreases k,
{
    aligned_holder_of_ordered_want_implies_holder_want_above(krnl, &cpus[k], objs[k - 1], wants[k - 1], wants[k]);
    if k > 1 {
        aligned_acquirer_chain_with_ordered_wants_implies_want_above_first(krnl, cpus, objs, wants, k - 1);
        lock_id_gt_transitive(wants[k], wants[k - 1], wants[0]);
    }
}

/// A ring of cpus aligned with one kernel state, each holding the lock the previous one wants at an ordered id, contradicts.
pub proof fn aligned_acquirers_with_ordered_wants_implies_no_wait_cycle(krnl: &KernelK, cpus: Seq<LocalContext>, objs: Seq<KernelObjId>, wants: Seq<LockId>)
    requires
        krnl.inv(),
        cpus.len() >= 1,
        objs.len() == cpus.len(),
        wants.len() == cpus.len(),
        forall|i: int| #![trigger cpus[i]] 0 <= i < cpus.len() ==> typed_lock_maps_aligned(krnl, &cpus[i]),
        forall|i: int| #![trigger cpus[i]] 0 <= i < cpus.len() ==> cpus[i].kernel_view_locking_state() is Acquire,
        forall|i: int| #![trigger objs[i]] 0 <= i < cpus.len() ==> cpus[if i + 1 == cpus.len() { 0 } else { i + 1 }].typed_lock_entry(objs[i]) is Some,
        forall|i: int| #![trigger objs[i]] 0 <= i < cpus.len() ==> wants[i].spec_le(kernel_obj_lock_id(krnl, objs[i])),
        forall|i: int| #![trigger wants[i]] 0 <= i < cpus.len() ==> cpus[i].lock_id_acyclic(wants[i]),
    ensures false,
{
    let last = cpus.len() - 1;
    aligned_holder_of_ordered_want_implies_holder_want_above(krnl, &cpus[0], objs[last], wants[last], wants[0]);
    if last > 0 {
        aligned_acquirer_chain_with_ordered_wants_implies_want_above_first(krnl, cpus, objs, wants, last);
        lock_id_gt_transitive(wants[0], wants[last], wants[0]);
    }
    lock_minor_lt_self_implies_false(wants[0].minor);
}

/// `a >= b > c >= d` implies `a > d`.
pub proof fn lock_id_ge_gt_ge_implies_gt(a: LockId, b: LockId, c: LockId, d: LockId)
    requires a.spec_ge(b), b.spec_gt(c), c.spec_ge(d),
    ensures a.spec_gt(d),
{
    if a != b { lock_id_gt_transitive(a, b, c); }
    if c != d { lock_id_gt_transitive(a, c, d); }
}

/// Along a chain whose edges are holder edges or same-want edges (the next cpu waits for the same object at the same id,
/// as behind a per-cpu reader-lock writer that has not taken every slot), wanted ids never decrease.
pub proof fn aligned_acquirer_holder_or_same_want_chain_implies_want_at_or_above(krnl: &KernelK, cpus: Seq<LocalContext>, objs: Seq<KernelObjId>,
    wants: Seq<LockId>, j: int, k: int)
    requires
        krnl.inv(),
        objs.len() == cpus.len(),
        wants.len() == cpus.len(),
        forall|i: int| #![trigger cpus[i]] 0 <= i < cpus.len() ==> typed_lock_maps_aligned(krnl, &cpus[i]),
        forall|i: int| #![trigger objs[i]] 0 <= i < cpus.len() ==> {
            ||| cpus[if i + 1 == cpus.len() { 0 } else { i + 1 }].typed_lock_entry(objs[i]) is Some && wants[i].spec_le(kernel_obj_lock_id(krnl, objs[i]))
            ||| objs[if i + 1 == cpus.len() { 0 } else { i + 1 }] == objs[i] && wants[if i + 1 == cpus.len() { 0 } else { i + 1 }] == wants[i]
        },
        forall|i: int| #![trigger wants[i]] 0 <= i < cpus.len() ==> cpus[i].lock_id_acyclic(wants[i]),
        0 <= j <= k < cpus.len(),
    ensures wants[k].spec_ge(wants[j]),
    decreases k - j,
{
    if j < k {
        aligned_acquirer_holder_or_same_want_chain_implies_want_at_or_above(krnl, cpus, objs, wants, j, k - 1);
        if cpus[k].typed_lock_entry(objs[k - 1]) is Some && wants[k - 1].spec_le(kernel_obj_lock_id(krnl, objs[k - 1])) {
            aligned_holder_of_ordered_want_implies_holder_want_above(krnl, &cpus[k], objs[k - 1], wants[k - 1], wants[k]);
            if wants[k - 1] != wants[j] { lock_id_gt_transitive(wants[k], wants[k - 1], wants[j]); }
        }
    }
}

/// A ring of cpus aligned with one kernel state, where each cpu holds the lock the previous one wants at an ordered id or
/// waits for the same object at the same id, contradicts as soon as one edge, at `h`, is a holder edge.
pub proof fn aligned_acquirers_with_holder_or_same_want_edges_implies_no_wait_cycle(krnl: &KernelK, cpus: Seq<LocalContext>, objs: Seq<KernelObjId>,
    wants: Seq<LockId>, h: int)
    requires
        krnl.inv(),
        cpus.len() >= 1,
        objs.len() == cpus.len(),
        wants.len() == cpus.len(),
        forall|i: int| #![trigger cpus[i]] 0 <= i < cpus.len() ==> typed_lock_maps_aligned(krnl, &cpus[i]),
        forall|i: int| #![trigger cpus[i]] 0 <= i < cpus.len() ==> cpus[i].kernel_view_locking_state() is Acquire,
        forall|i: int| #![trigger objs[i]] 0 <= i < cpus.len() ==> {
            ||| cpus[if i + 1 == cpus.len() { 0 } else { i + 1 }].typed_lock_entry(objs[i]) is Some && wants[i].spec_le(kernel_obj_lock_id(krnl, objs[i]))
            ||| objs[if i + 1 == cpus.len() { 0 } else { i + 1 }] == objs[i] && wants[if i + 1 == cpus.len() { 0 } else { i + 1 }] == wants[i]
        },
        forall|i: int| #![trigger wants[i]] 0 <= i < cpus.len() ==> cpus[i].lock_id_acyclic(wants[i]),
        0 <= h < cpus.len(),
        cpus[if h + 1 == cpus.len() { 0 } else { h + 1 }].typed_lock_entry(objs[h]) is Some,
        wants[h].spec_le(kernel_obj_lock_id(krnl, objs[h])),
    ensures false,
{
    let last = cpus.len() - 1;
    let next = if h + 1 == cpus.len() { 0 } else { h + 1 };
    aligned_holder_of_ordered_want_implies_holder_want_above(krnl, &cpus[next], objs[h], wants[h], wants[next]);
    aligned_acquirer_holder_or_same_want_chain_implies_want_at_or_above(krnl, cpus, objs, wants, 0, h);
    if h < last {
        aligned_acquirer_holder_or_same_want_chain_implies_want_at_or_above(krnl, cpus, objs, wants, h + 1, last);
        if cpus[0].typed_lock_entry(objs[last]) is Some && wants[last].spec_le(kernel_obj_lock_id(krnl, objs[last])) {
            aligned_holder_of_ordered_want_implies_holder_want_above(krnl, &cpus[0], objs[last], wants[last], wants[0]);
        }
        lock_id_ge_gt_ge_implies_gt(wants[last], wants[h + 1], wants[h], wants[0]);
        lock_id_ge_gt_ge_implies_gt(wants[0], wants[last], wants[0], wants[0]);
    } else {
        lock_id_ge_gt_ge_implies_gt(wants[0], wants[0], wants[last], wants[0]);
    }
    lock_minor_lt_self_implies_false(wants[0].minor);
}
}
