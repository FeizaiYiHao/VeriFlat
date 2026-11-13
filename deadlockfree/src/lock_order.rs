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
}
