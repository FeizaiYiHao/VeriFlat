use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_maps_equal_internal, assert_seqs_equal};
use crate::*;

verus! {
/// Cpu `cpu` unlocked and moved to container `target`, every other cpu unchanged, projects to that cpu-array update.
pub proof fn kernel_cpu_owner_changed_implies_u_cpu_array(before: &KernelK, after: &KernelK, cpu: CpuId, target: RwLockContainerPtr)
    requires
        index_valid(NUM_CPUS, cpu),
        after.cpu_arr.entries_unchanged_except(&before.cpu_arr, cpu),
        after.cpu_arr.spec_index(cpu).value.view().view().owning_container == target,
        after.cpu_arr.spec_index(cpu).value.view().view().state == before.cpu_arr.spec_index(cpu).value.view().view().state,
        after.cpu_arr.spec_index(cpu).value.view().view().current_process == before.cpu_arr.spec_index(cpu).value.view().view().current_process,
        after.cpu_arr.spec_index(cpu).value.view().view().current_thread == before.cpu_arr.spec_index(cpu).value.view().view().current_thread,
        after.cpu_arr.spec_index(cpu).value.locking_thread() is None,
        after.cpu_arr.spec_index(cpu).value.being_killed() == before.cpu_arr.spec_index(cpu).value.being_killed(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).cpu_array == a.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::Unlocked, owning_container: target, ..a.cpu_array[cpu as int] })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let a = kernel_k_to_kernel_u(*before);
    let b = kernel_k_to_kernel_u(*after);
    assert_seqs_equal!(b.cpu_array == a.cpu_array.update(cpu as int, CpuU { lock_state: LockStateU::Unlocked, owning_container: target, ..a.cpu_array[cpu as int] }), i => {
        if 0 <= i < NUM_CPUS { kernel_cpu_projection_at(before, i as usize); kernel_cpu_projection_at(after, i as usize); }
    });
}

/// Page `page` moved from container `source` to container `target` with both cpu sets unlocked, every other container field,
/// scheduler shard, and cpu-set lock owner unchanged, projects to that container-map update.
pub proof fn kernel_page_owner_changed_implies_u_container_map(before: &KernelK, after: &KernelK, source: RwLockContainerPtr, target: RwLockContainerPtr, page: PagePtr)
    requires
        container_scheduler_wf(before.ctn_mp, before.sched_mp),
        container_cpu_set_wf(before.ctn_mp, before.cpu_set_mp),
        *after == (KernelK { pg_arr: after.pg_arr, ctn_mp: after.ctn_mp, cpu_arr: after.cpu_arr, cpu_set_mp: after.cpu_set_mp, sched_mp: after.sched_mp, ..*before }),
        forall|s: RwLockSchedulerPtr| #![trigger after.sched_mp.spec_index(s)] before.sched_mp.dom().contains(s) ==>
            scheduler_shards_of(after.sched_mp.spec_index(s)) == scheduler_shards_of(before.sched_mp.spec_index(s)),
        source != target,
        before.ctn_mp.dom().contains(source),
        before.ctn_mp.dom().contains(target),
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(source).view_rodata().view().cpu_set).locking_thread() is None,
        after.cpu_set_mp.spec_index(before.ctn_mp.spec_index(target).view_rodata().view().cpu_set).locking_thread() is None,
        forall|p: RwLockCpuSetPtr| #![trigger after.cpu_set_mp.spec_index(p)] before.cpu_set_mp.dom().contains(p) && p != before.ctn_mp.spec_index(source).view_rodata().view().cpu_set
            && p != before.ctn_mp.spec_index(target).view_rodata().view().cpu_set ==> after.cpu_set_mp.spec_index(p).locking_thread() == before.cpu_set_mp.spec_index(p).locking_thread(),
        after.ctn_mp.dom() == before.ctn_mp.dom(),
        forall|c: RwLockContainerPtr| #![trigger after.ctn_mp.spec_index(c)] before.ctn_mp.dom().contains(c) ==> {
            &&& after.ctn_mp.spec_index(c).view_rodata() == before.ctn_mp.spec_index(c).view_rodata()
            &&& after.ctn_mp.spec_index(c).view_ghost() == before.ctn_mp.spec_index(c).view_ghost()
            &&& after.ctn_mp.spec_index(c).locking_thread() == before.ctn_mp.spec_index(c).locking_thread()
            &&& after.ctn_mp.spec_index(c).being_killed() == before.ctn_mp.spec_index(c).being_killed()
            &&& after.ctn_mp.spec_index(c).view() == (Container { owned_pages: after.ctn_mp.spec_index(c).view().owned_pages, ..before.ctn_mp.spec_index(c).view() })
            &&& after.ctn_mp.spec_index(c).view().owned_pages.view() == if c == source { before.ctn_mp.spec_index(c).view().owned_pages.view().remove(page) }
                else if c == target { before.ctn_mp.spec_index(c).view().owned_pages.view().insert(page) } else { before.ctn_mp.spec_index(c).view().owned_pages.view() }
        },
    ensures
        ({
            let a = kernel_k_to_kernel_u(*before);
            kernel_k_to_kernel_u(*after).container_map == a.container_map.insert(source, ContainerU {
                cpu_set_lock: LockStateU::Unlocked, owned_pages: a.container_map[source].owned_pages.remove(page), ..a.container_map[source]
            }).insert(target, ContainerU { cpu_set_lock: LockStateU::Unlocked, owned_pages: a.container_map[target].owned_pages.insert(page), ..a.container_map[target] })
        }),
{
    kernel_u_domains_projection(before); kernel_u_domains_projection(after);
    let a = kernel_k_to_kernel_u(*before);
    let b = kernel_k_to_kernel_u(*after);
    container_cpu_set_wf_container_at(before.ctn_mp, before.cpu_set_mp, source); container_cpu_set_wf_container_at(before.ctn_mp, before.cpu_set_mp, target);
    assert_maps_equal!(b.container_map, a.container_map.insert(source, ContainerU { cpu_set_lock: LockStateU::Unlocked, owned_pages: a.container_map[source].owned_pages.remove(page), ..a.container_map[source] })
        .insert(target, ContainerU { cpu_set_lock: LockStateU::Unlocked, owned_pages: a.container_map[target].owned_pages.insert(page), ..a.container_map[target] }), c => {
        if before.ctn_mp.dom().contains(c) {
            kernel_container_projection_at(before, c); kernel_container_projection_at(after, c);
            container_scheduler_wf_at(before.ctn_mp, before.sched_mp, c); container_cpu_set_wf_container_at(before.ctn_mp, before.cpu_set_mp, c);
        }
    });
}

/// Replacing thread `thread`'s syscall progress, every other thread unchanged, projects to that thread-map update.
pub proof fn kernel_thread_progress_changed_implies_u_thread_map(pre: &KernelK, post: &KernelK, thread: RwLockThreadPtr)
    requires
        pre.thr_mp.dom().contains(thread),
        post.thr_mp.unchanged_except(&pre.thr_mp, thread),
        post.thr_mp.spec_index(thread).view() == (Thread { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress, ..pre.thr_mp.spec_index(thread).view() }),
        post.thr_mp.spec_index(thread).locking_thread() == pre.thr_mp.spec_index(thread).locking_thread(),
        post.thr_mp.spec_index(thread).being_killed() == pre.thr_mp.spec_index(thread).being_killed(),
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            kernel_k_to_kernel_u(*post).thread_map == a.thread_map.insert(thread, ThreadU { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    assert_maps_equal!(b.thread_map, a.thread_map.insert(thread, ThreadU { syscall_progress: post.thr_mp.spec_index(thread).view().syscall_progress.view(), ..a.thread_map[thread] }), t => {
        if pre.thr_mp.dom().contains(t) { kernel_thread_projection_at(pre, t); kernel_thread_projection_at(post, t); }
    });
}

/// Setting the lock owners of process `process`'s page table and IOMMU table to `lock`'s mode and changing only its K-only
/// state, every other process and table lock owner unchanged, projects to that process-map update.
pub proof fn kernel_process_tables_lock_state_changed_implies_u_process_map(pre: &KernelK, post: &KernelK, process: RwLockProcessPtr, pagetable: RwLockPageTableRoot, lock: bool)
    requires
        process_pagetable_match(post.prc_mp, post.pt_mp),
        process_iommu_table_match(post.prc_mp, post.it_mp),
        pre.prc_mp.dom().contains(process),
        !pre.prc_mp.spec_index(process).view().zombie,
        pre.prc_mp.spec_index(process).view().pagetable == pagetable,
        post.prc_mp.unchanged_except(&pre.prc_mp, process),
        post.prc_mp.spec_index(process).view() == (Process { state: post.prc_mp.spec_index(process).view().state, ..pre.prc_mp.spec_index(process).view() }),
        post.prc_mp.spec_index(process).view_rodata() == pre.prc_mp.spec_index(process).view_rodata(),
        post.prc_mp.spec_index(process).view_ghost() == pre.prc_mp.spec_index(process).view_ghost(),
        post.prc_mp.spec_index(process).locking_thread() == pre.prc_mp.spec_index(process).locking_thread(),
        post.prc_mp.spec_index(process).being_killed() == pre.prc_mp.spec_index(process).being_killed(),
        post.pt_mp.dom() == pre.pt_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(p)] pre.pt_mp.dom().contains(p) ==> {
            &&& post.pt_mp.spec_index(p).view() == pre.pt_mp.spec_index(p).view()
            &&& p != pagetable ==> post.pt_mp.spec_index(p).locking_thread() == pre.pt_mp.spec_index(p).locking_thread()
        },
        lock ==> post.pt_mp.spec_index(pagetable).locking_thread() is Write,
        !lock ==> post.pt_mp.spec_index(pagetable).locking_thread() is None,
        post.it_mp.dom() == pre.it_mp.dom(),
        forall|p: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(p)] pre.it_mp.dom().contains(p) ==> {
            &&& post.it_mp.spec_index(p).view() == pre.it_mp.spec_index(p).view()
            &&& Some(p) != pre.prc_mp.spec_index(process).view().iommu_table ==> post.it_mp.spec_index(p).locking_thread() == pre.it_mp.spec_index(p).locking_thread()
        },
        pre.prc_mp.spec_index(process).view().iommu_table is Some && lock ==> post.it_mp.spec_index(pre.prc_mp.spec_index(process).view().iommu_table->Some_0).locking_thread() is Write,
        pre.prc_mp.spec_index(process).view().iommu_table is Some && !lock ==> post.it_mp.spec_index(pre.prc_mp.spec_index(process).view().iommu_table->Some_0).locking_thread() is None,
    ensures
        ({
            let a = kernel_k_to_kernel_u(*pre);
            let process_u = a.process_map[process];
            let state = if lock { LockStateU::WriteLocked } else { LockStateU::Unlocked };
            kernel_k_to_kernel_u(*post).process_map == a.process_map.insert(process, ProcessU {
                pagetable: Some(PageTableU { lock_state: state, ..process_u.pagetable->Some_0 }),
                iommu_table: match process_u.iommu_table { Some(t) => Some(PageTableU { lock_state: state, ..t }), None => None },
                ..process_u
            })
        }),
{
    kernel_u_domains_projection(pre); kernel_u_domains_projection(post);
    let a = kernel_k_to_kernel_u(*pre);
    let b = kernel_k_to_kernel_u(*post);
    let process_u = a.process_map[process];
    let state = if lock { LockStateU::WriteLocked } else { LockStateU::Unlocked };
    let new_process_u = ProcessU {
        pagetable: Some(PageTableU { lock_state: state, ..process_u.pagetable->Some_0 }),
        iommu_table: match process_u.iommu_table { Some(t) => Some(PageTableU { lock_state: state, ..t }), None => None },
        ..process_u
    };
    kernel_process_projection_at(pre, process);
    assert_maps_equal!(b.process_map, a.process_map.insert(process, new_process_u), p => {
        if pre.prc_mp.dom().contains(p) { kernel_process_projection_at(pre, p); } if post.prc_mp.dom().contains(p) { kernel_process_projection_at(post, p); }
        process_pagetable_match_process_at(post.prc_mp, post.pt_mp, p); process_pagetable_match_process_at(post.prc_mp, post.pt_mp, process);
        process_iommu_table_match_process_at(post.prc_mp, post.it_mp, p); process_iommu_table_match_process_at(post.prc_mp, post.it_mp, process);
    });
}
} // verus!
