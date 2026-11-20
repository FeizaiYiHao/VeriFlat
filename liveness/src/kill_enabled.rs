//! Round 8: a cpu inside `kill_process` whose wanted locks are free has an enabled kill step. Each stage names the step the
//! code takes and the state it leads to.
use vstd::prelude::*;
use crate::*;
use crate::frame::*;
use crate::family_kill::*;
use veriflat_syscall_kill_process::syscall_kill_process::syscall_kill_process_spec::*;

verus! {
/// The killer's thread moved to `process` at `stage`.
pub open spec fn kill_moved(u: KernelU, c: CpuId, process: RwLockProcessPtr, stage: KillStage) -> Map<RwLockThreadPtr, ThreadU> {
    u.thread_map.insert(kill_killer(u, c), kill_killer_at(u, c, process, stage))
}

/// Back on its own process, the killer finishes.
proof fn kill_own_implies_finish_enabled(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), in_kill(u, c), kill_holds(u, c), kill_target(u, c) == kill_own(u, c),
    ensures kill_enabled(u, c),
{
    reveal(kill_process_finish_step_pre); reveal(kill_process_finish_step); reveal(kernel_u_cpu_ownership_wf);
    let cpu = u.cpu_array[c as int];
    let pp = kill_own(u, c);
    let k = cpu.current_thread->Some_0;
    let u2 = KernelU {
        cpu_array: u.cpu_array.update(c as int, CpuU { lock_state: LockStateU::Unlocked, op: cpu_op_after_step(cpu.state), ..cpu }),
        process_map: u.process_map.insert(pp, ProcessU { lock_state: LockStateU::Unlocked, ..u.process_map[pp] }),
        thread_map: u.thread_map.insert(k, ThreadU { lock_state: LockStateU::Unlocked, syscall_progress: None, ..u.thread_map[k] }),
        ..u
    };
    assert(kill_stage(u, c) == KillStage::Walk);
    assert(labeled_step(StepLabel::KillProcessFinish, u, u2, c));
}

/// At a walk stage away from its own process the killer descends, marks or leaves dangling a thread, or reclaims.
proof fn kill_walk_implies_enabled(u: KernelU, c: CpuId)
    requires
        kernel_u_ownership_wf(u), kill_world_inv(u), in_kill(u, c), kill_holds(u, c), kill_wanted_free(u, c), kill_target(u, c) != kill_own(u, c),
        kill_stage(u, c) is Walk, kill_process_step_pre(u, c),
    ensures kill_enabled(u, c),
{
    reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_process_threads_wf); reveal(kernel_u_process_children_wf); reveal(kernel_u_process_ownership_wf);
    let tp = kill_target(u, c);
    let t = u.process_map[tp];
    let pp = kill_own(u, c);
    assert(kill_stage(u, c) == KillStage::Walk);
    proc_wf_at_of(u, tp);
    if t.children.len() > 0 {
        reveal(kill_process_mark_child_step);
        let ch = t.children[0];
        assert(t.children.contains(ch));
        assert(!u.process_map[ch].killed);
        let u2 = KernelU {
            process_map: u.process_map.insert(ch, ProcessU { lock_state: LockStateU::WriteLocked { writer: c }, killed: true, ..u.process_map[ch] }),
            thread_map: kill_moved(u, c, ch, KillStage::Walk),
            ..u
        };
        assert(labeled_step(StepLabel::KillProcessMarkChild, u, u2, c));
    } else if t.owned_threads.len() > 0 {
        let v = t.owned_threads[0];
        let vt = u.thread_map[v];
        assert(t.owned_threads.contains(v));
        assert(u.thread_map.dom().contains(v));
        assert(thread_wf_at(vt));
        if vt.state is WAITING_REPLY {
            reveal(kill_process_dangling_step);
            let u2 = KernelU {
                process_map: u.process_map.insert(tp, kill_process_absorb_thread(t, v, vt)),
                thread_map: u.thread_map.insert(v, ThreadU { state: ThreadState::DANGLING, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..vt }),
                ..u
            };
            assert(labeled_step(StepLabel::KillProcessDangling, u, u2, c));
        } else {
            reveal(kill_process_mark_thread_step);
            let u2 = KernelU {
                thread_map: u.thread_map.insert(v, ThreadU { lock_state: LockStateU::WriteLocked { writer: c }, killed: true, ..vt })
                    .insert(kill_killer(u, c), kill_killer_at(u, c, tp, KillStage::Thread { thread: v })),
                ..u
            };
            assert(labeled_step(StepLabel::KillProcessMarkThread, u, u2, c));
        }
    } else if t.zombie {
        reveal(kill_process_zombie_retire_step);
        let u2 = KernelU { thread_map: kill_moved(u, c, tp, KillStage::Retire), ..u };
        assert(labeled_step(StepLabel::KillProcessZombieRetire, u, u2, c));
    } else {
        reveal(kill_process_lock_table_step);
        let u2 = KernelU {
            process_map: u.process_map.insert(tp, ProcessU { pagetable: Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: c }, ..t.pagetable->Some_0 }), ..t }),
            thread_map: kill_moved(u, c, tp, KillStage::Reclaim { flushed: false }),
            ..u
        };
        assert(labeled_step(StepLabel::KillProcessLockTable, u, u2, c));
    }
}

/// After the flush the target releases its PCI functions and write-locks its IOMMU table.
proof fn kill_unown_enabled(u: KernelU, c: CpuId)
    requires
        kill_stage(u, c) == (KillStage::Reclaim { flushed: true }), kill_process_reclaim_step_pre(u, c, KillStage::Reclaim { flushed: true }),
        kill_table_cleared(u, c), kill_process_step_pre(u, c),
        u.process_map[kill_target(u, c)].iommu_table is Some ==> u.process_map[kill_target(u, c)].iommu_table->Some_0.lock_state is Unlocked,
    ensures kill_enabled(u, c),
{
    reveal(kill_process_unown_functions_step);
    let tp = kill_target(u, c);
    let t = u.process_map[tp];
    let pagetable = t.pagetable->Some_0;
    let table = u.iommu_root_table;
    let functions = pagetable.pci_functions.dom();
    let u2 = KernelU {
        process_map: u.process_map.insert(tp, ProcessU {
            pagetable: Some(PageTableU { pci_functions: Map::empty(), ..pagetable }),
            iommu_table: match t.iommu_table { Some(x) => Some(PageTableU { lock_state: LockStateU::WriteLocked { writer: c }, did: None, ..x }), None => None },
            ..t
        }),
        iommu_root_table: IommuRootTableU {
            owners: if functions == Set::<PciBdf>::empty() { table.owners } else { pci_owners_released(table.owners, functions) },
            attached: if t.iommu_table is Some {
                Seq::new(PCI_BUS_COUNT as nat, |bus: int| Seq::new(PCI_DEVICE_COUNT as nat, |device: int| Seq::new(PCI_FUNCTION_COUNT as nat,
                    |function: int| table.attached[bus][device][function] && !functions.contains((bus as usize, device as usize, function as usize)))))
            } else { table.attached },
        },
        iommu_tlb: if t.iommu_table is Some && t.iommu_table->Some_0.did is Some {
            u.iommu_tlb.insert(t.iommu_table->Some_0.did->Some_0, SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() })
        } else { u.iommu_tlb },
        ..u
    };
    assert(labeled_step(StepLabel::KillProcessUnownFunctions, u, u2, c));
}

/// At a thread stage the killer dequeues its victim, forces the cpu running it to idle, or unlinks it once killed.
proof fn kill_thread_implies_enabled(u: KernelU, c: CpuId)
    requires
        kernel_u_ownership_wf(u), kill_world_inv(u), in_kill(u, c), kill_holds(u, c), kill_wanted_free(u, c), kill_stage(u, c) is Thread,
        kill_process_step_pre(u, c),
    ensures kill_enabled(u, c),
{
    reveal(kernel_u_thread_ownership_wf); reveal(kernel_u_endpoint_wait_wf); reveal(kernel_u_running_thread_cpu_wf); reveal(kernel_u_cpu_ownership_wf);
    let tp = kill_target(u, c);
    let t = u.process_map[tp];
    let v = kill_stage(u, c)->Thread_thread;
    let vt = u.thread_map[v];
    assert(thread_wf_at(vt));
    if vt.state is SCHEDULED {
        reveal(kill_process_dequeue_scheduled_step);
        let shard = vt.state->SCHEDULED_cpu_id;
        let container = u.container_map[vt.owning_container];
        let u2 = KernelU {
            container_map: u.container_map.insert(vt.owning_container, ContainerU {
                scheduler: container.scheduler.update(shard as int, container.scheduler[shard as int].remove_value(v)), ..container
            }),
            thread_map: u.thread_map.insert(v, ThreadU { state: ThreadState::KILLED, error_code: None, ..vt }),
            ..u
        };
        assert(labeled_step(StepLabel::KillProcessDequeueScheduled, u, u2, c));
    } else if vt.state.is_endpoint_waiting() {
        reveal(kill_process_dequeue_endpoint_step);
        let ep = vt.blocking_endpoint_ptr->Some_0;
        let endpoint = u.endpoint_map[ep];
        let u2 = KernelU {
            endpoint_map: u.endpoint_map.insert(ep, EndpointU { queue: endpoint.queue.remove_value(v), ..endpoint }),
            thread_map: u.thread_map.insert(v, ThreadU { state: ThreadState::KILLED, blocking_endpoint_ptr: None, ..vt }),
            ..u
        };
        assert(labeled_step(StepLabel::KillProcessDequeueEndpoint, u, u2, c));
    } else if vt.state is RUNNING {
        reveal(kill_process_cpu_to_idle_step);
        let remote = vt.state->RUNNING_cpu_id;
        assert(u.cpu_array[remote as int].current_thread == Some(v));
        assert(u.cpu_array[remote as int] == u.cpu_array[remote as int]);
        let u2 = KernelU {
            cpu_array: u.cpu_array.update(remote as int, CpuU { state: CpuState::Idle, op: CpuOpState::Idle, current_process: None, current_thread: None, ..u.cpu_array[remote as int] }),
            thread_map: u.thread_map.insert(v, ThreadU { state: ThreadState::KILLED, ..vt }),
            ..u
        };
        assert(labeled_step(StepLabel::KillProcessCpuToIdle, u, u2, c));
    } else {
        reveal(kill_process_unlink_step);
        assert(vt.state is KILLED);
        let u2 = KernelU {
            process_map: u.process_map.insert(tp, kill_process_absorb_thread(t, v, vt)),
            thread_map: u.thread_map.insert(v, ThreadU { state: ThreadState::KILLED, quota_4k: 0, quota_2m: 0, quota_1g: 0, ..vt })
                .insert(kill_killer(u, c), kill_killer_at(u, c, tp, KillStage::Walk)),
            ..u
        };
        assert(labeled_step(StepLabel::KillProcessUnlink, u, u2, c));
    }
}

/// The quota step from stage `st`, whose next size is `size`.
pub open spec fn kill_quota_witness(u: KernelU, c: CpuId, size: PageSize) -> KernelU {
    let tp = kill_target(u, c);
    let t = u.process_map[tp];
    let container = u.container_map[t.owning_container];
    KernelU {
        container_map: u.container_map.insert(t.owning_container, match size {
            PageSize::SZ4k => ContainerU { quota_4k: (container.quota_4k + t.quota_4k) as usize, ..container },
            PageSize::SZ2m => ContainerU { quota_2m: (container.quota_2m + t.quota_2m) as usize, ..container },
            PageSize::SZ1g => ContainerU { quota_1g: (container.quota_1g + t.quota_1g) as usize, ..container },
        }),
        process_map: u.process_map.insert(tp, match size {
            PageSize::SZ4k => ProcessU { quota_4k: 0, ..t },
            PageSize::SZ2m => ProcessU { quota_2m: 0, ..t },
            PageSize::SZ1g => ProcessU { quota_1g: 0, ..t },
        }),
        thread_map: kill_moved(u, c, tp, KillStage::Quota { returned: size }),
        ..u
    }
}

/// While its tables are held the killer hides, flushes, removes an IOMMU leaf, returns quota, or unlocks.
proof fn kill_reclaim_implies_enabled(u: KernelU, c: CpuId)
    requires
        kernel_u_ownership_wf(u), kill_world_inv(u), in_kill(u, c), kill_holds(u, c), kill_wanted_free(u, c), kill_stage_reclaiming(kill_stage(u, c)),
        kill_process_step_pre(u, c),
    ensures kill_enabled(u, c),
{
    reveal(kernel_u_process_ownership_wf);
    let tp = kill_target(u, c);
    let t = u.process_map[tp];
    let st = kill_stage(u, c);
    assert(u.container_map.dom().contains(t.owning_container));
    if st == (KillStage::Reclaim { flushed: false }) {
        if kill_process_flush_step_pre(u, c) {
            reveal(kill_process_flushed_step);
            let u2 = KernelU { thread_map: kill_moved(u, c, tp, KillStage::Reclaim { flushed: true }), ..u };
            assert(labeled_step(StepLabel::KillProcessFlushed, u, u2, c));
        } else {
            reveal(kill_process_table_hidden_step); reveal(process_table_hidden_step);
            let o = t.pagetable->Some_0;
            assert(o.mapping_4k.restrict(o.mapping_4k.dom()) =~= o.mapping_4k);
            assert(o.mapping_2m.restrict(o.mapping_2m.dom()) =~= o.mapping_2m);
            assert(o.mapping_1g.restrict(o.mapping_1g.dom()) =~= o.mapping_1g);
            assert(o.pagetable_window_locks.restrict(o.pagetable_window_locks.dom()) =~= o.pagetable_window_locks);
            assert(u.process_map.insert(tp, t) =~= u.process_map);
            assert(labeled_step(StepLabel::KillProcessTableHidden, u, u, c));
        }
    } else if st == (KillStage::Reclaim { flushed: true }) && t.iommu_table is Some && t.iommu_table->Some_0.lock_state != (LockStateU::WriteLocked { writer: c }) {
        kill_unown_enabled(u, c);
    } else if st == (KillStage::Reclaim { flushed: true }) && t.iommu_table is Some && !process_iommu_4k_unmapped(t.iommu_table->Some_0) {
        reveal(kill_process_iommu_leaf_step);
        let it = t.iommu_table->Some_0;
        let m = it.mapping_4k;
        let iova = choose|iova: VAddr| m.dom().contains(iova);
        let kept = m.dom().remove(iova);
        let u2 = KernelU { process_map: u.process_map.insert(tp, ProcessU { iommu_table: Some(PageTableU { mapping_4k: m.restrict(kept), ..it }), ..t }), ..u };
        assert(m.restrict(kept).dom() =~= kept);
        assert(m.dom().difference(kept) =~= set![iova]);
        assert(labeled_step(StepLabel::KillProcessIommuLeaf, u, u2, c));
    } else if st == (KillStage::Quota { returned: PageSize::SZ1g }) {
        reveal(kill_process_unlock_table_step);
        let u2 = KernelU {
            process_map: u.process_map.insert(tp, ProcessU {
                pagetable: Some(PageTableU { lock_state: LockStateU::Unlocked, ..t.pagetable->Some_0 }),
                iommu_table: match t.iommu_table { Some(x) => Some(PageTableU { lock_state: LockStateU::Unlocked, ..x }), None => None },
                ..t
            }),
            thread_map: kill_moved(u, c, tp, KillStage::Zombie),
            ..u
        };
        assert(labeled_step(StepLabel::KillProcessUnlockTable, u, u2, c));
    } else {
        reveal(kill_process_quota_step);
        assert(kill_process_quota_stage_after(st) is Some);
        let size = kill_process_quota_stage_after(st)->Some_0->Quota_returned;
        assert(labeled_step(StepLabel::KillProcessQuota, u, kill_quota_witness(u, c, size), c));
    }
}

/// A reclaimed target becomes a zombie, and a zombie is retired.
proof fn kill_zombie_implies_enabled(u: KernelU, c: CpuId)
    requires
        kernel_u_ownership_wf(u), kill_world_inv(u), in_kill(u, c), kill_holds(u, c), kill_wanted_free(u, c), kill_target(u, c) != kill_own(u, c),
        kill_stage(u, c) is Zombie || kill_stage(u, c) is Retire, kill_process_step_pre(u, c),
    ensures kill_enabled(u, c),
{
    reveal(kernel_u_process_ownership_wf);
    let tp = kill_target(u, c);
    let t = u.process_map[tp];
    let ctn = t.owning_container;
    let container = u.container_map[ctn];
    assert(u.container_map.dom().contains(ctn));
    if kill_stage(u, c) is Zombie {
        reveal(kill_process_zombify_step);
        let u2 = KernelU {
            container_map: u.container_map.insert(ctn, ContainerU { free_pcids: container.free_pcids.insert(t.pcid), ..container }),
            process_map: u.process_map.insert(tp, ProcessU { zombie: true, pagetable: None, iommu_table: None, ..t }),
            thread_map: kill_moved(u, c, tp, KillStage::Retire),
            ..u
        };
        assert(labeled_step(StepLabel::KillProcessZombify, u, u2, c));
    } else {
        reveal(kill_process_retire_step);
        proc_wf_at_of(u, tp);
        let parent_ptr = t.parent->Some_0;
        let quota_4k = (container.quota_4k + 1) as usize;
        let u2 = KernelU {
            container_map: u.container_map.insert(ctn, ContainerU { owned_processes: container.owned_processes.remove(tp), quota_4k, ..container }),
            process_map: Map::new(u.process_map.dom().remove(tp), |p: RwLockProcessPtr| {
                let process = u.process_map[p];
                if t.uppertree_seq.contains(p) {
                    ProcessU { children: if p == parent_ptr { process.children.remove_value(tp) } else { process.children }, subtree_set: process.subtree_set.remove(tp), ..process }
                } else { process }
            }),
            thread_map: kill_moved(u, c, parent_ptr, KillStage::Walk),
            ..u
        };
        assert(t.uppertree_seq.contains(kill_own(u, c)));
        assert(labeled_step(StepLabel::KillProcessRetire, u, u2, c));
    }
}

/// Property (a) for `kill_process`, never blocked on free locks: under the world's kill invariants, a cpu inside a kill
/// whose wanted locks are free has an enabled kill step.
pub proof fn kill_world_inv_wanted_free_implies_kill_enabled(u: KernelU, c: CpuId)
    requires kernel_u_ownership_wf(u), kill_world_inv(u), in_kill(u, c), kill_wanted_free(u, c),
    ensures kill_enabled(u, c),
{
    kill_holds_at(u, c);
    if kill_target(u, c) == kill_own(u, c) { kill_own_implies_finish_enabled(u, c); }
    else {
        kill_holds_implies_step_pre(u, c);
        let st = kill_stage(u, c);
        if st is Walk { kill_walk_implies_enabled(u, c); }
        else if st is Thread { kill_thread_implies_enabled(u, c); }
        else if kill_stage_reclaiming(st) { kill_reclaim_implies_enabled(u, c); }
        else { kill_zombie_implies_enabled(u, c); }
    }
}
} // verus!
