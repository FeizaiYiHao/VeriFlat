use vstd::prelude::*;
use crate::*;

verus! {
/// EOF closure of `block_current`: loading the default table with `KERNEL_DEFAULT_PCID` and clearing its flush flag keeps `pcid_needflush_wf` and
/// `cpu_hw_cr3_pcid_wf`.
pub(super) proof fn block_current_eof(pre_cpus: CpuLockedArray, post_cpus: CpuLockedArray, pre_needflush: PcidNeedFlushArray, post_needflush: PcidNeedFlushArray, pre_hw: CpuHwCr3PcidArray, post_hw: CpuHwCr3PcidArray, cpu_id: CpuId, default_cr3: PageTableRoot)
    requires
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(default_cr3),
        pre_hw[cpu_id as int].owner_cpu() == cpu_id,
        post_hw[cpu_id as int].inv(),
        post_hw[cpu_id as int].view() == (default_cr3, KERNEL_DEFAULT_PCID),
        post_hw[cpu_id as int].owner_cpu() == pre_hw[cpu_id as int].owner_cpu(),
        forall|c: CpuId| #![trigger post_hw[c as int]] #![trigger pre_hw[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> post_hw[c as int] == pre_hw[c as int],
        post_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view() == (PcidNeedFlush { needflush: false, ..pre_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view() }),
        post_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().index() == pre_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view().index(),
        post_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).is_init(),
        post_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread() == pre_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).locking_thread(),
        post_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view_ghost() == pre_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID).view_ghost(),
        forall|c: CpuId, p: Pcid| #![trigger post_needflush.spec_index(c, p)] #![trigger pre_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != KERNEL_DEFAULT_PCID) ==> post_needflush.spec_index(c, p) == pre_needflush.spec_index(c, p),
        post_cpus.entries_unchanged_except(&pre_cpus, cpu_id),
        post_cpus.spec_index(cpu_id).view().view().view().current_cr3 == default_cr3,
        post_cpus.spec_index(cpu_id).view().view().view().current_pcid == KERNEL_DEFAULT_PCID,
    ensures
        pcid_needflush_wf(pre_needflush) ==> pcid_needflush_wf(post_needflush),
        cpu_hw_cr3_pcid_wf(pre_hw, pre_cpus, pre_needflush) ==> cpu_hw_cr3_pcid_wf(post_hw, post_cpus, post_needflush),
{ reveal(pcid_needflush_wf); reveal(cpu_hw_cr3_pcid_wf); }

/// EOF closure of `switch_to_thread`: loading `(cr3, pcid)` and clearing its flush flag keeps `pcid_needflush_wf` and `cpu_hw_cr3_pcid_wf`.
pub(super) proof fn switch_to_thread_eof(pre_cpus: CpuLockedArray, post_cpus: CpuLockedArray, pre_needflush: PcidNeedFlushArray, post_needflush: PcidNeedFlushArray, pre_hw: CpuHwCr3PcidArray, post_hw: CpuHwCr3PcidArray, cpu_id: CpuId, cr3: PageTableRoot, pcid: Pcid)
    requires
        index_valid(NUM_CPUS, cpu_id),
        page_ptr_valid(cr3),
        pcid_valid(pcid),
        pre_hw[cpu_id as int].owner_cpu() == cpu_id,
        post_hw[cpu_id as int].inv(),
        post_hw[cpu_id as int].view() == (cr3, pcid),
        post_hw[cpu_id as int].owner_cpu() == pre_hw[cpu_id as int].owner_cpu(),
        forall|c: CpuId| #![trigger post_hw[c as int]] #![trigger pre_hw[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> post_hw[c as int] == pre_hw[c as int],
        post_needflush.spec_index(cpu_id, pcid).view() == (PcidNeedFlush { needflush: false, ..pre_needflush.spec_index(cpu_id, pcid).view() }),
        post_needflush.spec_index(cpu_id, pcid).view().index() == pre_needflush.spec_index(cpu_id, pcid).view().index(),
        post_needflush.spec_index(cpu_id, pcid).is_init(),
        post_needflush.spec_index(cpu_id, pcid).locking_thread() == pre_needflush.spec_index(cpu_id, pcid).locking_thread(),
        post_needflush.spec_index(cpu_id, pcid).view_ghost() == pre_needflush.spec_index(cpu_id, pcid).view_ghost(),
        forall|c: CpuId, p: Pcid| #![trigger post_needflush.spec_index(c, p)] #![trigger pre_needflush.spec_index(c, p)] index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != pcid) ==> post_needflush.spec_index(c, p) == pre_needflush.spec_index(c, p),
        post_cpus.entries_unchanged_except(&pre_cpus, cpu_id),
        post_cpus.spec_index(cpu_id).view().view().view().current_cr3 == cr3,
        post_cpus.spec_index(cpu_id).view().view().view().current_pcid == pcid,
    ensures
        pcid_needflush_wf(pre_needflush) ==> pcid_needflush_wf(post_needflush),
        cpu_hw_cr3_pcid_wf(pre_hw, pre_cpus, pre_needflush) ==> cpu_hw_cr3_pcid_wf(post_hw, post_cpus, post_needflush),
{ reveal(pcid_needflush_wf); reveal(cpu_hw_cr3_pcid_wf); }
} // verus!
