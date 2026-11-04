use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
/// Shared with `create_process_with_iommu_from_staged_pages` (`with_iommu`); without it the IOMMU page arguments are
/// unused and passed as 0.
#[verifier::opaque]
pub open spec fn create_process_from_staged_pages_eof_transition_framing(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, with_iommu: bool,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
) -> bool {
    let process_pg_idx = page_ptr2page_index(process_pg_ptr);
    let pagetable_pg_idx = page_ptr2page_index(pagetable_pg_ptr);
    let l4_pg_idx = page_ptr2page_index(l4_pg_ptr);
    let ancestors = pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr);
    &&& post.irt == pre.irt
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.pcid_needflush == pre.pcid_needflush
    &&& post.cpu_hw_cr3_pcid == pre.cpu_hw_cr3_pcid
    &&& post.cpu_op == pre.cpu_op
    &&& post.sched_mp == pre.sched_mp
    &&& post.cpu_set_mp == pre.cpu_set_mp
    &&& post.ep_mp == pre.ep_mp
    &&& post.allc_4k_mp == pre.allc_4k_mp
    &&& post.allc_2m_mp == pre.allc_2m_mp
    &&& post.allc_1g_mp == pre.allc_1g_mp
    &&& post.cpu_offline_mp == pre.cpu_offline_mp
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
    &&& !with_iommu ==> forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index)]
        #![trigger pre.pg_arr.spec_index(index)]
        index_valid(NUM_PAGES, index) && index != process_pg_idx && index != pagetable_pg_idx && index != l4_pg_idx ==> post.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index)
    &&& with_iommu ==> forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index)]
        #![trigger pre.pg_arr.spec_index(index)]
        index_valid(NUM_PAGES, index) && index != process_pg_idx && index != pagetable_pg_idx && index != l4_pg_idx
            && index != page_ptr2page_index(iommu_table_pg_ptr) && index != page_ptr2page_index(iommu_l4_pg_ptr) ==> post.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index)
    &&& post.pg_arr.spec_index(l4_pg_idx).view().view() == (Page {
        state: PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_pg_ptr, table_type: PT_TYPE } },
        perm_4k: post.pg_arr.spec_index(l4_pg_idx).view().view().perm_4k, ..pre.pg_arr.spec_index(l4_pg_idx).view().view()
    })
    &&& post.pg_arr.spec_index(l4_pg_idx).view().view().perm_4k.view().is_none()
    &&& post.pg_arr.spec_index(l4_pg_idx).view().view_rodata() == pre.pg_arr.spec_index(l4_pg_idx).view().view_rodata()
    &&& post.pg_arr.spec_index(l4_pg_idx).view().view_ghost() == pre.pg_arr.spec_index(l4_pg_idx).view().view_ghost()
    &&& post.pg_arr.spec_index(l4_pg_idx).view().locking_thread() == pre.pg_arr.spec_index(l4_pg_idx).view().locking_thread()
    &&& post.pg_arr.spec_index(pagetable_pg_idx).view().view() == (Page {
        state: PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: PT_TYPE } },
        perm_4k: post.pg_arr.spec_index(pagetable_pg_idx).view().view().perm_4k, ..pre.pg_arr.spec_index(pagetable_pg_idx).view().view()
    })
    &&& post.pg_arr.spec_index(pagetable_pg_idx).view().view().perm_4k.view().is_none()
    &&& post.pg_arr.spec_index(pagetable_pg_idx).view().view_rodata() == pre.pg_arr.spec_index(pagetable_pg_idx).view().view_rodata()
    &&& post.pg_arr.spec_index(pagetable_pg_idx).view().view_ghost() == pre.pg_arr.spec_index(pagetable_pg_idx).view().view_ghost()
    &&& post.pg_arr.spec_index(pagetable_pg_idx).view().locking_thread() == pre.pg_arr.spec_index(pagetable_pg_idx).view().locking_thread()
    &&& post.pg_arr.spec_index(process_pg_idx).view().view() == (Page {
        state: PageState::Allocated4k { state: Allocated4KPageState::AsProcess },
        perm_4k: post.pg_arr.spec_index(process_pg_idx).view().view().perm_4k, ..pre.pg_arr.spec_index(process_pg_idx).view().view()
    })
    &&& post.pg_arr.spec_index(process_pg_idx).view().view().perm_4k.view().is_none()
    &&& post.pg_arr.spec_index(process_pg_idx).view().view_rodata() == pre.pg_arr.spec_index(process_pg_idx).view().view_rodata()
    &&& post.pg_arr.spec_index(process_pg_idx).view().view_ghost() == pre.pg_arr.spec_index(process_pg_idx).view().view_ghost()
    &&& post.pg_arr.spec_index(process_pg_idx).view().locking_thread() == pre.pg_arr.spec_index(process_pg_idx).view().locking_thread()
    &&& post.pt_mp.dom() == pre.pt_mp.dom().insert(pagetable_pg_ptr)
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger post.pt_mp.dom().contains(pt_ptr)]
        #![trigger post.pt_mp.spec_index(pt_ptr)]
        #![trigger pre.pt_mp.spec_index(pt_ptr)]
        post.pt_mp.dom().contains(pt_ptr) && pt_ptr != pagetable_pg_ptr ==> {
            &&& pre.pt_mp.dom().contains(pt_ptr)
            &&& post.pt_mp.spec_index(pt_ptr) == pre.pt_mp.spec_index(pt_ptr)
        }
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger post.pt_mp.view().spec_index(pt_ptr).is_init()]
        post.pt_mp.dom().contains(pt_ptr) && pt_ptr != pagetable_pg_ptr ==> {
            &&& post.pt_mp.view().spec_index(pt_ptr).is_init()
            &&& post.pt_mp.view().spec_index(pt_ptr).addr() == pt_ptr
        }
    &&& post.pt_mp.view().spec_index(pagetable_pg_ptr).is_init()
    &&& post.pt_mp.view().spec_index(pagetable_pg_ptr).addr() == pagetable_pg_ptr
    &&& post.pt_mp.spec_index(pagetable_pg_ptr).is_init()
    &&& !post.pt_mp.spec_index(pagetable_pg_ptr).being_killed()
    &&& post.pt_mp.spec_index(pagetable_pg_ptr).view().proc_ptr == process_pg_ptr
    &&& post.pt_mp.spec_index(pagetable_pg_ptr).view().pcid_value() == pcid
    &&& post.pt_mp.spec_index(pagetable_pg_ptr).view().cr3 == l4_pg_ptr
    &&& post.pt_mp.spec_index(pagetable_pg_ptr).view().kernel_l4_end == pre.dflt_pt.view().kernel_l4_end
    &&& post.pt_mp.spec_index(pagetable_pg_ptr).view().table_stale_cpus.view() == Set::<CpuId>::empty()
    &&& post.pt_lower.view() == pre.pt_lower.view().insert(pagetable_pg_ptr, post.pt_lower.view().spec_index(pagetable_pg_ptr))
    &&& post.pt_mp.spec_index(pagetable_pg_ptr).view_ghost() == post.pt_lower.view().spec_index(pagetable_pg_ptr)
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger whole_pagetable(post.pt_mp, post.pt_lower.view(), pt_ptr)]
        pre.pt_mp.dom().contains(pt_ptr) ==> whole_pagetable(post.pt_mp, post.pt_lower.view(), pt_ptr) == whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pt_ptr)
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_pg_ptr).wf()
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_pg_ptr).is_empty()
    &&& whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_pg_ptr).page_closure() =~= set![l4_pg_ptr]
    &&& post.prc_mp.dom() == pre.prc_mp.dom().insert(process_pg_ptr)
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.dom().contains(p_ptr)]
        #![trigger post.prc_mp.spec_index(p_ptr)]
        post.prc_mp.dom().contains(p_ptr) && p_ptr != process_pg_ptr ==> {
            &&& pre.prc_mp.dom().contains(p_ptr)
            &&& post.prc_mp.spec_index(p_ptr).is_init() == pre.prc_mp.spec_index(p_ptr).is_init()
            &&& post.prc_mp.spec_index(p_ptr).locking_thread() == pre.prc_mp.spec_index(p_ptr).locking_thread()
            &&& post.prc_mp.spec_index(p_ptr).being_killed() == pre.prc_mp.spec_index(p_ptr).being_killed()
            &&& post.prc_mp.spec_index(p_ptr).killer_info() == pre.prc_mp.spec_index(p_ptr).killer_info()
            &&& post.prc_mp.spec_index(p_ptr).view_rodata() == pre.prc_mp.spec_index(p_ptr).view_rodata()
            &&& post.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq == pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq
            &&& post.prc_mp.spec_index(p_ptr).view_ghost().owned_pci_functions == pre.prc_mp.spec_index(p_ptr).view_ghost().owned_pci_functions
            &&& post.prc_mp.spec_index(p_ptr).view() == if p_ptr == parent_ptr {
                Process { children: post.prc_mp.spec_index(p_ptr).view().children, ..pre.prc_mp.spec_index(p_ptr).view() }
            } else {
                pre.prc_mp.spec_index(p_ptr).view()
            }
        }
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.spec_index(process_pg_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)]
        #![trigger post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set]
        post.prc_mp.spec_index(process_pg_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
            ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view().insert(process_pg_ptr)
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set]
        pre.prc_mp.dom().contains(p_ptr) && !post.prc_mp.spec_index(process_pg_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
            ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.view().spec_index(p_ptr).is_init()]
        post.prc_mp.dom().contains(p_ptr) && p_ptr != process_pg_ptr ==> {
            &&& post.prc_mp.view().spec_index(p_ptr).is_init()
            &&& post.prc_mp.view().spec_index(p_ptr).addr() == p_ptr
        }
    &&& post.prc_mp.view().spec_index(process_pg_ptr).is_init()
    &&& post.prc_mp.view().spec_index(process_pg_ptr).addr() == process_pg_ptr
    &&& post.prc_mp.spec_index(parent_ptr).view().children.view() == pre.prc_mp.spec_index(parent_ptr).view().children.view().push(process_pg_ptr)
    &&& !pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(post.prc_mp.spec_index(process_pg_ptr).view().parent_linkedlist_node.addr())
    &&& post.prc_mp.spec_index(parent_ptr).view().children.map() == pre.prc_mp.spec_index(parent_ptr).view().children.map().insert(post.prc_mp.spec_index(process_pg_ptr).view().parent_linkedlist_node.addr(), process_pg_ptr)
    &&& post.prc_mp.spec_index(process_pg_ptr).is_init()
    &&& !post.prc_mp.spec_index(process_pg_ptr).being_killed()
    &&& post.prc_mp.spec_index(process_pg_ptr).wlocked()
    &&& !post.prc_mp.spec_index(process_pg_ptr).view().zombie
    &&& post.prc_mp.spec_index(process_pg_ptr).view().state.view() is Creating
    &&& post.prc_mp.spec_index(process_pg_ptr).view().pcid == pcid
    &&& post.prc_mp.spec_index(process_pg_ptr).view().pagetable == pagetable_pg_ptr
    &&& post.prc_mp.spec_index(process_pg_ptr).view_ghost().owned_pci_functions.view().is_empty()
    &&& post.prc_mp.spec_index(process_pg_ptr).view().quota_4k == 0
    &&& post.prc_mp.spec_index(process_pg_ptr).view().quota_2m == 0
    &&& post.prc_mp.spec_index(process_pg_ptr).view().quota_1g == 0
    &&& !post.prc_mp.spec_index(process_pg_ptr).view().parent_linkedlist_node.is_init()
    &&& post.prc_mp.spec_index(process_pg_ptr).view().children.view() == Seq::<RwLockProcessPtr>::empty()
    &&& post.prc_mp.spec_index(process_pg_ptr).view().owned_threads.view() == Seq::<RwLockThreadPtr>::empty()
    &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().owning_container == ctn_ptr
    &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().container_depth == pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().depth
    &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().parent == Some(parent_ptr)
    &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().depth == pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth + 1
    &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().pagetable == pagetable_pg_ptr
    &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().cr3 == l4_pg_ptr
    &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().pcid == pcid
    &&& post.prc_mp.spec_index(process_pg_ptr).view_ghost().uppertree_seq.view() == ancestors
    &&& post.prc_mp.spec_index(process_pg_ptr).view_ghost().subtree_set.view() == Set::<RwLockProcessPtr>::empty()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, ctn_ptr)
    &&& post.ctn_mp.spec_index(ctn_ptr).view() == pre.ctn_mp.spec_index(ctn_ptr).view()
    &&& post.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view() == pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view().insert(process_pg_ptr)
    &&& post.ctn_mp.spec_index(ctn_ptr).view_rodata() == pre.ctn_mp.spec_index(ctn_ptr).view_rodata()
    &&& post.ctn_mp.spec_index(ctn_ptr).view_ghost() == (ContainerGhost { owned_processes: post.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes, ..pre.ctn_mp.spec_index(ctn_ptr).view_ghost() })
    &&& post.ctn_mp.spec_index(ctn_ptr).locking_thread() == pre.ctn_mp.spec_index(ctn_ptr).locking_thread()
    &&& post.ctn_mp.spec_index(ctn_ptr).control() == pre.ctn_mp.spec_index(ctn_ptr).control()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> post.ctn_mp.spec_index(c).view_ghost().owned_threads == pre.ctn_mp.spec_index(c).view_ghost().owned_threads
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger post.ctn_mp.view().spec_index(c_ptr).is_init()]
        pre.ctn_mp.dom().contains(c_ptr) ==> {
            &&& post.ctn_mp.view().spec_index(c_ptr).is_init() == pre.ctn_mp.view().spec_index(c_ptr).is_init()
            &&& post.ctn_mp.view().spec_index(c_ptr).addr() == pre.ctn_mp.view().spec_index(c_ptr).addr()
        }
    &&& post.thrd_mp.unchanged_except(&pre.thrd_mp, staging_thrd_ptr)
    &&& post.thrd_mp.spec_index(staging_thrd_ptr).view() == (Thread {
        quota_4k: post.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k,
        temp_alloc_cache_4k: post.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k, ..pre.thrd_mp.spec_index(staging_thrd_ptr).view()
    })
    &&& post.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view().is_empty()
    &&& post.thrd_mp.spec_index(staging_thrd_ptr).locking_thread() == pre.thrd_mp.spec_index(staging_thrd_ptr).locking_thread()
    &&& post.thrd_mp.spec_index(staging_thrd_ptr).being_killed() == pre.thrd_mp.spec_index(staging_thrd_ptr).being_killed()
    &&& post.thrd_mp.spec_index(staging_thrd_ptr).killer_info() == pre.thrd_mp.spec_index(staging_thrd_ptr).killer_info()
    &&& post.thrd_mp.spec_index(staging_thrd_ptr).view_ghost() == pre.thrd_mp.spec_index(staging_thrd_ptr).view_ghost()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger post.thrd_mp.view().spec_index(t_ptr).is_init()]
        pre.thrd_mp.dom().contains(t_ptr) ==> {
            &&& post.thrd_mp.view().spec_index(t_ptr).is_init() == pre.thrd_mp.view().spec_index(t_ptr).is_init()
            &&& post.thrd_mp.view().spec_index(t_ptr).addr() == pre.thrd_mp.view().spec_index(t_ptr).addr()
        }
    &&& post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, pcid_allc_ptr)
    &&& post.pcid_allc_mp.spec_index(pcid_allc_ptr).view().alloc_ensures(&pre.pcid_allc_mp.spec_index(pcid_allc_ptr).view(), process_pg_ptr, pcid)
    &&& post.pcid_allc_mp.spec_index(pcid_allc_ptr).locking_thread() == pre.pcid_allc_mp.spec_index(pcid_allc_ptr).locking_thread()
    &&& post.pcid_allc_mp.spec_index(pcid_allc_ptr).being_killed() == pre.pcid_allc_mp.spec_index(pcid_allc_ptr).being_killed()
    &&& forall|a_ptr: RwLockPcidAllocatorPtr|
        #![trigger post.pcid_allc_mp.view().spec_index(a_ptr).is_init()]
        pre.pcid_allc_mp.dom().contains(a_ptr) ==> {
            &&& post.pcid_allc_mp.view().spec_index(a_ptr).is_init() == pre.pcid_allc_mp.view().spec_index(a_ptr).is_init()
            &&& post.pcid_allc_mp.view().spec_index(a_ptr).addr() == pre.pcid_allc_mp.view().spec_index(a_ptr).addr()
        }
    &&& with_iommu ==> {
        let iommu_table_pg_idx = page_ptr2page_index(iommu_table_pg_ptr);
        let iommu_l4_pg_idx = page_ptr2page_index(iommu_l4_pg_ptr);
        &&& post.pg_arr.spec_index(iommu_l4_pg_idx).view().view() == (Page {
            state: PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: iommu_table_pg_ptr, table_type: IOMMU_TYPE } },
            perm_4k: post.pg_arr.spec_index(iommu_l4_pg_idx).view().view().perm_4k, ..pre.pg_arr.spec_index(iommu_l4_pg_idx).view().view()
        })
        &&& post.pg_arr.spec_index(iommu_l4_pg_idx).view().view().perm_4k.view().is_none()
        &&& post.pg_arr.spec_index(iommu_l4_pg_idx).view().view_rodata() == pre.pg_arr.spec_index(iommu_l4_pg_idx).view().view_rodata()
        &&& post.pg_arr.spec_index(iommu_l4_pg_idx).view().view_ghost() == pre.pg_arr.spec_index(iommu_l4_pg_idx).view().view_ghost()
        &&& post.pg_arr.spec_index(iommu_l4_pg_idx).view().locking_thread() == pre.pg_arr.spec_index(iommu_l4_pg_idx).view().locking_thread()
        &&& post.pg_arr.spec_index(iommu_table_pg_idx).view().view() == (Page {
            state: PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot { table_type: IOMMU_TYPE } },
            perm_4k: post.pg_arr.spec_index(iommu_table_pg_idx).view().view().perm_4k, ..pre.pg_arr.spec_index(iommu_table_pg_idx).view().view()
        })
        &&& post.pg_arr.spec_index(iommu_table_pg_idx).view().view().perm_4k.view().is_none()
        &&& post.pg_arr.spec_index(iommu_table_pg_idx).view().view_rodata() == pre.pg_arr.spec_index(iommu_table_pg_idx).view().view_rodata()
        &&& post.pg_arr.spec_index(iommu_table_pg_idx).view().view_ghost() == pre.pg_arr.spec_index(iommu_table_pg_idx).view().view_ghost()
        &&& post.pg_arr.spec_index(iommu_table_pg_idx).view().locking_thread() == pre.pg_arr.spec_index(iommu_table_pg_idx).view().locking_thread()
        &&& post.it_mp.dom() == pre.it_mp.dom().insert(iommu_table_pg_ptr)
        &&& forall|it_ptr: RwLockPageTableRoot|
            #![trigger post.it_mp.dom().contains(it_ptr)]
            #![trigger post.it_mp.spec_index(it_ptr)]
            #![trigger pre.it_mp.spec_index(it_ptr)]
            post.it_mp.dom().contains(it_ptr) && it_ptr != iommu_table_pg_ptr ==> {
                &&& pre.it_mp.dom().contains(it_ptr)
                &&& post.it_mp.spec_index(it_ptr) == pre.it_mp.spec_index(it_ptr)
            }
        &&& forall|it_ptr: RwLockPageTableRoot|
            #![trigger post.it_mp.view().spec_index(it_ptr).is_init()]
            post.it_mp.dom().contains(it_ptr) && it_ptr != iommu_table_pg_ptr ==> {
                &&& post.it_mp.view().spec_index(it_ptr).is_init()
                &&& post.it_mp.view().spec_index(it_ptr).addr() == it_ptr
            }
        &&& post.it_mp.view().spec_index(iommu_table_pg_ptr).is_init()
        &&& post.it_mp.view().spec_index(iommu_table_pg_ptr).addr() == iommu_table_pg_ptr
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).is_init()
        &&& !post.it_mp.spec_index(iommu_table_pg_ptr).being_killed()
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).view().proc_ptr == process_pg_ptr
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).view().pcid is None
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).view().did is None
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).view().cr3 == iommu_l4_pg_ptr
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).view().kernel_l4_end == 0
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).view().is_empty()
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).view().page_closure() == set![iommu_l4_pg_ptr]
        &&& post.it_mp.spec_index(iommu_table_pg_ptr).locking_thread() is Write
        &&& post.prc_mp.spec_index(process_pg_ptr).view().iommu_table == Some(iommu_table_pg_ptr)
        &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().iommu_cr3 == Some(iommu_l4_pg_ptr)
        &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().iommu_table_ptr == Some(iommu_table_pg_ptr)
        &&& post.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k == pre.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k - 5
    }
    &&& !with_iommu ==> {
        &&& post.it_mp == pre.it_mp
        &&& post.prc_mp.spec_index(process_pg_ptr).view().iommu_table is None
        &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().iommu_cr3 is None
        &&& post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().iommu_table_ptr is None
        &&& post.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k == pre.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k - 3
    }
}

proof fn create_process_from_staged_pages_eof_subsystems_inv(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        !pre.prc_mp.dom().contains(process_pg_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == ctn_ptr,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.pcid_allc_mp.dom().contains(pcid_allc_ptr),
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().inv(),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable_pg_ptr).inv(),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_pg_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.spec_index(ctn_ptr).inv(),
        post.thrd_mp.spec_index(staging_thrd_ptr).inv(),
        thread_perms_wf(post.thrd_mp),
        post.pcid_allc_mp.perms_wf(),
        post.pcid_allc_mp.spec_index(pcid_allc_ptr).inv(),
    ensures
        post.subsystems_inv(),
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    let process_pg_idx = page_ptr2page_index(process_pg_ptr);
    let pagetable_pg_idx = page_ptr2page_index(pagetable_pg_ptr);
    let l4_pg_idx = page_ptr2page_index(l4_pg_ptr);
    assert(process_pg_idx != pagetable_pg_idx && process_pg_idx != l4_pg_idx && pagetable_pg_idx != l4_pg_idx) by {
        page_ptr2page_index_neq(process_pg_ptr, pagetable_pg_ptr); page_ptr2page_index_neq(process_pg_ptr, l4_pg_ptr);
    };
    assert(pagetable_perms_wf(post.pt_mp)) by { reveal(pagetable_perms_wf); };
    assert(pagetable_lower_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_lower_wf); };
    assert(pagetable_window_holders_hold_pagetable(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_holders_hold_pagetable); reveal(WholePageTable::wf_window_locks); };
    assert(pagetable_hidden_leaves_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_leaves_only_when_locked); };
    assert(pagetable_hidden_l1_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_hidden_l1_only_when_locked); };
    assert(pagetable_window_stale_cpus_only_when_locked(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_window_stale_cpus_only_when_locked); };
    assert(pagetable_table_stale_cpus_only_when_write_locked(post.pt_mp)) by { reveal(pagetable_table_stale_cpus_only_when_write_locked); };
    assert(pagetable_lower_backup_wf(post.pt_mp, post.pt_lower.view()));
    assert(page_array_wf(post.pg_arr)) by { reveal(page_array_wf); };
    assert(process_tree_fields_wf(post.prc_mp)) by {
        assert(process_tree_fields_wf(pre.prc_mp)) by { reveal(process_perms_wf); };
        reveal(container_process_wf);
        assert(!pre.prc_mp.spec_index(parent_ptr).view().children.view().contains(process_pg_ptr)) by { reveal(per_container_process_tree_wf); reveal(process_children_parent_wf); };
        assert(!pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().contains(parent_ptr)) by { reveal(per_container_process_tree_wf); reveal(process_uppertree_seq_wf); };
        process_perms_wf_at(pre.prc_mp, parent_ptr);
    };
    assert(process_perms_wf(post.prc_mp)) by { reveal(process_perms_wf); };
    assert(container_perms_wf(post.ctn_mp)) by { reveal(container_perms_wf); reveal(container_tree_fields_wf); };
    assert(pcid_allocator_perms_wf(post.pcid_allc_mp)) by { reveal(pcid_allocator_perms_wf); };
    assert(post.default_pagetable_wf()) by { reveal(KernelK::default_pagetable_wf); };
}

proof fn create_process_from_staged_pages_eof_page_table_relations(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        !pre.prc_mp.dom().contains(process_pg_ptr),
        !pre.pt_mp.dom().contains(pagetable_pg_ptr),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        page_mappings_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr),
        page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr),
        pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr),
        iommu_table_pages_wf(post.it_mp, post.pg_arr),
        process_pagetable_wf(post.prc_mp, post.pt_mp),
        process_iommu_table_wf(post.prc_mp, post.it_mp),
        pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view()),
        iommu_table_no_huge_leaf_wf(post.it_mp),
        process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr),
        pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp),
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(mapped_4k_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_4k_page_pagetable_wf); reveal(pagetable_lower_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(mapped_2m_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_2m_page_pagetable_wf); reveal(pagetable_lower_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(mapped_1g_page_pagetable_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(mapped_1g_page_pagetable_wf); reveal(pagetable_perms_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(container_process_page_pagetable_wf(post.ctn_mp, post.prc_mp, post.pt_mp, post.pg_arr)) by { reveal(container_process_page_pagetable_wf); };
    assert(page_iommu_table_wf(post.ctn_mp, post.prc_mp, post.it_mp, post.pg_arr)) by { reveal(page_iommu_table_wf); reveal(iommu_table_perms_wf); page_ptr_valid_imply_page_index_valid(); };
    assert(pagetable_pages_wf(post.pt_mp, post.pt_lower.view(), post.pg_arr)) by { reveal(pagetable_pages_wf); };
    assert(iommu_table_pages_wf(post.it_mp, post.pg_arr)) by { iommu_table_pages_wf_preserved_for_page_state_eq(pre.it_mp, post.it_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pagetable_wf(post.prc_mp, post.pt_mp)) by { reveal(process_pagetable_wf); };
    assert(process_iommu_table_wf(post.prc_mp, post.it_mp)) by { reveal(process_iommu_table_wf); };
    assert(pagetable_no_1g_leaf_wf(post.pt_mp, post.pt_lower.view())) by { reveal(pagetable_no_1g_leaf_wf); };
    assert(iommu_table_no_huge_leaf_wf(post.it_mp)) by { reveal(iommu_table_no_huge_leaf_wf); };
    assert(process_emptied_tables_wf(post.prc_mp, post.pt_mp, post.pt_lower.view(), post.it_mp, post.pg_arr)) by {
        assert(post.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().mappings() == pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().mappings());
        assert(post.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().mappings() == pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().mappings());
        assert(post.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().mappings() == pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().mappings());
        reveal(process_emptied_tables_wf); reveal(process_pagetable_wf);
    };
    assert(pagetable_hidden_roots_only_when_write_locked_or_emptied(post.pt_mp, post.prc_mp)) by { reveal(pagetable_hidden_roots_only_when_write_locked_or_emptied); reveal(process_pagetable_wf); };
}

broadcast proof fn create_process_from_staged_pages_eof_thread_staged_pages_4k_backward(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
    thrd_ptr: RwLockThreadPtr, pg_ptr: PagePtr,
)
    requires
        thread_staged_4k_pages_wf(pre.thrd_mp, pre.pg_arr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr],
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
        post.thrd_mp.dom().contains(thrd_ptr),
        post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr),
    ensures
        #![trigger create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
            post.thrd_mp.spec_index(thrd_ptr).view().temp_alloc_cache_4k.view().contains(pg_ptr)]
        page_ptr_valid(pg_ptr) && post.pg_arr.spec_index(page_ptr2page_index(pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: thrd_ptr }),
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    if thrd_ptr != staging_thrd_ptr {
        thread_staged_4k_pages_wf_at(pre.thrd_mp, pre.pg_arr, thrd_ptr, pg_ptr);
        thread_staged_4k_pages_wf_at(pre.thrd_mp, pre.pg_arr, staging_thrd_ptr, process_pg_ptr);
        thread_staged_4k_pages_wf_at(pre.thrd_mp, pre.pg_arr, staging_thrd_ptr, pagetable_pg_ptr);
        thread_staged_4k_pages_wf_at(pre.thrd_mp, pre.pg_arr, staging_thrd_ptr, l4_pg_ptr);
        page_ptr_valid_imply_page_index_valid();
    }
}

proof fn create_process_from_staged_pages_eof_thread_staged_pages_4k(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        thread_staged_4k_pages_wf(pre.thrd_mp, pre.pg_arr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr],
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr),
{ broadcast use create_process_from_staged_pages_eof_thread_staged_pages_4k_backward; reveal(create_process_from_staged_pages_eof_transition_framing); reveal(thread_staged_4k_pages_wf); }

proof fn create_process_from_staged_pages_eof_thread_staged_pages_1g(pre: KernelK, post: KernelK, staging_thrd_ptr: RwLockThreadPtr)
    requires
        thread_staged_1g_pages_wf(pre.thrd_mp, pre.pg_arr),
        post.thrd_mp.dom() == pre.thrd_mp.dom(),
        forall|t: RwLockThreadPtr, p: PagePtr| #![trigger post.thrd_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p)]
            pre.thrd_mp.dom().contains(t) ==> post.thrd_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p) == pre.thrd_mp.spec_index(t).view().temp_alloc_cache_1g.view().contains(p),
        forall|i: PageIndex| #![trigger post.pg_arr.spec_index(i)]
            index_valid(NUM_PAGES, i) && (pre.pg_arr.spec_index(i).view().view().state is Owned1g || post.pg_arr.spec_index(i).view().view().state is Owned1g)
            ==> post.pg_arr.spec_index(i).view().view().state == pre.pg_arr.spec_index(i).view().view().state,
    ensures
        thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr),
{ reveal(thread_staged_1g_pages_wf); }

proof fn create_process_from_staged_pages_eof_memory_relations(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        !pre.prc_mp.dom().contains(process_pg_ptr),
        !pre.pt_mp.dom().contains(pagetable_pg_ptr),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        container_owned_pages_wf(post.ctn_mp, post.pg_arr),
        hugepage_2m_wf(post.pg_arr),
        hugepage_1g_wf(post.pg_arr),
        container_pages_wf(post.ctn_mp, post.pg_arr),
        process_pages_wf(post.prc_mp, post.pg_arr),
        thread_pages_wf(post.thrd_mp, post.pg_arr),
        scheduler_pages_wf(post.sched_mp, post.pg_arr),
        cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr),
        pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr),
        thread_staged_pages_wf(post.thrd_mp, post.pg_arr),
        endpoint_pages_wf(post.ep_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_page_ptrs_wf(post.allc_1g_mp),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr)) by {
        allocator_4k_pages_wf_preserved_for_page_state_eq(pre.allc_4k_mp, post.allc_4k_mp, pre.pg_arr, post.pg_arr);
        allocator_2m_pages_wf_preserved_for_page_state_eq(pre.allc_2m_mp, post.allc_2m_mp, pre.pg_arr, post.pg_arr);
        allocator_1g_pages_wf_preserved_for_page_state_eq(pre.allc_1g_mp, post.allc_1g_mp, pre.pg_arr, post.pg_arr);
    };
    assert(container_owned_pages_wf(post.ctn_mp, post.pg_arr)) by { container_page_owner_wf_preserved_for_owned_pages_and_owning_container_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(hugepage_2m_wf(post.pg_arr)) by { hugepage_2m_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(hugepage_1g_wf(post.pg_arr)) by { hugepage_1g_wf_preserved_for_page_state_eq(pre.pg_arr, post.pg_arr); };
    assert(container_pages_wf(post.ctn_mp, post.pg_arr)) by { container_pages_wf_preserved_for_page_state_eq(pre.ctn_mp, post.ctn_mp, pre.pg_arr, post.pg_arr); };
    assert(process_pages_wf(post.prc_mp, post.pg_arr)) by { reveal(process_pages_wf); };
    assert(thread_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_pages_wf_preserved_for_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(scheduler_pages_wf(post.sched_mp, post.pg_arr)) by { scheduler_pages_wf_preserved_for_page_state_eq(pre.sched_mp, post.sched_mp, pre.pg_arr, post.pg_arr); };
    assert(cpu_set_pages_wf(post.cpu_set_mp, post.pg_arr)) by { reveal(cpu_set_pages_wf); };
    assert(pcid_allocator_pages_wf(post.pcid_allc_mp, post.pg_arr)) by { pcid_allocator_pages_wf_preserved_for_page_state_eq(pre.pcid_allc_mp, post.pcid_allc_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_4k_pages_wf(post.thrd_mp, post.pg_arr)) by { create_process_from_staged_pages_eof_thread_staged_pages_4k(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid); };
    assert(thread_staged_2m_pages_wf(post.thrd_mp, post.pg_arr)) by { thread_staged_2m_pages_wf_preserved_for_temp_cache_and_owned_page_state_eq(pre.thrd_mp, post.thrd_mp, pre.pg_arr, post.pg_arr); };
    assert(thread_staged_1g_pages_wf(post.thrd_mp, post.pg_arr)) by { create_process_from_staged_pages_eof_thread_staged_pages_1g(pre, post, staging_thrd_ptr); };
    assert(endpoint_pages_wf(post.ep_mp, post.pg_arr)) by { endpoint_pages_wf_preserved_for_page_state_eq(pre.ep_mp, post.ep_mp, pre.pg_arr, post.pg_arr); };
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { container_allocator_wf_preserved_for_owner_depth_eq(pre.ctn_mp, post.ctn_mp, pre.allc_4k_mp, post.allc_4k_mp, pre.allc_2m_mp, post.allc_2m_mp, pre.allc_1g_mp, post.allc_1g_mp); };
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by {
        reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by {
        reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by {
        reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf);
        reveal(allocator_free_page_ptrs_wf);
    };
}

pub(crate) proof fn create_process_from_staged_pages_eof_allocator_quota_wf(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, with_iommu: bool,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        with_iommu ==> {
            &&& process_pg_ptr != iommu_table_pg_ptr && process_pg_ptr != iommu_l4_pg_ptr
            &&& pagetable_pg_ptr != iommu_table_pg_ptr && pagetable_pg_ptr != iommu_l4_pg_ptr
            &&& l4_pg_ptr != iommu_table_pg_ptr && l4_pg_ptr != iommu_l4_pg_ptr
            &&& iommu_table_pg_ptr != iommu_l4_pg_ptr
        },
        !pre.prc_mp.dom().contains(process_pg_ptr),
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k >= if with_iommu { 5usize } else { 3usize },
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= if with_iommu {
            set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, iommu_table_pg_ptr, iommu_l4_pg_ptr]
        } else {
            set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr]
        },
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, with_iommu, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp),
        container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp),
        container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp),
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.allc_4k_mp)) by {
        let old_target_owned = pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view();
        reveal(container_process_wf); lemma_process_effective_quota_folds_insert_zero(old_target_owned, pre.prc_mp, post.prc_mp, process_pg_ptr);
        lemma_process_effective_quota_4k_fold_sum_eq_forall(); reveal(container_process_allocator_quota_4k_wf);
    };
    assert(container_thread_wf(post.ctn_mp, pre.thrd_mp)) by { reveal(container_thread_wf); };
    container_process_allocator_quota_4k_wf_preserved_for_thread_4k_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_4k_mp);
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.allc_2m_mp)) by {
        let old_target_owned = pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view();
        reveal(container_process_wf); lemma_process_effective_quota_folds_insert_zero(old_target_owned, pre.prc_mp, post.prc_mp, process_pg_ptr);
        lemma_process_effective_quota_2m_fold_sum_eq_forall(); reveal(container_process_allocator_quota_2m_wf);
    };
    container_process_allocator_quota_2m_wf_preserved_for_thread_2m_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_2m_mp);
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.allc_1g_mp)) by {
        let old_target_owned = pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view();
        reveal(container_process_wf); lemma_process_effective_quota_folds_insert_zero(old_target_owned, pre.prc_mp, post.prc_mp, process_pg_ptr);
        lemma_process_effective_quota_1g_fold_sum_eq_forall(); reveal(container_process_allocator_quota_1g_wf);
    };
    container_process_allocator_quota_1g_wf_preserved_for_thread_1g_fields(post.ctn_mp, post.prc_mp, pre.thrd_mp, post.thrd_mp, post.allc_1g_mp);
}

proof fn create_process_from_staged_pages_eof_memory_management_inv(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        post.subsystems_inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        !pre.prc_mp.dom().contains(process_pg_ptr),
        !pre.pt_mp.dom().contains(pagetable_pg_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == ctn_ptr,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k >= 3,
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr],
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        post.memory_management_inv(),
{
    create_process_from_staged_pages_eof_page_table_relations(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    create_process_from_staged_pages_eof_memory_relations(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    create_process_from_staged_pages_eof_allocator_quota_wf(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    create_process_from_staged_pages_eof_process_kernel_pages_owner_wf(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    create_process_from_staged_pages_eof_page_object_owner_wf(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    create_process_from_staged_pages_eof_container_kill_retire_wf(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
}

/// The staged pages leave their thread for kernel-object states that name no owner object, so every page keeps its
/// object owner.
pub(crate) proof fn create_process_from_staged_pages_eof_page_object_owner_wf(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, with_iommu: bool,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, with_iommu, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        page_object_owner_wf(post.ctn_mp, post.thrd_mp, post.pg_arr),
{ reveal(create_process_from_staged_pages_eof_transition_framing); reveal(page_object_owner_wf); reveal(container_owned_pages_wf); }

/// The new process's container owns its parent, so it is not retire-ready; every other container and the allocators are
/// unchanged.
pub(crate) proof fn create_process_from_staged_pages_eof_container_kill_retire_wf(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, with_iommu: bool,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        container_kill_retire_wf(pre.ctn_mp, pre.allc_4k_mp, pre.allc_2m_mp, pre.allc_1g_mp),
        container_process_wf(pre.ctn_mp, pre.prc_mp),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, with_iommu, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{ reveal(create_process_from_staged_pages_eof_transition_framing); container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, parent_ptr); reveal(container_kill_retire_wf); }

/// The new process's object page, page-table root page, and L4 page belong to its container; every other page keeps its
/// state, owner, and process.
proof fn create_process_from_staged_pages_eof_process_kernel_pages_owner_wf(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures
        process_object_pages_owner_wf(post.prc_mp, post.pt_mp, post.it_mp, post.pg_arr),
{
    hide(Seq::contains); reveal(create_process_from_staged_pages_eof_transition_framing);
    page_ptr_valid_imply_page_index_valid(); page_ptr2page_index_injective();
    reveal(process_object_pages_owner_wf); reveal(process_pages_wf); reveal(pagetable_pages_wf); reveal(iommu_table_pages_wf); reveal(process_pagetable_wf); reveal(process_iommu_table_wf);
}

proof fn create_process_from_staged_pages_eof_process_tree_invariants(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, with_iommu: bool,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_pg_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == ctn_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().owning_container == ctn_ptr,
        pre.pcid_allc_mp.dom().contains(pcid_allc_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator == pcid_allc_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allc_ptr).view().pcid_is_free(pcid),
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, with_iommu, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
        post.prc_mp.spec_index(process_pg_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.spec_index(ctn_ptr).inv(),
        post.thrd_mp.spec_index(staging_thrd_ptr).inv(),
        post.pcid_allc_mp.spec_index(pcid_allc_ptr).inv(),
        process_perms_wf(post.prc_mp),
    ensures
        container_tree_wf(post.rt_ctn, post.ctn_mp),
        container_process_wf(post.ctn_mp, post.prc_mp),
        per_container_process_tree_wf(post.ctn_mp, post.prc_mp),
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    let ancestors = pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr);
    let root_process = pre.ctn_mp.spec_index(ctn_ptr).view().root_process;
    let process_tree_dom = pre.ctn_mp.spec_index(ctn_ptr).view_ghost().owned_processes.view();
    assert(process_tree_wf(root_process, process_tree_dom, pre.prc_mp)) by { reveal(container_process_wf); reveal(per_container_process_tree_wf); };
    assert(process_add_child_ensures(root_process, process_tree_dom, pre.prc_mp, post.prc_mp, parent_ptr, process_pg_ptr)) by { reveal(container_process_wf); ancestors.to_set_ensures(); seq_push_implies_contains::<RwLockProcessPtr>(); };
    process_add_child_preserves_tree_wf(root_process, process_tree_dom, pre.prc_mp, post.prc_mp, parent_ptr, process_pg_ptr);
    assert(container_tree_wf(post.rt_ctn, post.ctn_mp)) by { container_no_change_to_tree_fields_imply_wf(pre.rt_ctn, pre.ctn_mp, post.ctn_mp); };
    assert(container_process_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_process_wf); };
    assert(per_container_process_tree_wf(post.ctn_mp, post.prc_mp)) by {
        reveal(per_container_process_tree_wf); reveal(container_process_wf); reveal(process_uppertree_seq_wf); process_no_change_to_tree_fields_imply_wf_forall();
        ancestors.to_set_ensures();
    };
}

/// Separate query: inside the combined process-management closure this leaf fails in the monolith.
proof fn create_process_from_staged_pages_eof_container_cpu_wf(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, with_iommu: bool,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        container_cpu_wf(pre.ctn_mp, pre.cpu_set_mp, pre.cpu_arr),
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, with_iommu, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
    ensures container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr),
{ reveal(create_process_from_staged_pages_eof_transition_framing); reveal(container_cpu_wf); }

pub(crate) proof fn create_process_from_staged_pages_eof_process_management_inv(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, with_iommu: bool,
    iommu_table_pg_ptr: PagePtr, iommu_l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thrd_ptr: RwLockThreadPtr,
    ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        !pre.prc_mp.dom().contains(process_pg_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == ctn_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().owning_container == ctn_ptr,
        pre.pcid_allc_mp.dom().contains(pcid_allc_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator == pcid_allc_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allc_ptr).view().pcid_is_free(pcid),
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, with_iommu, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
        post.prc_mp.spec_index(process_pg_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.spec_index(ctn_ptr).inv(),
        post.thrd_mp.spec_index(staging_thrd_ptr).inv(),
        post.pcid_allc_mp.spec_index(pcid_allc_ptr).inv(),
        post.subsystems_inv(),
    ensures
        post.process_management_inv(),
{
    hide(Seq::contains); reveal(create_process_from_staged_pages_eof_transition_framing);
    create_process_from_staged_pages_eof_process_tree_invariants(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, with_iommu, iommu_table_pg_ptr, iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    assert(post.process_management_inv()) by {
        assert(post.ctn_mp.spec_index(post.rt_ctn).view_ghost().owned_processes.view().contains(post.ctn_mp.spec_index(post.rt_ctn).view().root_process)) by { reveal(container_root_wf); };
        assert(container_endpoint_wf(post.ctn_mp, post.ep_mp)) by { container_endpoint_wf_preserved_for_endpoint_owner_eq(pre.ctn_mp, post.ctn_mp, pre.ep_mp, post.ep_mp); };
        assert(container_cpu_wf(post.ctn_mp, post.cpu_set_mp, post.cpu_arr)) by {
            create_process_from_staged_pages_eof_container_cpu_wf(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, with_iommu, iommu_table_pg_ptr,
                iommu_l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
        };
        assert(thread_endpoint_ref_counter_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_ref_counter_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
        assert(thread_endpoint_queue_wf(post.thrd_mp, post.ep_mp)) by { thread_endpoint_queue_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.ep_mp); };
        assert(thread_caller_callee_wf(post.thrd_mp)) by { thread_caller_callee_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp); };
        assert(thread_dangling_chain_end_wf(post.thrd_mp)) by { thread_dangling_chain_end_wf_from_dangling_chain_fields_unchanged(pre.thrd_mp, post.thrd_mp); };
        assert(container_thread_endpoint_wf(post.ctn_mp, post.thrd_mp, post.ep_mp)) by {
            container_thread_endpoint_wf_preserved_for_descriptor_owner_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp, pre.ep_mp, post.ep_mp);
            reveal(container_endpoint_wf);
            reveal(thread_endpoint_ref_counter_wf);
        };
        assert(container_scheduler_wf(post.ctn_mp, post.sched_mp)) by { container_scheduler_wf_preserved_for_scheduler_owner_eq(pre.ctn_mp, post.ctn_mp, pre.sched_mp, post.sched_mp); };
        assert(container_cpu_set_wf(post.ctn_mp, post.cpu_set_mp)) by { reveal(container_cpu_set_wf); };
        assert(container_cpu_offline_flags_wf(post.ctn_mp, post.cpu_offline_mp)) by { container_cpu_offline_flags_wf_preserved_for_flags_owner_eq(pre.ctn_mp, post.ctn_mp, pre.cpu_offline_mp, post.cpu_offline_mp); };
        assert(container_pcid_allocator_wf(post.ctn_mp, post.pcid_allc_mp)) by { reveal(container_pcid_allocator_wf); };
        assert(process_pcid_allocator_wf(post.ctn_mp, post.prc_mp, post.pcid_allc_mp)) by { reveal(process_pcid_allocator_wf); reveal(container_pcid_allocator_wf); };
        assert(container_thread_scheduler_wf(post.ctn_mp, post.thrd_mp, post.sched_mp)) by { container_thread_scheduler_wf_preserved_for_scheduled_thread_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp, post.sched_mp); reveal(container_thread_wf); };
        assert(container_thread_wf(post.ctn_mp, post.thrd_mp)) by { container_thread_wf_preserved_for_container_thread_link_eq(pre.ctn_mp, post.ctn_mp, pre.thrd_mp, post.thrd_mp); };
        assert(process_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(process_kill_mark_wf); };
        assert(container_kill_mark_wf(post.ctn_mp, post.prc_mp)) by { reveal(container_kill_mark_wf); };
        assert(cpu_set_kill_mark_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp)) by { reveal(cpu_set_kill_mark_wf); container_process_wf_process_at(pre.ctn_mp, pre.prc_mp, parent_ptr); };
        assert(process_state_lock_wf(post.prc_mp)) by { reveal(process_state_lock_wf); };
        assert(process_cpu_wf(post.prc_mp, post.cpu_arr)) by { reveal(process_cpu_wf); };
        assert(process_thread_wf(post.prc_mp, post.thrd_mp)) by { reveal(Seq::contains); reveal(process_thread_wf); };
        assert(process_emptied_threads_wf(post.prc_mp, post.thrd_mp)) by { reveal(process_emptied_threads_wf); };
        assert(thread_cpu_wf(post.thrd_mp, post.cpu_arr)) by { thread_cpu_wf_preserved_for_thread_process_management_fields(pre.thrd_mp, post.thrd_mp, post.cpu_arr); };
    };
}

pub(super) proof fn create_process_from_staged_pages_eof_inv(
    pre: KernelK, post: KernelK, process_pg_ptr: PagePtr, pagetable_pg_ptr: PagePtr, l4_pg_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thrd_ptr: RwLockThreadPtr, ctn_ptr: RwLockContainerPtr, pcid_allc_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
)
    requires
        pre.inv(),
        page_ptr_valid(process_pg_ptr),
        page_ptr_valid(pagetable_pg_ptr),
        page_ptr_valid(l4_pg_ptr),
        process_pg_ptr != pagetable_pg_ptr,
        process_pg_ptr != l4_pg_ptr,
        pagetable_pg_ptr != l4_pg_ptr,
        !pre.prc_mp.dom().contains(process_pg_ptr),
        !pre.pt_mp.dom().contains(pagetable_pg_ptr),
        pre.prc_mp.dom().contains(parent_ptr),
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == ctn_ptr,
        pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        pre.ctn_mp.dom().contains(ctn_ptr),
        pre.thrd_mp.dom().contains(staging_thrd_ptr),
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().owning_container == ctn_ptr,
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k >= 3,
        pre.thrd_mp.spec_index(staging_thrd_ptr).view().temp_alloc_cache_4k.view() =~= set![process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr],
        pre.pcid_allc_mp.dom().contains(pcid_allc_ptr),
        pre.ctn_mp.spec_index(ctn_ptr).view_rodata().view().pcid_allocator == pcid_allc_ptr,
        pre.pcid_allc_mp.spec_index(pcid_allc_ptr).view().pcid_is_free(pcid),
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().view().owning_container == ctn_ptr,
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thrd_ptr }),
        pre.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().view().owning_container == ctn_ptr,
        create_process_from_staged_pages_eof_transition_framing(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid),
        post.pg_arr.inv(),
        post.pg_arr.spec_index(page_ptr2page_index(process_pg_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(pagetable_pg_ptr)).view().inv(),
        post.pg_arr.spec_index(page_ptr2page_index(l4_pg_ptr)).view().inv(),
        post.pt_mp.perms_wf(),
        post.pt_mp.spec_index(pagetable_pg_ptr).inv(),
        post.prc_mp.perms_wf(),
        post.prc_mp.spec_index(process_pg_ptr).inv(),
        post.prc_mp.spec_index(parent_ptr).inv(),
        post.ctn_mp.perms_wf(),
        post.ctn_mp.spec_index(ctn_ptr).inv(),
        post.thrd_mp.spec_index(staging_thrd_ptr).inv(),
        thread_perms_wf(post.thrd_mp),
        post.pcid_allc_mp.perms_wf(),
        post.pcid_allc_mp.spec_index(pcid_allc_ptr).inv(),
    ensures
        post == (KernelK { pg_arr: post.pg_arr, prc_mp: post.prc_mp, pt_mp: post.pt_mp, pt_lower: post.pt_lower, ctn_mp: post.ctn_mp, thrd_mp: post.thrd_mp, pcid_allc_mp: post.pcid_allc_mp, ..pre }),
        post.prc_mp.dom() == pre.prc_mp.dom().insert(process_pg_ptr),
        post.prc_mp.spec_index(parent_ptr).view().owned_threads == pre.prc_mp.spec_index(parent_ptr).view().owned_threads,
        post.prc_mp.spec_index(parent_ptr).being_killed() == pre.prc_mp.spec_index(parent_ptr).being_killed(),
        !post.prc_mp.spec_index(process_pg_ptr).being_killed(),
        !post.prc_mp.spec_index(process_pg_ptr).view().zombie,
        post.prc_mp.spec_index(process_pg_ptr).view().state.view() is Creating,
        post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().owning_container == ctn_ptr,
        post.prc_mp.spec_index(process_pg_ptr).view_rodata().view().pagetable == pagetable_pg_ptr,
        post.prc_mp.spec_index(process_pg_ptr).view().iommu_table == None,
        post.pt_mp.dom() == pre.pt_mp.dom().insert(pagetable_pg_ptr),
        forall|pt: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(pt)]
            pre.pt_mp.dom().contains(pt) ==> post.pt_mp.spec_index(pt) == pre.pt_mp.spec_index(pt),
        whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable_pg_ptr).is_empty(),
        post.pt_mp.spec_index(pagetable_pg_ptr).view().proc_ptr == process_pg_ptr,
        post.prc_mp.spec_index(process_pg_ptr).view().pagetable == pagetable_pg_ptr,
        post.ctn_mp.dom() == pre.ctn_mp.dom(),
        post.ctn_mp.spec_index(ctn_ptr).view_rodata() == pre.ctn_mp.spec_index(ctn_ptr).view_rodata(),
        post.ctn_mp.spec_index(ctn_ptr).being_killed() == pre.ctn_mp.spec_index(ctn_ptr).being_killed(),
        post.ctn_mp.spec_index(ctn_ptr).killer_info() == pre.ctn_mp.spec_index(ctn_ptr).killer_info(),
        post.thrd_mp.dom() == pre.thrd_mp.dom(),
        post.thrd_mp.spec_index(staging_thrd_ptr).view() == (Thread {
            quota_4k: (pre.thrd_mp.spec_index(staging_thrd_ptr).view().quota_4k - 3) as usize,
            temp_alloc_cache_4k: Ghost(Set::empty()), ..pre.thrd_mp.spec_index(staging_thrd_ptr).view()
        }),
        post.thrd_mp.spec_index(staging_thrd_ptr).being_killed() == pre.thrd_mp.spec_index(staging_thrd_ptr).being_killed(),
        post.pcid_allc_mp.dom() == pre.pcid_allc_mp.dom(),
        post.inv(),
{
    reveal(create_process_from_staged_pages_eof_transition_framing);
    create_process_from_staged_pages_eof_subsystems_inv(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    create_process_from_staged_pages_eof_memory_management_inv(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    create_process_from_staged_pages_eof_process_management_inv(pre, post, process_pg_ptr, pagetable_pg_ptr, l4_pg_ptr, false, 0, 0, parent_ptr, staging_thrd_ptr, ctn_ptr, pcid_allc_ptr, pcid);
    assert(iommu_root_table_process_wf(post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_root_table_process_wf); };
    assert(process_pci_function_ownership_wf(post.irt.view(), post.prc_mp)) by { reveal(process_pci_function_ownership_wf); };
    assert(iommu_tlb_wf(post.iommu_tlb, post.irt.view(), post.prc_mp, post.it_mp)) by { reveal(iommu_tlb_wf); reveal(iommu_root_table_process_wf); };
    assert(cpu_dirty_map_wf(post.ctn_mp, post.cpu_set_mp, post.prc_mp, post.cpu_arr, post.cpu_tlb, post.pt_mp, post.pcid_needflush)) by {
        reveal(cpu_dirty_map_process_in_cpu_container); reveal(container_cpu_wf); reveal(cpu_dirty_map_proc_pcid_match); reveal(cpu_dirty_map_pagetable_pcid_match);
    };
    assert(cpu_tlb_wf(post.cpu_tlb, post.pt_mp, post.pt_lower.view(), post.cpu_arr, post.pcid_needflush)) by { reveal(cpu_tlb_wf); };
    structure_caches_dirty_maps_and_table_structures_unchanged_implies_structure_cache_wf(pre, post);
}

}
