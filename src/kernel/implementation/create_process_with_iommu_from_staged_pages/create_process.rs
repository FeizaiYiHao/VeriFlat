use vstd::prelude::*;
use crate::*;
use super::*;

verus! {
/// User-view change predicate for publishing a process with empty CPU and IOMMU page tables.
#[verifier::opaque]
pub open spec fn kernel_u_create_process_with_iommu_changed(
    old_u: KernelU, new_u: KernelU, parent_ptr: RwLockProcessPtr, child_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
) -> bool {
    let child = new_u.process_map.spec_index(child_ptr);
    let old_staging = old_u.thread_map.spec_index(staging_thread_ptr);
    &&& new_u.endpoint_map == old_u.endpoint_map
    &&& new_u.iommu_root_table == old_u.iommu_root_table
    &&& new_u.cpu_array == old_u.cpu_array
    &&& old_u.thread_map.dom().contains(staging_thread_ptr)
    &&& old_staging.quota_4k >= 5
    &&& new_u.thread_map == old_u.thread_map.insert(staging_thread_ptr, ThreadU {
        quota_4k: (old_staging.quota_4k as int - 5) as usize, ..old_staging
    })
    &&& old_u.process_map.dom().contains(parent_ptr)
    &&& !old_u.process_map.dom().contains(child_ptr)
    &&& new_u.process_map.dom() == old_u.process_map.dom().insert(child_ptr)
    &&& !child.zombie
    &&& child.pagetable is Some
    &&& child.pagetable.unwrap().mapping_4k.is_empty()
    &&& child.pagetable.unwrap().mapping_2m.is_empty()
    &&& child.pagetable.unwrap().mapping_1g.is_empty()
    &&& child.iommu_table is Some
    &&& child.iommu_table.unwrap().mapping_4k.is_empty()
    &&& child.iommu_table.unwrap().mapping_2m.is_empty()
    &&& child.iommu_table.unwrap().mapping_1g.is_empty()
    &&& child.owned_pci_functions.is_empty()
    &&& child.quota_4k == 0
    &&& child.quota_2m == 0
    &&& child.quota_1g == 0
    &&& child.parent == Some(parent_ptr)
    &&& child.children.len() == 0
    &&& child.depth == old_u.process_map.spec_index(parent_ptr).depth + 1
    &&& child.uppertree_seq == old_u.process_map.spec_index(parent_ptr).uppertree_seq.push(parent_ptr)
    &&& child.subtree_set.is_empty()
    &&& child.owned_threads.len() == 0
    &&& !child.killed
    &&& forall|p: RwLockProcessPtr|
        #![trigger new_u.process_map.spec_index(p)]
        old_u.process_map.dom().contains(p) ==> {
            &&& new_u.process_map.spec_index(p).pagetable == old_u.process_map.spec_index(p).pagetable
            &&& new_u.process_map.spec_index(p).iommu_table == old_u.process_map.spec_index(p).iommu_table
            &&& new_u.process_map.spec_index(p).owned_pci_functions == old_u.process_map.spec_index(p).owned_pci_functions
            &&& new_u.process_map.spec_index(p).quota_4k == old_u.process_map.spec_index(p).quota_4k
            &&& new_u.process_map.spec_index(p).quota_2m == old_u.process_map.spec_index(p).quota_2m
            &&& new_u.process_map.spec_index(p).quota_1g == old_u.process_map.spec_index(p).quota_1g
            &&& new_u.process_map.spec_index(p).parent == old_u.process_map.spec_index(p).parent
            &&& new_u.process_map.spec_index(p).depth == old_u.process_map.spec_index(p).depth
            &&& new_u.process_map.spec_index(p).uppertree_seq == old_u.process_map.spec_index(p).uppertree_seq
            &&& new_u.process_map.spec_index(p).owned_threads == old_u.process_map.spec_index(p).owned_threads
            &&& new_u.process_map.spec_index(p).zombie == old_u.process_map.spec_index(p).zombie
            &&& new_u.process_map.spec_index(p).killed == old_u.process_map.spec_index(p).killed
            &&& p == parent_ptr ==> new_u.process_map.spec_index(p).children == old_u.process_map.spec_index(p).children.push(child_ptr)
            &&& p != parent_ptr ==> new_u.process_map.spec_index(p).children == old_u.process_map.spec_index(p).children
            &&& child.uppertree_seq.contains(p) ==> new_u.process_map.spec_index(p).subtree_set == old_u.process_map.spec_index(p).subtree_set.insert(child_ptr)
            &&& !child.uppertree_seq.contains(p) ==> new_u.process_map.spec_index(p).subtree_set == old_u.process_map.spec_index(p).subtree_set
        }
}

#[verifier::opaque]
pub open spec fn create_process_with_iommu_from_staged_pages_kernel_state_framing(
    pre: KernelK, post: KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr, staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr, pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid,
) -> bool {
    let process_page_index = page_ptr2page_index(process_page_ptr);
    let pagetable_page_index = page_ptr2page_index(pagetable_page_ptr);
    let l4_page_index = page_ptr2page_index(l4_page_ptr);
    let iommu_table_page_index = page_ptr2page_index(iommu_table_page_ptr);
    let iommu_l4_page_index = page_ptr2page_index(iommu_l4_page_ptr);
    let ancestors = pre.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view().push(parent_ptr);
    &&& post.irt == pre.irt
    &&& post.cpu_arr == pre.cpu_arr
    &&& post.pcid_needflush == pre.pcid_needflush
    &&& post.cpu_published == pre.cpu_published
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
    &&& forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index)]
        #![trigger pre.pg_arr.spec_index(index)]
        index_valid(NUM_PAGES, index) && index != process_page_index && index != pagetable_page_index && index != l4_page_index && index != iommu_table_page_index && index != iommu_l4_page_index ==> post.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index)
    &&& post.pg_arr.spec_index(l4_page_index).view().view() == (Page {
        state: PageState::Allocated4k {
            state: Allocated4KPageState::PageTable {
                pagetable_root: pagetable_page_ptr,
            },
        },
        perm_4k: post.pg_arr.spec_index(l4_page_index).view().view().perm_4k,
        ..pre.pg_arr.spec_index(l4_page_index).view().view()
    })
    &&& post.pg_arr.spec_index(l4_page_index).view().view().perm_4k.view().is_none()
    &&& post.pg_arr.spec_index(l4_page_index).view().view_rodata() == pre.pg_arr.spec_index(l4_page_index).view().view_rodata()
    &&& post.pg_arr.spec_index(l4_page_index).view().view_ghost() == pre.pg_arr.spec_index(l4_page_index).view().view_ghost()
    &&& post.pg_arr.spec_index(l4_page_index).view().locking_thread() == pre.pg_arr.spec_index(l4_page_index).view().locking_thread()
    &&& post.pg_arr.spec_index(pagetable_page_index).view().view() == (Page {
        state: PageState::Allocated4k {
            state: Allocated4KPageState::AsPageTableRoot,
        },
        perm_4k: post.pg_arr.spec_index(pagetable_page_index).view().view().perm_4k,
        ..pre.pg_arr.spec_index(pagetable_page_index).view().view()
    })
    &&& post.pg_arr.spec_index(pagetable_page_index).view().view().perm_4k.view().is_none()
    &&& post.pg_arr.spec_index(pagetable_page_index).view().view_rodata() == pre.pg_arr.spec_index(pagetable_page_index).view().view_rodata()
    &&& post.pg_arr.spec_index(pagetable_page_index).view().view_ghost() == pre.pg_arr.spec_index(pagetable_page_index).view().view_ghost()
    &&& post.pg_arr.spec_index(pagetable_page_index).view().locking_thread() == pre.pg_arr.spec_index(pagetable_page_index).view().locking_thread()
    &&& post.pg_arr.spec_index(iommu_l4_page_index).view().view() == (Page {
        state: PageState::IOMMUTable {
            iommu_table_root: iommu_table_page_ptr,
        },
        perm_4k: post.pg_arr.spec_index(iommu_l4_page_index).view().view().perm_4k,
        ..pre.pg_arr.spec_index(iommu_l4_page_index).view().view()
    })
    &&& post.pg_arr.spec_index(iommu_l4_page_index).view().view().perm_4k.view().is_none()
    &&& post.pg_arr.spec_index(iommu_l4_page_index).view().view_rodata() == pre.pg_arr.spec_index(iommu_l4_page_index).view().view_rodata()
    &&& post.pg_arr.spec_index(iommu_l4_page_index).view().view_ghost() == pre.pg_arr.spec_index(iommu_l4_page_index).view().view_ghost()
    &&& post.pg_arr.spec_index(iommu_l4_page_index).view().locking_thread() == pre.pg_arr.spec_index(iommu_l4_page_index).view().locking_thread()
    &&& post.pg_arr.spec_index(iommu_table_page_index).view().view() == (Page {
        state: PageState::Allocated4k {
            state: Allocated4KPageState::AsIommuTableRoot,
        },
        perm_4k: post.pg_arr.spec_index(iommu_table_page_index).view().view().perm_4k,
        ..pre.pg_arr.spec_index(iommu_table_page_index).view().view()
    })
    &&& post.pg_arr.spec_index(iommu_table_page_index).view().view().perm_4k.view().is_none()
    &&& post.pg_arr.spec_index(iommu_table_page_index).view().view_rodata() == pre.pg_arr.spec_index(iommu_table_page_index).view().view_rodata()
    &&& post.pg_arr.spec_index(iommu_table_page_index).view().view_ghost() == pre.pg_arr.spec_index(iommu_table_page_index).view().view_ghost()
    &&& post.pg_arr.spec_index(iommu_table_page_index).view().locking_thread() == pre.pg_arr.spec_index(iommu_table_page_index).view().locking_thread()
    &&& post.pg_arr.spec_index(process_page_index).view().view() == (Page {
        state: PageState::Allocated4k {
            state: Allocated4KPageState::AsProcess,
        },
        perm_4k: post.pg_arr.spec_index(process_page_index).view().view().perm_4k,
        ..pre.pg_arr.spec_index(process_page_index).view().view()
    })
    &&& post.pg_arr.spec_index(process_page_index).view().view().perm_4k.view().is_none()
    &&& post.pg_arr.spec_index(process_page_index).view().view_rodata() == pre.pg_arr.spec_index(process_page_index).view().view_rodata()
    &&& post.pg_arr.spec_index(process_page_index).view().view_ghost() == pre.pg_arr.spec_index(process_page_index).view().view_ghost()
    &&& post.pg_arr.spec_index(process_page_index).view().locking_thread() == pre.pg_arr.spec_index(process_page_index).view().locking_thread()
    &&& post.pt_mp.dom() == pre.pt_mp.dom().insert(pagetable_page_ptr)
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger post.pt_mp.dom().contains(pt_ptr)]
        #![trigger post.pt_mp.spec_index(pt_ptr)]
        #![trigger pre.pt_mp.spec_index(pt_ptr)]
        post.pt_mp.dom().contains(pt_ptr) && pt_ptr != pagetable_page_ptr ==> {
            &&& pre.pt_mp.dom().contains(pt_ptr)
            &&& post.pt_mp.spec_index(pt_ptr) == pre.pt_mp.spec_index(pt_ptr)
        }
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger post.pt_mp.view().spec_index(pt_ptr).is_init()]
        post.pt_mp.dom().contains(pt_ptr) && pt_ptr != pagetable_page_ptr ==> {
            &&& post.pt_mp.view().spec_index(pt_ptr).is_init()
            &&& post.pt_mp.view().spec_index(pt_ptr).addr() == pt_ptr
        }
    &&& post.pt_mp.view().spec_index(pagetable_page_ptr).is_init()
    &&& post.pt_mp.view().spec_index(pagetable_page_ptr).addr() == pagetable_page_ptr
    &&& post.pt_mp.spec_index(pagetable_page_ptr).is_init()
    &&& !post.pt_mp.spec_index(pagetable_page_ptr).being_killed()
    &&& post.pt_mp.spec_index(pagetable_page_ptr).view().proc_ptr == process_page_ptr
    &&& post.pt_mp.spec_index(pagetable_page_ptr).view().pcid_value() == pcid
    &&& post.pt_mp.spec_index(pagetable_page_ptr).view().cr3 == l4_page_ptr
    &&& post.pt_mp.spec_index(pagetable_page_ptr).view().kernel_l4_end == pre.dflt_pt.view().kernel_l4_end
    &&& post.pt_mp.spec_index(pagetable_page_ptr).view().is_empty()
    &&& post.pt_mp.spec_index(pagetable_page_ptr).view().page_closure() == set![l4_page_ptr]
    &&& post.it_mp.dom() == pre.it_mp.dom().insert(iommu_table_page_ptr)
    &&& forall|it_ptr: RwLockPageTableRoot|
        #![trigger post.it_mp.dom().contains(it_ptr)]
        #![trigger post.it_mp.spec_index(it_ptr)]
        #![trigger pre.it_mp.spec_index(it_ptr)]
        post.it_mp.dom().contains(it_ptr) && it_ptr != iommu_table_page_ptr ==> {
            &&& pre.it_mp.dom().contains(it_ptr)
            &&& post.it_mp.spec_index(it_ptr) == pre.it_mp.spec_index(it_ptr)
        }
    &&& forall|it_ptr: RwLockPageTableRoot|
        #![trigger post.it_mp.view().spec_index(it_ptr).is_init()]
        post.it_mp.dom().contains(it_ptr) && it_ptr != iommu_table_page_ptr ==> {
            &&& post.it_mp.view().spec_index(it_ptr).is_init()
            &&& post.it_mp.view().spec_index(it_ptr).addr() == it_ptr
        }
    &&& post.it_mp.view().spec_index(iommu_table_page_ptr).is_init()
    &&& post.it_mp.view().spec_index(iommu_table_page_ptr).addr() == iommu_table_page_ptr
    &&& post.it_mp.spec_index(iommu_table_page_ptr).is_init()
    &&& !post.it_mp.spec_index(iommu_table_page_ptr).being_killed()
    &&& post.it_mp.spec_index(iommu_table_page_ptr).view().proc_ptr == process_page_ptr
    &&& post.it_mp.spec_index(iommu_table_page_ptr).view().pcid is None
    &&& post.it_mp.spec_index(iommu_table_page_ptr).view().cr3 == iommu_l4_page_ptr
    &&& post.it_mp.spec_index(iommu_table_page_ptr).view().kernel_l4_end == 0
    &&& post.it_mp.spec_index(iommu_table_page_ptr).view().is_empty()
    &&& post.it_mp.spec_index(iommu_table_page_ptr).view().page_closure() == set![iommu_l4_page_ptr]
    &&& post.prc_mp.dom() == pre.prc_mp.dom().insert(process_page_ptr)
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.dom().contains(p_ptr)]
        #![trigger post.prc_mp.spec_index(p_ptr)]
        post.prc_mp.dom().contains(p_ptr) && p_ptr != process_page_ptr ==> {
            &&& pre.prc_mp.dom().contains(p_ptr)
            &&& post.prc_mp.spec_index(p_ptr).is_init() == pre.prc_mp.spec_index(p_ptr).is_init()
            &&& post.prc_mp.spec_index(p_ptr).locking_thread() == pre.prc_mp.spec_index(p_ptr).locking_thread()
            &&& post.prc_mp.spec_index(p_ptr).being_killed() == pre.prc_mp.spec_index(p_ptr).being_killed()
            &&& post.prc_mp.spec_index(p_ptr).view_rodata() == pre.prc_mp.spec_index(p_ptr).view_rodata()
            &&& post.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq == pre.prc_mp.spec_index(p_ptr).view_ghost().uppertree_seq
            &&& post.prc_mp.spec_index(p_ptr).view() == if p_ptr == parent_ptr {
                Process {
                    children: post.prc_mp.spec_index(p_ptr).view().children,
                    ..pre.prc_mp.spec_index(p_ptr).view()
                }
            } else {
                pre.prc_mp.spec_index(p_ptr).view()
            }
        }
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.spec_index(process_page_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)]
        #![trigger post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set]
        post.prc_mp.spec_index(process_page_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr) ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view() == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view().insert(process_page_ptr)
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set]
        pre.prc_mp.dom().contains(p_ptr) && !post.prc_mp.spec_index(process_page_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr) ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.view().spec_index(p_ptr).is_init()]
        post.prc_mp.dom().contains(p_ptr) && p_ptr != process_page_ptr ==> {
            &&& post.prc_mp.view().spec_index(p_ptr).is_init()
            &&& post.prc_mp.view().spec_index(p_ptr).addr() == p_ptr
        }
    &&& post.prc_mp.view().spec_index(process_page_ptr).is_init()
    &&& post.prc_mp.view().spec_index(process_page_ptr).addr() == process_page_ptr
    &&& post.prc_mp.spec_index(parent_ptr).view().children.view() == pre.prc_mp.spec_index(parent_ptr).view().children.view().push(process_page_ptr)
    &&& !pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(post.prc_mp.spec_index(process_page_ptr).view().parent_linkedlist_node.addr(),)
    &&& post.prc_mp.spec_index(parent_ptr).view().children.map() == pre.prc_mp.spec_index(parent_ptr).view().children.map().insert(
            post.prc_mp.spec_index(process_page_ptr).view().parent_linkedlist_node.addr(), process_page_ptr,
        )
    &&& post.prc_mp.spec_index(process_page_ptr).is_init()
    &&& !post.prc_mp.spec_index(process_page_ptr).being_killed()
    &&& post.prc_mp.spec_index(process_page_ptr).wlocked()
    &&& !post.prc_mp.spec_index(process_page_ptr).view().zombie
    &&& post.prc_mp.spec_index(process_page_ptr).view().pcid == pcid
    &&& post.prc_mp.spec_index(process_page_ptr).view().pagetable == pagetable_page_ptr
    &&& post.prc_mp.spec_index(process_page_ptr).view().iommu_table == Some(iommu_table_page_ptr)
    &&& post.prc_mp.spec_index(process_page_ptr).view().pci_function_ref_counter == 0
    &&& post.prc_mp.spec_index(process_page_ptr).view().owned_pci_functions.view().is_empty()
    &&& post.prc_mp.spec_index(process_page_ptr).view().quota_4k == 0
    &&& post.prc_mp.spec_index(process_page_ptr).view().quota_2m == 0
    &&& post.prc_mp.spec_index(process_page_ptr).view().quota_1g == 0
    &&& !post.prc_mp.spec_index(process_page_ptr).view().parent_linkedlist_node.is_init()
    &&& post.prc_mp.spec_index(process_page_ptr).view().children.view() == Seq::<RwLockProcessPtr>::empty()
    &&& post.prc_mp.spec_index(process_page_ptr).view().owned_threads.view() == Seq::<RwLockThreadPtr>::empty()
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().owning_container == container_ptr
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().container_depth == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().parent == Some(parent_ptr)
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().depth == pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth + 1
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().pagetable == pagetable_page_ptr
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().cr3 == l4_page_ptr
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().pcid == pcid
    &&& post.prc_mp.spec_index(process_page_ptr).view_ghost().uppertree_seq.view() == ancestors
    &&& post.prc_mp.spec_index(process_page_ptr).view_ghost().subtree_set.view() == Set::<RwLockProcessPtr>::empty()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr)
    &&& post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view()
    &&& post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view() == pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().insert(process_page_ptr)
    &&& post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata()
    &&& post.ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
        owned_processes: post.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes, ..pre.ctn_mp.spec_index(container_ptr).view_ghost()
    })
    &&& post.ctn_mp.spec_index(container_ptr).locking_thread() == pre.ctn_mp.spec_index(container_ptr).locking_thread()
    &&& post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> post.ctn_mp.spec_index(c).view_ghost().owned_threads == pre.ctn_mp.spec_index(c).view_ghost().owned_threads
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger post.ctn_mp.view().spec_index(c_ptr).is_init()]
        pre.ctn_mp.dom().contains(c_ptr) ==> {
            &&& post.ctn_mp.view().spec_index(c_ptr).is_init() == pre.ctn_mp.view().spec_index(c_ptr).is_init()
            &&& post.ctn_mp.view().spec_index(c_ptr).addr() == pre.ctn_mp.view().spec_index(c_ptr).addr()
        }
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, staging_thread_ptr)
    &&& post.thr_mp.spec_index(staging_thread_ptr).view() == (Thread {
        quota_4k: post.thr_mp.spec_index(staging_thread_ptr).view().quota_4k,
        temp_alloc_cache_4k: post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k,
        ..pre.thr_mp.spec_index(staging_thread_ptr).view()
    })
    &&& post.thr_mp.spec_index(staging_thread_ptr).view().quota_4k == pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 5
    &&& post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().is_empty()
    &&& post.thr_mp.spec_index(staging_thread_ptr).locking_thread() == pre.thr_mp.spec_index(staging_thread_ptr).locking_thread()
    &&& post.thr_mp.spec_index(staging_thread_ptr).being_killed() == pre.thr_mp.spec_index(staging_thread_ptr).being_killed()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger post.thr_mp.view().spec_index(t_ptr).is_init()]
        pre.thr_mp.dom().contains(t_ptr) ==> {
            &&& post.thr_mp.view().spec_index(t_ptr).is_init() == pre.thr_mp.view().spec_index(t_ptr).is_init()
            &&& post.thr_mp.view().spec_index(t_ptr).addr() == pre.thr_mp.view().spec_index(t_ptr).addr()
        }
    &&& post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, pcid_allocator_ptr)
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().alloc_ensures(&pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view(), process_page_ptr, pcid,)
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread() == pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_ptr).being_killed() == pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).being_killed()
    &&& forall|a_ptr: RwLockPcidAllocatorPtr|
        #![trigger post.pcid_allc_mp.view().spec_index(a_ptr).is_init()]
        pre.pcid_allc_mp.dom().contains(a_ptr) ==> {
            &&& post.pcid_allc_mp.view().spec_index(a_ptr).is_init() == pre.pcid_allc_mp.view().spec_index(a_ptr).is_init()
            &&& post.pcid_allc_mp.view().spec_index(a_ptr).addr() == pre.pcid_allc_mp.view().spec_index(a_ptr).addr()
        }
}

#[verifier::spinoff_prover]
pub fn create_process_with_iommu_from_staged_pages(
    krnl: &mut KernelK, process_page_ptr: PagePtr, pagetable_page_ptr: PagePtr, l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr, iommu_l4_page_ptr: PagePtr, parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr, container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr, pcid: Pcid, Tracked(lctx): Tracked<&mut LocalContext>,
    Tracked(process_page_lock_perm): Tracked<&LockPerm>, Tracked(pagetable_page_lock_perm): Tracked<&LockPerm>,
    Tracked(l4_page_lock_perm): Tracked<&LockPerm>, Tracked(iommu_table_page_lock_perm): Tracked<&LockPerm>,
    Tracked(iommu_l4_page_lock_perm): Tracked<&LockPerm>, Tracked(parent_lock_perm): Tracked<&LockPerm>,
    Tracked(staging_thread_lock_perm): Tracked<&LockPerm>, Tracked(pcid_allocator_lock_perm): Tracked<&LockPerm>,
) -> (ret: (RwLockProcessPtr, RwLockPageTableRoot, RwLockPageTableRoot, Tracked<LockPerm>, Tracked<LockPerm>, Tracked<LockPerm>))
    requires
        old(krnl).inv(),
        old(lctx).kernel_view_locking_state() is Release,
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        page_ptr_valid(process_page_ptr),
        page_ptr_valid(pagetable_page_ptr),
        page_ptr_valid(l4_page_ptr),
        page_ptr_valid(iommu_table_page_ptr),
        page_ptr_valid(iommu_l4_page_ptr),
        index_valid(NUM_PAGES, page_ptr2page_index(process_page_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(pagetable_page_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(l4_page_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(iommu_table_page_ptr)),
        index_valid(NUM_PAGES, page_ptr2page_index(iommu_l4_page_ptr)),
        !old(krnl).prc_mp.dom().contains(process_page_ptr),
        !old(krnl).pt_mp.dom().contains(pagetable_page_ptr),
        !old(krnl).it_mp.dom().contains(iommu_table_page_ptr),
        process_page_ptr != pagetable_page_ptr,
        process_page_ptr != l4_page_ptr,
        pagetable_page_ptr != l4_page_ptr,
        process_page_ptr != iommu_table_page_ptr,
        process_page_ptr != iommu_l4_page_ptr,
        pagetable_page_ptr != iommu_table_page_ptr,
        pagetable_page_ptr != iommu_l4_page_ptr,
        l4_page_ptr != iommu_table_page_ptr,
        l4_page_ptr != iommu_l4_page_ptr,
        iommu_table_page_ptr != iommu_l4_page_ptr,
        old(krnl).ctn_mp.dom().contains(container_ptr),
        old(krnl).prc_mp.dom().contains(parent_ptr),
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().owning_container == container_ptr,
        old(krnl).prc_mp.spec_index(parent_ptr).view_rodata().view().depth < usize::MAX,
        typed_lock_map_contains_mode(old(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        !old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        parent_lock_perm.state() is WriteLock,
        parent_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_lock_perm.lock_id() == old(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        old(krnl).thr_mp.dom().contains(staging_thread_ptr),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        !old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k >= 5,
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view() =~= set![process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr],
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_2m.view().is_empty(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_1g.view().is_empty(),
        old(krnl).thr_mp.spec_index(staging_thread_ptr).view().free_quota_pending_clean(),
        staging_thread_lock_perm.state() is WriteLock,
        staging_thread_lock_perm.thread_id() == old(lctx).thread_id(),
        staging_thread_lock_perm.lock_id() == old(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        old(krnl).pcid_allc_mp.dom().contains(pcid_allocator_ptr),
        old(krnl).ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator == pcid_allocator_ptr,
        typed_lock_map_contains_mode(old(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).view().pcid_is_free(pcid),
        pcid_allocator_lock_perm.state() is WriteLock,
        pcid_allocator_lock_perm.thread_id() == old(lctx).thread_id(),
        pcid_allocator_lock_perm.lock_id() == old(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(process_page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(pagetable_page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(l4_page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(iommu_table_page_ptr), TypedLockMode::Write),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().state == (PageState::Owned4k { thread_ptr: staging_thread_ptr }),
        old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().view().owning_container == container_ptr,
        typed_lock_map_contains_mode(old(lctx).page_lock_map(), page_ptr2page_index(iommu_l4_page_ptr), TypedLockMode::Write),
        process_page_lock_perm.state() is WriteLock,
        process_page_lock_perm.thread_id() == old(lctx).thread_id(),
        process_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.state() is WriteLock,
        pagetable_page_lock_perm.thread_id() == old(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.state() is WriteLock,
        l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_table_page_lock_perm.state() is WriteLock,
        iommu_table_page_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_table_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_l4_page_lock_perm.state() is WriteLock,
        iommu_l4_page_lock_perm.thread_id() == old(lctx).thread_id(),
        iommu_l4_page_lock_perm.lock_id() == old(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().locking_thread()->Write_lock_id,
    ensures
        *final(krnl) == (KernelK {
            pg_arr: final(krnl).pg_arr, prc_mp: final(krnl).prc_mp, pt_mp: final(krnl).pt_mp, it_mp: final(krnl).it_mp,
            ctn_mp: final(krnl).ctn_mp, thr_mp: final(krnl).thr_mp, pcid_allc_mp: final(krnl).pcid_allc_mp, ..*old(krnl)
        }),
        final(krnl).prc_mp.dom() == old(krnl).prc_mp.dom().insert(process_page_ptr),
        final(krnl).prc_mp.spec_index(parent_ptr).view().owned_threads == old(krnl).prc_mp.spec_index(parent_ptr).view().owned_threads,
        final(krnl).prc_mp.spec_index(parent_ptr).being_killed() == old(krnl).prc_mp.spec_index(parent_ptr).being_killed(),
        !final(krnl).prc_mp.spec_index(process_page_ptr).being_killed(),
        !final(krnl).prc_mp.spec_index(process_page_ptr).view().zombie,
        final(krnl).prc_mp.spec_index(process_page_ptr).view_rodata().view().owning_container == container_ptr,
        final(krnl).prc_mp.spec_index(process_page_ptr).view_rodata().view().pagetable == pagetable_page_ptr,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().iommu_table == Some(iommu_table_page_ptr),
        final(krnl).pt_mp.dom() == old(krnl).pt_mp.dom().insert(pagetable_page_ptr),
        forall|pt: RwLockPageTableRoot| #![trigger final(krnl).pt_mp.spec_index(pt)]
            old(krnl).pt_mp.dom().contains(pt) ==> final(krnl).pt_mp.spec_index(pt) == old(krnl).pt_mp.spec_index(pt),
        final(krnl).pt_mp.spec_index(pagetable_page_ptr).view().is_empty(),
        final(krnl).pt_mp.spec_index(pagetable_page_ptr).view().proc_ptr == process_page_ptr,
        final(krnl).prc_mp.spec_index(process_page_ptr).view().pagetable == pagetable_page_ptr,
        final(krnl).ctn_mp.dom() == old(krnl).ctn_mp.dom(),
        final(krnl).ctn_mp.spec_index(container_ptr).view_rodata() == old(krnl).ctn_mp.spec_index(container_ptr).view_rodata(),
        final(krnl).ctn_mp.spec_index(container_ptr).being_killed() == old(krnl).ctn_mp.spec_index(container_ptr).being_killed(),
        final(krnl).thr_mp.dom() == old(krnl).thr_mp.dom(),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).view() == (Thread {
            quota_4k: (old(krnl).thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 5) as usize,
            temp_alloc_cache_4k: Ghost(Set::empty()), ..old(krnl).thr_mp.spec_index(staging_thread_ptr).view()
        }),
        final(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed() == old(krnl).thr_mp.spec_index(staging_thread_ptr).being_killed(),
        final(krnl).pcid_allc_mp.dom() == old(krnl).pcid_allc_mp.dom(),
        final(krnl).it_mp.dom() == old(krnl).it_mp.dom().insert(iommu_table_page_ptr),
        final(krnl).it_mp.spec_index(iommu_table_page_ptr).view().is_empty(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(krnl).inv(),
        kernel_u_create_process_with_iommu_changed(kernel_k_to_nonlock_kernel_u(*old(krnl)), kernel_k_to_nonlock_kernel_u(*final(krnl)), parent_ptr, process_page_ptr, staging_thread_ptr,),
        kernel_k_to_nonlock_kernel_u(*final(krnl)) != kernel_k_to_nonlock_kernel_u(*old(krnl)),
        ret.0 == process_page_ptr,
        ret.1 == pagetable_page_ptr,
        ret.2 == iommu_table_page_ptr,
        create_process_with_iommu_from_staged_pages_kernel_state_framing(
            *old(krnl), *final(krnl), process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr,
            parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        ),
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), process_page_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).pagetable_lock_map(), pagetable_page_ptr, TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).iommu_table_lock_map(), iommu_table_page_ptr, TypedLockMode::Write),
        ret.3.view().state() is WriteLock,
        ret.3.view().thread_id() == final(lctx).thread_id(),
        ret.3.view().lock_id() == final(krnl).prc_mp.spec_index(process_page_ptr).locking_thread()->Write_lock_id,
        ret.4.view().state() is WriteLock,
        ret.4.view().thread_id() == final(lctx).thread_id(),
        ret.4.view().lock_id() == final(krnl).pt_mp.spec_index(pagetable_page_ptr).locking_thread()->Write_lock_id,
        ret.5.view().state() is WriteLock,
        ret.5.view().thread_id() == final(lctx).thread_id(),
        ret.5.view().lock_id() == final(krnl).it_mp.spec_index(iommu_table_page_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).thread_lock_map(), staging_thread_ptr, TypedLockMode::Write),
        staging_thread_lock_perm.lock_id() == final(krnl).thr_mp.spec_index(staging_thread_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).process_lock_map(), parent_ptr, TypedLockMode::Write),
        parent_lock_perm.lock_id() == final(krnl).prc_mp.spec_index(parent_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).pcid_allocator_lock_map(), pcid_allocator_ptr, TypedLockMode::Write),
        pcid_allocator_lock_perm.lock_id() == final(krnl).pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()->Write_lock_id,
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(process_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(pagetable_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(l4_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(iommu_table_page_ptr), TypedLockMode::Write),
        typed_lock_map_contains_mode(final(lctx).page_lock_map(), page_ptr2page_index(iommu_l4_page_ptr), TypedLockMode::Write),
        process_page_lock_perm.thread_id() == final(lctx).thread_id(),
        process_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(process_page_ptr)).view().locking_thread()->Write_lock_id,
        pagetable_page_lock_perm.thread_id() == final(lctx).thread_id(),
        pagetable_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(pagetable_page_ptr)).view().locking_thread()->Write_lock_id,
        l4_page_lock_perm.thread_id() == final(lctx).thread_id(),
        l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(l4_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_table_page_lock_perm.thread_id() == final(lctx).thread_id(),
        iommu_table_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_table_page_ptr)).view().locking_thread()->Write_lock_id,
        iommu_l4_page_lock_perm.thread_id() == final(lctx).thread_id(),
        iommu_l4_page_lock_perm.lock_id() == final(krnl).pg_arr.spec_index(page_ptr2page_index(iommu_l4_page_ptr)).view().locking_thread()->Write_lock_id,
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).cpu_offline_flag_lock_map() == old(lctx).cpu_offline_flag_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).cpu_set_lock_map() == old(lctx).cpu_set_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        final(lctx).kernel_view_locking_state() is Release,
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).process_lock_map() == old(lctx).process_lock_map().insert(process_page_ptr, TypedHeldLock {
            lock_id: final(krnl).prc_mp.lock_id_by_key(process_page_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map().insert(pagetable_page_ptr, TypedHeldLock {
            lock_id: final(krnl).pt_mp.lock_id_by_key(pagetable_page_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map().insert(iommu_table_page_ptr, TypedHeldLock {
            lock_id: final(krnl).it_mp.lock_id_by_key(iommu_table_page_ptr), mode: TypedLockMode::Write,
        }),
        final(lctx).page_lock_map() == old(lctx).page_lock_map().insert(page_ptr2page_index(l4_page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l4_page_ptr)), mode: TypedLockMode::Write,
            }).insert(page_ptr2page_index(pagetable_page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pagetable_page_ptr)), mode: TypedLockMode::Write,
            }).insert(page_ptr2page_index(iommu_l4_page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(iommu_l4_page_ptr)), mode: TypedLockMode::Write,
            }).insert(page_ptr2page_index(iommu_table_page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(iommu_table_page_ptr)), mode: TypedLockMode::Write,
            }).insert(page_ptr2page_index(process_page_ptr), TypedHeldLock {
                lock_id: final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(process_page_ptr)), mode: TypedLockMode::Write,
            }),
        final(krnl).prc_mp.lock_id_by_key(process_page_ptr).major == PROCESS_LOCK_MAJOR,
        final(krnl).pt_mp.lock_id_by_key(pagetable_page_ptr).major == PAGE_TABLE_LOCK_MAJOR,
        final(krnl).it_mp.lock_id_by_key(iommu_table_page_ptr).major == IOMMU_TABLE_LOCK_MAJOR,
        final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(l4_page_ptr)).major < MAPPED_PAGE_LOCK_MAJOR,
        final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(pagetable_page_ptr)).major < MAPPED_PAGE_LOCK_MAJOR,
        final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(process_page_ptr)).major < MAPPED_PAGE_LOCK_MAJOR,
        final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(iommu_l4_page_ptr)).major < MAPPED_PAGE_LOCK_MAJOR,
        final(krnl).pg_arr.lock_id_by_index(page_ptr2page_index(iommu_table_page_ptr)).major < MAPPED_PAGE_LOCK_MAJOR,
{
    let process_page_index = page_ptr2page_index(process_page_ptr);
    let pagetable_page_index = page_ptr2page_index(pagetable_page_ptr);
    let l4_page_index = page_ptr2page_index(l4_page_ptr);
    let iommu_table_page_index = page_ptr2page_index(iommu_table_page_ptr);
    let iommu_l4_page_index = page_ptr2page_index(iommu_l4_page_ptr);
    proof {
        assert({
            &&& process_page_ptr == page_index2page_ptr(process_page_index)
            &&& pagetable_page_ptr == page_index2page_ptr(pagetable_page_index)
            &&& l4_page_ptr == page_index2page_ptr(l4_page_index)
            &&& iommu_table_page_ptr == page_index2page_ptr(iommu_table_page_index)
            &&& iommu_l4_page_ptr == page_index2page_ptr(iommu_l4_page_index)
        }) by { page_ptr_roundtrip(); };
        assert(krnl.pg_arr.inv()) by { reveal(page_array_wf); };
        assert(krnl.pt_mp.perms_wf()) by { reveal(pagetable_perms_wf); };
        assert(krnl.it_mp.perms_wf()) by { reveal(iommu_table_perms_wf); };
        assert(krnl.prc_mp.perms_wf() && krnl.prc_mp.view().spec_index(parent_ptr).is_init() && krnl.prc_mp.view().spec_index(parent_ptr).addr() == parent_ptr && krnl.prc_mp.spec_index(parent_ptr).inv()) by { process_perms_wf_at(krnl.prc_mp, parent_ptr); };
        assert(krnl.ctn_mp.perms_wf() && krnl.ctn_mp.view().spec_index(container_ptr).is_init() && krnl.ctn_mp.view().spec_index(container_ptr).addr() == container_ptr && krnl.ctn_mp.spec_index(container_ptr).inv()) by { container_perms_wf_at(krnl.ctn_mp, container_ptr); };
        assert(krnl.pcid_allc_mp.perms_wf() && krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).inv()) by { pcid_allocator_perms_wf_at(krnl.pcid_allc_mp, pcid_allocator_ptr); };
        assert(krnl.thr_mp.perms_wf() && krnl.thr_mp.spec_index(staging_thread_ptr).is_init() && krnl.thr_mp.spec_index(staging_thread_ptr).inv()) by { thread_perms_wf_at(krnl.thr_mp, staging_thread_ptr); };
        assert(krnl.pg_arr.spec_index(l4_page_index).view().is_init() && krnl.pg_arr.spec_index(l4_page_index).view().view().inv() && krnl.pg_arr.spec_index(l4_page_index).view().view().addr == l4_page_ptr && krnl.pg_arr.spec_index(l4_page_index).view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(pagetable_page_index).view().is_init() && krnl.pg_arr.spec_index(pagetable_page_index).view().view().inv() && krnl.pg_arr.spec_index(pagetable_page_index).view().view().addr == pagetable_page_ptr && krnl.pg_arr.spec_index(pagetable_page_index).view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(process_page_index).view().is_init() && krnl.pg_arr.spec_index(process_page_index).view().view().inv() && krnl.pg_arr.spec_index(process_page_index).view().view().addr == process_page_ptr && krnl.pg_arr.spec_index(process_page_index).view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(iommu_table_page_index).view().is_init() && krnl.pg_arr.spec_index(iommu_table_page_index).view().view().inv() && krnl.pg_arr.spec_index(iommu_table_page_index).view().view().addr == iommu_table_page_ptr && krnl.pg_arr.spec_index(iommu_table_page_index).view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(krnl.pg_arr.spec_index(iommu_l4_page_index).view().is_init() && krnl.pg_arr.spec_index(iommu_l4_page_index).view().view().inv() && krnl.pg_arr.spec_index(iommu_l4_page_index).view().view().addr == iommu_l4_page_ptr && krnl.pg_arr.spec_index(iommu_l4_page_index).view().view().perm_4k.view().is_some()
        ) by { reveal(page_array_wf); };
        assert(krnl.dflt_pt.view().wf()) by { reveal(KernelK::default_pagetable_wf); };
        assert(pei_valid(krnl.dflt_pt.view().kernel_l4_end)) by { reveal(PageTable::kernel_entries_wf); };
    }
    let ghost parent_ancestors =
        krnl.prc_mp.spec_index(parent_ptr).view_ghost().uppertree_seq.view();
    let ghost ancestors = parent_ancestors.push(parent_ptr);
    let ghost parent_children =
        krnl.prc_mp.spec_index(parent_ptr).view().children.view();
    proof {
        let process_tree_dom =
            krnl.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view();
        let root_process =
            krnl.ctn_mp.spec_index(container_ptr).view().root_process;
        assert(process_tree_dom.contains(parent_ptr)) by { reveal(container_process_wf); };
        assert(process_tree_wf(
            root_process, process_tree_dom, krnl.prc_mp,
        )) by { reveal(per_container_process_tree_wf); };
        assert(process_tree_dom.subset_of(krnl.prc_mp.dom())) by { reveal(container_process_wf); };
        assert(parent_ancestors.to_set().subset_of(process_tree_dom)) by { parent_ancestors.to_set_ensures(); reveal(process_uppertree_seq_wf); };
        assert(ancestors.to_set().subset_of(process_tree_dom)) by { parent_ancestors.to_set_ensures(); ancestors.to_set_ensures(); };
        assert(parent_ancestors.no_duplicates()) by { process_perms_wf_at(krnl.prc_mp, parent_ptr); };
        assert(!parent_ancestors.contains(parent_ptr)) by { reveal(process_uppertree_seq_wf); };
        seq_push_unique_lemma::<RwLockProcessPtr>();
        assert(!krnl.prc_mp.spec_index(parent_ptr).view().children.view().contains(process_page_ptr)) by { reveal(process_children_parent_wf); };
        assert(parent_children.len() <= NUM_PAGES) by {
            assert(parent_children.no_duplicates()) by { process_perms_wf_at(krnl.prc_mp, parent_ptr); };
            reveal(process_children_parent_wf);
            lemma_kernel_object_ptr_seq_len_bounded(&*krnl, parent_children);
        };
        assert(krnl.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().process_is_unallocated(process_page_ptr)) by { reveal(process_pcid_allocator_wf); };
    }
    let Tracked(l4_page_perm) = page_array_retype_owned_4k(
        &mut krnl.pg_arr, l4_page_index, PageState::Allocated4k { state: Allocated4KPageState::PageTable { pagetable_root: pagetable_page_ptr } },
        Tracked(&mut *lctx), Tracked(l4_page_lock_perm),
    );
    let (l4_ptr, Tracked(mut l4_perm)) = page_perm_to_page_map(l4_page_ptr, Tracked(l4_page_perm));
    let default_pt = krnl.dflt_pt.borrow();
    default_pt.copy_kernel_entries_to_unpublished_root(l4_ptr, Tracked(&mut l4_perm));
    proof { assert(default_pt.kernel_entries.view().len() == default_pt.kernel_l4_end) by { reveal(PageTable::kernel_entries_wf); }; }
    let pagetable_value = PageTable::<PT_TYPE>::new(Some(pcid), Ghost(default_pt.kernel_entries.view()), l4_ptr, Tracked(l4_perm), default_pt.kernel_l4_end, process_page_ptr);

    let Tracked(pagetable_page_perm) = page_array_retype_owned_4k(
        &mut krnl.pg_arr, pagetable_page_index, PageState::Allocated4k { state: Allocated4KPageState::AsPageTableRoot },
        Tracked(&mut *lctx), Tracked(pagetable_page_lock_perm),
    );
    let Tracked(pagetable_lock_perm) = krnl.retype_page_to_pagetable_and_insert(pagetable_page_ptr, pagetable_value, Tracked(pagetable_page_perm), Tracked(&mut *lctx));

    let Tracked(iommu_l4_page_perm) = page_array_retype_owned_4k(
        &mut krnl.pg_arr, iommu_l4_page_index, PageState::IOMMUTable { iommu_table_root: iommu_table_page_ptr },
        Tracked(&mut *lctx), Tracked(iommu_l4_page_lock_perm),
    );
    let (iommu_l4_ptr, Tracked(iommu_l4_perm)) = page_perm_to_page_map(iommu_l4_page_ptr, Tracked(iommu_l4_page_perm));
    let iommu_table_value = PageTable::<IOMMU_TYPE>::new(None, Ghost(Seq::empty()), iommu_l4_ptr, Tracked(iommu_l4_perm), 0, process_page_ptr);

    let Tracked(iommu_table_page_perm) = page_array_retype_owned_4k(
        &mut krnl.pg_arr, iommu_table_page_index, PageState::Allocated4k { state: Allocated4KPageState::AsIommuTableRoot },
        Tracked(&mut *lctx), Tracked(iommu_table_page_lock_perm),
    );
    let Tracked(iommu_table_lock_perm) = krnl.retype_page_to_iommu_table_and_insert(iommu_table_page_ptr, iommu_table_value, Tracked(iommu_table_page_perm), Tracked(&mut *lctx));

    let parent_depth = krnl.prc_mp.borrow_rodata(parent_ptr).borrow().depth;
    let cr3 = l4_ptr;
    let mut process_value = Process::new_fresh(process_page_ptr, pcid, pagetable_page_ptr, krnl.ctn_mp.borrow_rodata(container_ptr).borrow().depth, parent_depth + 1);
    process_value.iommu_table = Some(iommu_table_page_ptr);
    let process_rodata = ReadOnlyNode::new(ProcessRO { owning_container: container_ptr, container_depth: krnl.ctn_mp.borrow_rodata(container_ptr).borrow().depth, parent: Some(parent_ptr), depth: parent_depth + 1, pagetable: pagetable_page_ptr, cr3, pcid }, Ghost(process_page_ptr));
    let process_ghost = ProcessGhost { uppertree_seq: Ghost(ancestors), subtree_set: Ghost(Set::empty()) };
    proof {
        assert(parent_ancestors.len() == parent_depth) by { process_perms_wf_at(krnl.prc_mp, parent_ptr); };
        assert(ancestors.len() == process_rodata.view().depth) by { seq_push_lemma::<RwLockProcessPtr>(); };
    }
    let Tracked(process_page_perm) = page_array_retype_owned_4k(
        &mut krnl.pg_arr, process_page_index, PageState::Allocated4k { state: Allocated4KPageState::AsProcess },
        Tracked(&mut *lctx), Tracked(process_page_lock_perm),
    );
    let Tracked(process_lock_perm) = krnl.retype_page_to_process_and_insert(process_page_ptr, process_value, process_rodata, process_ghost, Tracked(process_page_perm), Tracked(&mut *lctx));

    process_map_link_new_child(&mut krnl.prc_mp, parent_ptr, process_page_ptr, Ghost(ancestors), Tracked(&*lctx), Tracked(parent_lock_perm), Tracked(&process_lock_perm));
    proof { container_map_add_owned_process(&mut krnl.ctn_mp, container_ptr, process_page_ptr, lctx.container_lock_map(), lctx.thread_id()); }
    pcid_allocator_map_alloc(&mut krnl.pcid_allc_mp, pcid_allocator_ptr, process_page_ptr, pcid, Tracked(&*lctx), Tracked(pcid_allocator_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thr_mp, staging_thread_ptr, process_page_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thr_mp, staging_thread_ptr, pagetable_page_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thr_mp, staging_thread_ptr, l4_page_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thr_mp, staging_thread_ptr, iommu_table_page_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));
    thread_map_consume_staged_4k(&mut krnl.thr_mp, staging_thread_ptr, iommu_l4_page_ptr, Tracked(&*lctx), Tracked(staging_thread_lock_perm));

    proof {
        assert(create_process_with_iommu_from_staged_pages_kernel_state_framing(
            *old(krnl), *krnl, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr,
            parent_ptr, staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        )) by { reveal(create_process_with_iommu_from_staged_pages_kernel_state_framing); ancestors.to_set_ensures(); };
    }
    proof {
        eof_inv(
            *old(krnl), *krnl, process_page_ptr, pagetable_page_ptr, l4_page_ptr, iommu_table_page_ptr, iommu_l4_page_ptr, parent_ptr,
            staging_thread_ptr, container_ptr, pcid_allocator_ptr, pcid,
        );
    }
    (process_page_ptr, pagetable_page_ptr, iommu_table_page_ptr, Tracked(process_lock_perm), Tracked(pagetable_lock_perm), Tracked(iommu_table_lock_perm))
}
}
