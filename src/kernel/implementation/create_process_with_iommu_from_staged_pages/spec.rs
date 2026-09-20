use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use crate::*;
use super::*;

verus! {
/// User-view change predicate for publishing a process with empty CPU and IOMMU page tables.
pub open spec fn kernel_u_create_process_with_iommu_changed(
    old_u: KernelU,
    new_u: KernelU,
    parent_ptr: RwLockProcessPtr,
    child_ptr: RwLockProcessPtr,
) -> bool {
    let child = new_u.process_map.spec_index(child_ptr);
    &&& new_u.cpu_array == old_u.cpu_array
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

pub open spec fn create_process_with_iommu_from_staged_pages_kernel_state_framing(
    pre: KernelK,
    post: KernelK,
    process_page_ptr: PagePtr,
    pagetable_page_ptr: PagePtr,
    l4_page_ptr: PagePtr,
    iommu_table_page_ptr: PagePtr,
    iommu_l4_page_ptr: PagePtr,
    parent_ptr: RwLockProcessPtr,
    staging_thread_ptr: RwLockThreadPtr,
    container_ptr: RwLockContainerPtr,
    pcid_allocator_ptr: RwLockPcidAllocatorPtr,
    pcid: Pcid,
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
    &&& post.cpu_tlb == pre.cpu_tlb
    &&& post.iommu_tlb == pre.iommu_tlb
    &&& post.rt_ctn == pre.rt_ctn
    &&& post.dflt_pt == pre.dflt_pt
    &&& forall|index: PageIndex|
        #![trigger post.pg_arr.spec_index(index)]
        #![trigger pre.pg_arr.spec_index(index)]
        index_valid(NUM_PAGES, index)
            && index != process_page_index
            && index != pagetable_page_index
            && index != l4_page_index
            && index != iommu_table_page_index
            && index != iommu_l4_page_index
        ==> post.pg_arr.spec_index(index) == pre.pg_arr.spec_index(index)
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
        post.pt_mp.dom().contains(pt_ptr)
            && pt_ptr != pagetable_page_ptr
        ==> {
            &&& pre.pt_mp.dom().contains(pt_ptr)
            &&& post.pt_mp.spec_index(pt_ptr) == pre.pt_mp.spec_index(pt_ptr)
        }
    &&& forall|pt_ptr: RwLockPageTableRoot|
        #![trigger post.pt_mp.view().spec_index(pt_ptr).is_init()]
        post.pt_mp.dom().contains(pt_ptr)
            && pt_ptr != pagetable_page_ptr
        ==> {
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
        post.it_mp.dom().contains(it_ptr)
            && it_ptr != iommu_table_page_ptr
        ==> {
            &&& pre.it_mp.dom().contains(it_ptr)
            &&& post.it_mp.spec_index(it_ptr) == pre.it_mp.spec_index(it_ptr)
        }
    &&& forall|it_ptr: RwLockPageTableRoot|
        #![trigger post.it_mp.view().spec_index(it_ptr).is_init()]
        post.it_mp.dom().contains(it_ptr)
            && it_ptr != iommu_table_page_ptr
        ==> {
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
        post.prc_mp.dom().contains(p_ptr)
            && p_ptr != process_page_ptr
        ==> {
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
        post.prc_mp.spec_index(process_page_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
        ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view()
            == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set.view().insert(process_page_ptr)
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set]
        pre.prc_mp.dom().contains(p_ptr)
            && !post.prc_mp.spec_index(process_page_ptr).view_ghost().uppertree_seq.view().to_set().contains(p_ptr)
        ==> post.prc_mp.spec_index(p_ptr).view_ghost().subtree_set
            == pre.prc_mp.spec_index(p_ptr).view_ghost().subtree_set
    &&& forall|p_ptr: RwLockProcessPtr|
        #![trigger post.prc_mp.view().spec_index(p_ptr).is_init()]
        post.prc_mp.dom().contains(p_ptr)
            && p_ptr != process_page_ptr
        ==> {
            &&& post.prc_mp.view().spec_index(p_ptr).is_init()
            &&& post.prc_mp.view().spec_index(p_ptr).addr() == p_ptr
        }
    &&& post.prc_mp.view().spec_index(process_page_ptr).is_init()
    &&& post.prc_mp.view().spec_index(process_page_ptr).addr() == process_page_ptr
    &&& post.prc_mp.spec_index(parent_ptr).view().children.view()
        == pre.prc_mp.spec_index(parent_ptr).view().children.view().push(process_page_ptr)
    &&& !pre.prc_mp.spec_index(parent_ptr).view().children.map().dom().contains(
        post.prc_mp.spec_index(process_page_ptr).view().parent_linkedlist_node.addr(),
    )
    &&& post.prc_mp.spec_index(parent_ptr).view().children.map()
        == pre.prc_mp.spec_index(parent_ptr).view().children.map().insert(
            post.prc_mp.spec_index(process_page_ptr).view().parent_linkedlist_node.addr(),
            process_page_ptr,
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
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().container_depth
        == pre.ctn_mp.spec_index(container_ptr).view_rodata().view().depth
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().parent == Some(parent_ptr)
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().depth
        == pre.prc_mp.spec_index(parent_ptr).view_rodata().view().depth + 1
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().pagetable == pagetable_page_ptr
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().cr3 == l4_page_ptr
    &&& post.prc_mp.spec_index(process_page_ptr).view_rodata().view().pcid == pcid
    &&& post.prc_mp.spec_index(process_page_ptr).view_ghost().uppertree_seq.view() == ancestors
    &&& post.prc_mp.spec_index(process_page_ptr).view_ghost().subtree_set.view() == Set::<RwLockProcessPtr>::empty()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr)
    &&& post.ctn_mp.spec_index(container_ptr).view() == (Container {
        owned_processes: post.ctn_mp.spec_index(container_ptr).view().owned_processes,
        ..pre.ctn_mp.spec_index(container_ptr).view()
    })
    &&& post.ctn_mp.spec_index(container_ptr).view().owned_processes.view()
        == pre.ctn_mp.spec_index(container_ptr).view().owned_processes.view().insert(process_page_ptr)
    &&& post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata()
    &&& post.ctn_mp.spec_index(container_ptr).view_ghost() == pre.ctn_mp.spec_index(container_ptr).view_ghost()
    &&& post.ctn_mp.spec_index(container_ptr).locking_thread() == pre.ctn_mp.spec_index(container_ptr).locking_thread()
    &&& post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed()
    &&& forall|c_ptr: RwLockContainerPtr|
        #![trigger post.ctn_mp.view().spec_index(c_ptr).is_init()]
        pre.ctn_mp.dom().contains(c_ptr)
        ==> {
            &&& post.ctn_mp.view().spec_index(c_ptr).is_init()
                == pre.ctn_mp.view().spec_index(c_ptr).is_init()
            &&& post.ctn_mp.view().spec_index(c_ptr).addr()
                == pre.ctn_mp.view().spec_index(c_ptr).addr()
        }
    &&& post.thr_mp.unchanged_except(&pre.thr_mp, staging_thread_ptr)
    &&& post.thr_mp.spec_index(staging_thread_ptr).view() == (Thread {
        quota_4k: post.thr_mp.spec_index(staging_thread_ptr).view().quota_4k,
        temp_alloc_cache_4k: post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k,
        ..pre.thr_mp.spec_index(staging_thread_ptr).view()
    })
    &&& post.thr_mp.spec_index(staging_thread_ptr).view().quota_4k
        == pre.thr_mp.spec_index(staging_thread_ptr).view().quota_4k - 5
    &&& post.thr_mp.spec_index(staging_thread_ptr).view().temp_alloc_cache_4k.view().is_empty()
    &&& post.thr_mp.spec_index(staging_thread_ptr).locking_thread() == pre.thr_mp.spec_index(staging_thread_ptr).locking_thread()
    &&& post.thr_mp.spec_index(staging_thread_ptr).being_killed() == pre.thr_mp.spec_index(staging_thread_ptr).being_killed()
    &&& forall|t_ptr: RwLockThreadPtr|
        #![trigger post.thr_mp.view().spec_index(t_ptr).is_init()]
        pre.thr_mp.dom().contains(t_ptr)
        ==> {
            &&& post.thr_mp.view().spec_index(t_ptr).is_init()
                == pre.thr_mp.view().spec_index(t_ptr).is_init()
            &&& post.thr_mp.view().spec_index(t_ptr).addr()
                == pre.thr_mp.view().spec_index(t_ptr).addr()
        }
    &&& post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, pcid_allocator_ptr)
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_ptr).view().alloc_ensures(
        &pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).view(),
        process_page_ptr,
        pcid,
    )
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread() == pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).locking_thread()
    &&& post.pcid_allc_mp.spec_index(pcid_allocator_ptr).being_killed() == pre.pcid_allc_mp.spec_index(pcid_allocator_ptr).being_killed()
    &&& forall|a_ptr: RwLockPcidAllocatorPtr|
        #![trigger post.pcid_allc_mp.view().spec_index(a_ptr).is_init()]
        pre.pcid_allc_mp.dom().contains(a_ptr)
        ==> {
            &&& post.pcid_allc_mp.view().spec_index(a_ptr).is_init()
                == pre.pcid_allc_mp.view().spec_index(a_ptr).is_init()
            &&& post.pcid_allc_mp.view().spec_index(a_ptr).addr()
                == pre.pcid_allc_mp.view().spec_index(a_ptr).addr()
        }
}


}
