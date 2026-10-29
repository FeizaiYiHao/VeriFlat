use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_spec::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof_entry::kill_container_retire_eof_target_empty;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof_tree::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_container_retire_eof_pages::*;

verus! {
/// Retiring the childless marked container `container_ptr` from `pre` to `post`: it leaves the container map, its parent
/// `parent_ptr`'s children, and every ancestor's subtree; its scheduler, cpu set, offline request table, PCID
/// allocator, and allocators leave their maps; its five 4K object pages join the 4K global pool and its container and
/// PCID allocator 2M pages the 2M global pool of `owner_ptr`, which owns them, their tails, and every page the
/// container owned. Quotas and every other object keep their values.
#[verifier::opaque]
pub(crate) open spec fn kill_container_retire_eof_transition_framing(
    pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr,
) -> bool {
    let target = pre.ctn_mp.spec_index(container_ptr);
    let ro = target.view_rodata().view();
    let owner_ro = pre.ctn_mp.spec_index(owner_ptr).view_rodata().view();
    let pages_4k = kill_container_retire_pages_4k(ro);
    let heads = kill_container_retire_heads(container_ptr, ro);
    let tails = kill_container_retire_tails(heads);
    &&& post == (KernelK { ctn_mp: post.ctn_mp, sched_mp: post.sched_mp, cpu_set_mp: post.cpu_set_mp, pcid_allc_mp: post.pcid_allc_mp, cpu_offline_mp: post.cpu_offline_mp,
        allc_4k_mp: post.allc_4k_mp, allc_2m_mp: post.allc_2m_mp, allc_1g_mp: post.allc_1g_mp, pg_arr: post.pg_arr, ..pre })
    &&& post.ctn_mp.perms_wf()
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom().remove(container_ptr)
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] post.ctn_mp.dom().contains(c) ==> {
        let old_c = pre.ctn_mp.spec_index(c);
        let new_c = post.ctn_mp.spec_index(c);
        &&& new_c.is_init() == old_c.is_init()
        &&& new_c.view_rodata() == old_c.view_rodata()
        &&& new_c.locking_thread() == old_c.locking_thread()
        &&& new_c.killer_info() == old_c.killer_info()
        &&& new_c.control() == old_c.control()
        &&& post.ctn_mp.lock_id_by_key(c) == pre.ctn_mp.lock_id_by_key(c)
        &&& new_c.view() == (Container { children: new_c.view().children, owned_pages: new_c.view().owned_pages, ..old_c.view() })
        &&& c != parent_ptr ==> new_c.view().children == old_c.view().children
        &&& new_c.view().owned_pages.view() == if c == owner_ptr { old_c.view().owned_pages.view().union(target.view().owned_pages.view()) } else { old_c.view().owned_pages.view() }
        &&& new_c.view_ghost() == (ContainerGhost { subtree_set: new_c.view_ghost().subtree_set, ..old_c.view_ghost() })
        &&& new_c.view_ghost().subtree_set.view()
            == if target.view_ghost().uppertree_seq.view().contains(c) { old_c.view_ghost().subtree_set.view().remove(container_ptr) } else { old_c.view_ghost().subtree_set.view() }
    }
    &&& post.ctn_mp.spec_index(parent_ptr).view().children.view() == pre.ctn_mp.spec_index(parent_ptr).view().children.view().remove_value(container_ptr)
    &&& post.ctn_mp.spec_index(parent_ptr).view().children.map() == pre.ctn_mp.spec_index(parent_ptr).view().children.map().remove(target.view().parent_linkedlist_node.addr())
    &&& post.sched_mp.perms_wf()
    &&& post.sched_mp.dom() == pre.sched_mp.dom().remove(ro.scheduler)
    &&& forall|s: RwLockSchedulerPtr| #![trigger post.sched_mp.spec_index(s)] post.sched_mp.dom().contains(s) ==> post.sched_mp.spec_index(s) == pre.sched_mp.spec_index(s)
    &&& post.cpu_set_mp.perms_wf()
    &&& post.cpu_set_mp.dom() == pre.cpu_set_mp.dom().remove(ro.cpu_set)
    &&& forall|s: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.spec_index(s)] post.cpu_set_mp.dom().contains(s) ==> post.cpu_set_mp.spec_index(s) == pre.cpu_set_mp.spec_index(s)
    &&& forall|s: RwLockCpuSetPtr| #![trigger post.cpu_set_mp.lock_id_by_key(s)] post.cpu_set_mp.dom().contains(s) ==> post.cpu_set_mp.lock_id_by_key(s) == pre.cpu_set_mp.lock_id_by_key(s)
    &&& post.pcid_allc_mp.perms_wf()
    &&& post.pcid_allc_mp.dom() == pre.pcid_allc_mp.dom().remove(ro.pcid_allocator)
    &&& forall|a: RwLockPcidAllocatorPtr| #![trigger post.pcid_allc_mp.spec_index(a)] post.pcid_allc_mp.dom().contains(a) ==> post.pcid_allc_mp.spec_index(a) == pre.pcid_allc_mp.spec_index(a)
    &&& post.cpu_offline_mp.perms_wf()
    &&& post.cpu_offline_mp.dom() == pre.cpu_offline_mp.dom().remove(cpu_offline_flags_ptr(container_ptr))
    &&& forall|f: RwLockCpuOfflineFlagsPtr| #![trigger post.cpu_offline_mp.spec_index(f)]
        post.cpu_offline_mp.dom().contains(f) ==> post.cpu_offline_mp.spec_index(f) == pre.cpu_offline_mp.spec_index(f)
    &&& post.allc_4k_mp.perms_wf()
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom().remove(ro.allocator_ptr_4k)
    &&& forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_4k_mp.spec_index(a)]
        post.allc_4k_mp.dom().contains(a) && a != owner_ro.allocator_ptr_4k ==> post.allc_4k_mp.spec_index(a) == pre.allc_4k_mp.spec_index(a)
    &&& ({
        let pre_allocator = pre.allc_4k_mp.spec_index(owner_ro.allocator_ptr_4k);
        let post_allocator = post.allc_4k_mp.spec_index(owner_ro.allocator_ptr_4k);
        let pre_pool = pre_allocator.global_pool.view();
        let post_pool = post_allocator.global_pool.view();
        &&& post_allocator.wf()
        &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + 5
        &&& post_allocator.quota.view() == (AllocatorQuota { value: (pre_allocator.quota.view().value + 5) as usize, ..pre_allocator.quota.view() })
        &&& post_allocator.quota.locking_thread() == pre_allocator.quota.locking_thread()
        &&& post_allocator.quota.is_init()
        &&& post_pool.view().len() == pre_pool.view().len() + 5
        &&& forall|p: PagePtr| #![trigger post_pool.view().contains(p)] post_pool.view().contains(p) == (pre_pool.view().contains(p) || pages_4k.contains(page_ptr2page_index(p)) && page_ptr_valid(p))
        &&& forall|a: usize| #![trigger pre_pool.map().dom().contains(a)] pre_pool.map().dom().contains(a) ==> post_pool.map().dom().contains(a) && post_pool.map().spec_index(a) == pre_pool.map().spec_index(a)
        &&& forall|k: int| #![trigger pages_4k[k]] 0 <= k < 5 ==> {
            let node = pre.pg_arr.spec_index(pages_4k[k]).view().view().free_list_node_storage.addr();
            &&& post_pool.map().dom().contains(node)
            &&& post_pool.map().spec_index(node) == page_index2page_ptr(pages_4k[k])
        }
        &&& post_allocator.global_pool.locking_thread() == pre_allocator.global_pool.locking_thread()
        &&& post_allocator.cpu_caches == pre_allocator.cpu_caches
        &&& post_allocator.owning_container == pre_allocator.owning_container
    })
    &&& post.allc_2m_mp.perms_wf()
    &&& post.allc_2m_mp.dom() == pre.allc_2m_mp.dom().remove(ro.allocator_ptr_2m)
    &&& forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_2m_mp.spec_index(a)]
        post.allc_2m_mp.dom().contains(a) && a != owner_ro.allocator_ptr_2m ==> post.allc_2m_mp.spec_index(a) == pre.allc_2m_mp.spec_index(a)
    &&& ({
        let pre_allocator = pre.allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m);
        let post_allocator = post.allc_2m_mp.spec_index(owner_ro.allocator_ptr_2m);
        let pre_pool = pre_allocator.global_pool.view();
        let post_pool = post_allocator.global_pool.view();
        &&& post_allocator.wf()
        &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + 2
        &&& post_allocator.quota.view() == (AllocatorQuota { value: (pre_allocator.quota.view().value + 2) as usize, ..pre_allocator.quota.view() })
        &&& post_allocator.quota.locking_thread() == pre_allocator.quota.locking_thread()
        &&& post_allocator.quota.is_init()
        &&& post_pool.view().len() == pre_pool.view().len() + 2
        &&& post_pool.view() == pre_pool.view().insert(0, page_index2page_ptr(heads[0])).insert(0, page_index2page_ptr(heads[1]))
        &&& forall|a: usize| #![trigger pre_pool.map().dom().contains(a)] pre_pool.map().dom().contains(a) ==> post_pool.map().dom().contains(a) && post_pool.map().spec_index(a) == pre_pool.map().spec_index(a)
        &&& forall|k: int| #![trigger heads[k]] 0 <= k < 2 ==> {
            let node = pre.pg_arr.spec_index(heads[k]).view().view().free_list_node_storage.addr();
            &&& post_pool.map().dom().contains(node)
            &&& post_pool.map().spec_index(node) == page_index2page_ptr(heads[k])
        }
        &&& post_allocator.global_pool.locking_thread() == pre_allocator.global_pool.locking_thread()
        &&& post_allocator.cpu_caches == pre_allocator.cpu_caches
        &&& post_allocator.owning_container == pre_allocator.owning_container
    })
    &&& post.allc_1g_mp.perms_wf()
    &&& post.allc_1g_mp.dom() == pre.allc_1g_mp.dom().remove(ro.allocator_ptr_1g)
    &&& forall|a: RwLockPageAllocatorPtr| #![trigger post.allc_1g_mp.spec_index(a)] post.allc_1g_mp.dom().contains(a) ==> post.allc_1g_mp.spec_index(a) == pre.allc_1g_mp.spec_index(a)
    &&& page_array_wf(post.pg_arr)
    &&& forall|i: PageIndex| #![trigger post.pg_arr.spec_index(i)]
        index_valid(NUM_PAGES, i) && !pages_4k.contains(i) && !heads.contains(i) && !tails.contains(i) ==> post.pg_arr.spec_index(i) == pre.pg_arr.spec_index(i)
    &&& forall|k: int| #![trigger pages_4k[k]] 0 <= k < 5 ==> {
        let pre_page = pre.pg_arr.spec_index(pages_4k[k]).view();
        let post_page = post.pg_arr.spec_index(pages_4k[k]).view();
        &&& post_page.is_init() == pre_page.is_init()
        &&& post_page.locking_thread() == pre_page.locking_thread()
        &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
        &&& post_page.view() == (Page { state: PageState::Free4k { allocator_ptr: Ghost(owner_ro.allocator_ptr_4k), state: FreePageAllocatorState::GlobalList },
            owning_container: owner_ptr, free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    }
    &&& forall|k: int| #![trigger heads[k]] 0 <= k < 2 ==> {
        let pre_page = pre.pg_arr.spec_index(heads[k]).view();
        let post_page = post.pg_arr.spec_index(heads[k]).view();
        &&& post_page.is_init() == pre_page.is_init()
        &&& post_page.locking_thread() == pre_page.locking_thread()
        &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
        &&& post_page.view() == (Page { state: PageState::Free2m { allocator_ptr: Ghost(owner_ro.allocator_ptr_2m), state: FreePageAllocatorState::GlobalList },
            owning_container: owner_ptr, free_list_node_storage: post_page.view().free_list_node_storage, perm_2m: post_page.view().perm_2m, ..pre_page.view() })
    }
    &&& forall|i: PageIndex| #![trigger post.pg_arr.spec_index(i)] tails.contains(i) ==> {
        &&& post.pg_arr.spec_index(i).view().view() == (Page { owning_container: owner_ptr, ..pre.pg_arr.spec_index(i).view().view() })
        &&& post.pg_arr.spec_index(i).view().is_init() == pre.pg_arr.spec_index(i).view().is_init()
        &&& post.pg_arr.spec_index(i).view().locking_thread() == pre.pg_arr.spec_index(i).view().locking_thread()
    }
}

/// Retiring the marked childless container `container_ptr`, which owns no process, thread, cpu, or quota, has
/// `owner_ptr` in its upper tree, and owns no page staged in a thread, keeps every kernel invariant.
pub(crate) proof fn kill_container_retire_eof(pre: KernelK, post: KernelK, container_ptr: RwLockContainerPtr, parent_ptr: RwLockContainerPtr, owner_ptr: RwLockContainerPtr)
    requires
        pre.inv(),
        kill_container_retire_eof_transition_framing(pre, post, container_ptr, parent_ptr, owner_ptr),
        kill_container_retire_eof_target_empty(pre, container_ptr, parent_ptr, owner_ptr),
        post.ctn_mp.spec_index(parent_ptr).view().inv(),
        post.ctn_mp.spec_index(parent_ptr).view().children.view().no_duplicates(),
    ensures post.inv(),
{
    kill_container_retire_eof_container_perms(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_container_tree(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_container_objects(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_container_threads(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_container_processes(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_tlb(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_page_objects_allocators(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_page_objects_containers(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_page_objects_retired(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_page_objects_processes(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_page_objects_threads(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_hugepages(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_mappings_pagetable(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_mappings(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_page_owners(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_allocators(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_allocator_free_4k_pages(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_allocator_free_2m_pages(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_allocator_free_1g_pages(pre, post, container_ptr, parent_ptr, owner_ptr);
    kill_container_retire_eof_allocator_quotas(pre, post, container_ptr, parent_ptr, owner_ptr);
    reveal(kill_container_retire_eof_transition_framing); reveal(KernelK::default_pagetable_wf);
}
} // verus!
