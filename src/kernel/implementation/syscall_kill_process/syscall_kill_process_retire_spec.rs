use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::syscall_kill_process_walk::{KillScope, kill_scope_containers};

verus! {
/// The page indices the retirement of `target` frees, in retire order: the process page, the page table's object page
/// and root table page, and, with an IOMMU table, its object page and root table page.
pub open spec fn kill_retire_pages(k: KernelK, target: RwLockProcessPtr) -> Seq<PageIndex> {
    let process = k.prc_mp.spec_index(target).view();
    let pt = k.pt_mp.spec_index(process.pagetable).view();
    let base = seq![page_ptr2page_index(target), page_ptr2page_index(process.pagetable), page_ptr2page_index(pt.cr3)];
    match process.iommu_table {
        Some(it) => base.push(page_ptr2page_index(it)).push(page_ptr2page_index(k.it_mp.spec_index(it).view().cr3)),
        None => base,
    }
}

/// Retiring the empty zombie `target`, whose parent is `parent_ptr` and whose container is `container_ptr`: the process
/// leaves the process map, its parent's children, and its ancestors' subtrees, and leaves its container's processes; its
/// page table and IOMMU table, which only hold their root tables, leave their maps; every page in
/// `kill_retire_pages(pre, target)` returns through its free-list node to shard `cpu_id` of the container's 4K allocator
/// `allocator_ptr`, whose quota grows by the number of those pages.
#[verifier::opaque]
pub open spec fn kill_retire_eof_transition_framing(
    pre: KernelK, post: KernelK, cpu_id: CpuId, target: RwLockProcessPtr, parent_ptr: RwLockProcessPtr, container_ptr: RwLockContainerPtr,
    allocator_ptr: RwLockPageAllocatorPtr,
) -> bool {
    let process = pre.prc_mp.spec_index(target);
    let pagetable = process.view().pagetable;
    let iommu_table = process.view().iommu_table;
    let uppers = process.view_ghost().uppertree_seq.view();
    let node_addr = process.view().parent_linkedlist_node.addr();
    let pages = kill_retire_pages(pre, target);
    let n = pages.len();
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    let pre_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let post_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    let pre_cache = pre_allocator.cpu_caches.spec_index(cpu_id).view();
    let post_cache = post_allocator.cpu_caches.spec_index(cpu_id).view();
    &&& post == (KernelK { prc_mp: post.prc_mp, ctn_mp: post.ctn_mp, pt_mp: post.pt_mp, it_mp: post.it_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, ..pre })
    &&& post.prc_mp.dom() == pre.prc_mp.dom().remove(target)
    &&& forall|p: RwLockProcessPtr| #![trigger post.prc_mp.spec_index(p)] post.prc_mp.dom().contains(p) ==> {
        let old_p = pre.prc_mp.spec_index(p);
        let new_p = post.prc_mp.spec_index(p);
        &&& new_p.view() == if p == parent_ptr { Process { children: new_p.view().children, ..old_p.view() } } else { old_p.view() }
        &&& new_p.view_ghost() == if uppers.contains(p) { ProcessGhost { subtree_set: Ghost(old_p.view_ghost().subtree_set.view().remove(target)), ..old_p.view_ghost() } }
            else { old_p.view_ghost() }
        &&& new_p.view_rodata() == old_p.view_rodata()
        &&& new_p.is_init() == old_p.is_init()
        &&& new_p.locking_thread() == old_p.locking_thread()
        &&& new_p.being_killed() == old_p.being_killed()
        &&& new_p.killer_info() == old_p.killer_info()
        &&& post.prc_mp.view().spec_index(p).is_init() == pre.prc_mp.view().spec_index(p).is_init()
        &&& post.prc_mp.view().spec_index(p).addr() == pre.prc_mp.view().spec_index(p).addr()
    }
    &&& post.prc_mp.spec_index(parent_ptr).view().children.view() == pre.prc_mp.spec_index(parent_ptr).view().children.view().remove_value(target)
    &&& post.prc_mp.spec_index(parent_ptr).view().children.map() == pre.prc_mp.spec_index(parent_ptr).view().children.map().remove(node_addr)
    &&& post.prc_mp.spec_index(parent_ptr).view().children.dom() == pre.prc_mp.spec_index(parent_ptr).view().children.dom().remove(node_addr)
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)] pre.ctn_mp.dom().contains(c) && c != container_ptr ==> post.ctn_mp.spec_index(c) == pre.ctn_mp.spec_index(c)
    &&& post.ctn_mp.spec_index(container_ptr).view() == pre.ctn_mp.spec_index(container_ptr).view()
    &&& post.ctn_mp.spec_index(container_ptr).view_rodata() == pre.ctn_mp.spec_index(container_ptr).view_rodata()
    &&& post.ctn_mp.spec_index(container_ptr).view_ghost() == (ContainerGhost {
        owned_processes: Ghost(pre.ctn_mp.spec_index(container_ptr).view_ghost().owned_processes.view().remove(target)), ..pre.ctn_mp.spec_index(container_ptr).view_ghost() })
    &&& post.ctn_mp.spec_index(container_ptr).locking_thread() == pre.ctn_mp.spec_index(container_ptr).locking_thread()
    &&& post.ctn_mp.spec_index(container_ptr).being_killed() == pre.ctn_mp.spec_index(container_ptr).being_killed()
    &&& post.ctn_mp.spec_index(container_ptr).killer_info() == pre.ctn_mp.spec_index(container_ptr).killer_info()
    &&& post.ctn_mp.unchanged_except(&pre.ctn_mp, container_ptr)
    &&& post.pt_mp.dom() =~= pre.pt_mp.dom().remove(pagetable)
    &&& forall|t: RwLockPageTableRoot| #![trigger post.pt_mp.spec_index(t)] post.pt_mp.dom().contains(t) ==> post.pt_mp.spec_index(t) == pre.pt_mp.spec_index(t)
    &&& forall|t: RwLockPageTableRoot| #![trigger post.pt_mp.lock_id_by_key(t)] post.pt_mp.dom().contains(t) ==> post.pt_mp.lock_id_by_key(t) == pre.pt_mp.lock_id_by_key(t)
    &&& post.it_mp.dom() =~= match iommu_table { Some(it) => pre.it_mp.dom().remove(it), None => pre.it_mp.dom() }
    &&& forall|t: RwLockPageTableRoot| #![trigger post.it_mp.spec_index(t)] post.it_mp.dom().contains(t) ==> post.it_mp.spec_index(t) == pre.it_mp.spec_index(t)
    &&& forall|t: RwLockPageTableRoot| #![trigger post.it_mp.lock_id_by_key(t)] post.it_mp.dom().contains(t) ==> post.it_mp.lock_id_by_key(t) == pre.it_mp.lock_id_by_key(t)
    &&& forall|i: PageIndex| #![trigger post.pg_arr.spec_index(i)] index_valid(NUM_PAGES, i) && !pages.contains(i) ==> post.pg_arr.spec_index(i) == pre.pg_arr.spec_index(i)
    &&& forall|k: int| #![trigger pages[k]] 0 <= k < n ==> {
        let pre_page = pre.pg_arr.spec_index(pages[k]).view();
        let post_page = post.pg_arr.spec_index(pages[k]).view();
        &&& post_page.is_init() == pre_page.is_init()
        &&& post_page.view_rodata() == pre_page.view_rodata()
        &&& post_page.view_ghost() == pre_page.view_ghost()
        &&& post_page.locking_thread() == pre_page.locking_thread()
        &&& post_page.being_killed() == pre_page.being_killed()
        &&& post_page.view().free_list_node_storage.addr() == pre_page.view().free_list_node_storage.addr()
        &&& post_page.view() == (Page { state: free_state, free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    }
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + n
    &&& post_cache.view().view().len() == pre_cache.view().view().len() + n
    &&& forall|p: PagePtr| #![trigger post_cache.view().view().contains(p)]
        post_cache.view().view().contains(p) == (pre_cache.view().view().contains(p) || pages.contains(page_ptr2page_index(p)) && page_ptr_valid(p))
    &&& forall|a: usize| #![trigger pre_cache.view().map().dom().contains(a)]
        pre_cache.view().map().dom().contains(a) ==> post_cache.view().map().dom().contains(a) && post_cache.view().map().spec_index(a) == pre_cache.view().map().spec_index(a)
    &&& forall|k: int| #![trigger pages[k]] 0 <= k < n ==> {
        let node = pre.pg_arr.spec_index(pages[k]).view().view().free_list_node_storage.addr();
        &&& !pre_cache.view().map().dom().contains(node)
        &&& post_cache.view().map().dom().contains(node)
        &&& post_cache.view().map().spec_index(node) == page_index2page_ptr(pages[k])
    }
    &&& post_allocator.cpu_caches.entries_unchanged_except(&pre_allocator.cpu_caches, cpu_id)
    &&& post_cache.locking_thread() == pre_cache.locking_thread()
    &&& post_allocator.global_pool == pre_allocator.global_pool
    &&& post_allocator.owning_container == pre_allocator.owning_container
    &&& post_allocator.quota.view().value == pre_allocator.quota.view().value + n
    &&& post_allocator.quota.view() == (AllocatorQuota { value: post_allocator.quota.view().value, ..pre_allocator.quota.view() })
    &&& post_allocator.quota.is_init() == pre_allocator.quota.is_init()
    &&& post_allocator.quota.view_rodata() == pre_allocator.quota.view_rodata()
    &&& post_allocator.quota.view_ghost() == pre_allocator.quota.view_ghost()
    &&& post_allocator.quota.locking_thread() == pre_allocator.quota.locking_thread()
    &&& post_allocator.quota.being_killed() == pre_allocator.quota.being_killed()
}

/// The pages the killer write-holds from before it locks the zombie `target`'s tables until it retires `target`: the
/// process page and the object pages of its page table and, if any, its IOMMU table.
pub open spec fn kill_retire_held_pages(k: KernelK, target: RwLockProcessPtr) -> Set<PageIndex> {
    let process = k.prc_mp.spec_index(target).view();
    match process.iommu_table {
        Some(it) => set![page_ptr2page_index(target), page_ptr2page_index(process.pagetable), page_ptr2page_index(it)],
        None => set![page_ptr2page_index(target), page_ptr2page_index(process.pagetable)],
    }
}

/// The killer `thread_ptr` of process `process_ptr`, retiring the zombie `target` in `scope`, holds its
/// `killer_held_context_except_tables` locks with the containers of `scope` and besides write-holds the pages
/// `kill_retire_held_pages(k, target)` with `page_perms`, the target's page table with `pt_perm`, and its IOMMU table, if
/// any, with `it_perm`.
pub open spec fn kill_retire_held_state(
    k: KernelK, lctx: LocalContext, scope: KillScope, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr, target: RwLockProcessPtr,
    page_perms: Map<PageIndex, LockPerm>, pt_perm: LockPerm, it_perm: Option<LockPerm>,
) -> bool {
    let process = k.prc_mp.spec_index(target).view();
    let held = kill_retire_held_pages(k, target);
    &&& killer_held_context_except_tables(k, lctx, process_ptr, thread_ptr, kill_scope_containers(scope, lctx))
    &&& lctx.page_lock_map().dom() == held
    &&& page_perms.dom() == held
    &&& forall|p: PageIndex| #![trigger page_perms.dom().contains(p)] page_perms.dom().contains(p) ==> {
        &&& typed_lock_map_contains_mode(lctx.page_lock_map(), p, TypedLockMode::Write)
        &&& page_perms[p].state() is WriteLock
        &&& page_perms[p].thread_id() == lctx.thread_id()
        &&& page_perms[p].lock_id() == k.pg_arr.spec_index(p).view().locking_thread()->Write_lock_id
    }
    &&& lctx.pagetable_lock_map().dom() == set![process.pagetable]
    &&& typed_lock_map_contains_mode(lctx.pagetable_lock_map(), process.pagetable, TypedLockMode::Write)
    &&& pt_perm.state() is WriteLock
    &&& pt_perm.thread_id() == lctx.thread_id()
    &&& pt_perm.lock_id() == k.pt_mp.spec_index(process.pagetable).locking_thread()->Write_lock_id
    &&& lctx.iommu_table_lock_map().dom() == match process.iommu_table { Some(it) => set![it], None => Set::<RwLockPageTableRoot>::empty() }
    &&& it_perm is Some == process.iommu_table is Some
    &&& process.iommu_table is Some ==> {
        let it = process.iommu_table->Some_0;
        &&& typed_lock_map_contains_mode(lctx.iommu_table_lock_map(), it, TypedLockMode::Write)
        &&& it_perm->Some_0.state() is WriteLock
        &&& it_perm->Some_0.thread_id() == lctx.thread_id()
        &&& it_perm->Some_0.lock_id() == k.it_mp.spec_index(it).locking_thread()->Write_lock_id
    }
}

/// The page table of the zombie `target` and its IOMMU table, if any, hold only their root tables and map nothing.
pub open spec fn kill_retire_tables_emptied(k: KernelK, target: RwLockProcessPtr) -> bool {
    let process = k.prc_mp.spec_index(target).view();
    let pt = k.pt_mp.spec_index(process.pagetable).view();
    &&& pt.page_closure() =~= set![pt.cr3]
    &&& pt.mapping_4k().dom() =~= Set::<VAddr>::empty()
    &&& pt.mapping_2m().dom() =~= Set::<VAddr>::empty()
    &&& pt.mapping_1g().dom() =~= Set::<VAddr>::empty()
    &&& process.iommu_table is Some ==> {
        let it = k.it_mp.spec_index(process.iommu_table->Some_0).view();
        &&& it.page_closure() =~= set![it.cr3]
        &&& it.mapping_4k().dom() =~= Set::<VAddr>::empty()
        &&& it.mapping_2m().dom() =~= Set::<VAddr>::empty()
        &&& it.mapping_1g().dom() =~= Set::<VAddr>::empty()
    }
}
} // verus!
