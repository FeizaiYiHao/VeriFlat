use vstd::prelude::*;
use crate::*;

verus! {
/// The exiting thread `thread_ptr` leaves the kernel from `cpu_id`, which goes idle on the default page table: its
/// process drops it through the process-list node at `proc_node_addr`, absorbs its quotas, and becomes a zombie without
/// threads; a zombie root process makes the container a zombie; the container and its upper containers drop the thread;
/// and the thread's page returns through its free-list node at `cache_node_addr` to shard `cpu_id` of the 4K allocator
/// of its owner `owner`, whose quota grows by one; a zombie releases its PCID to its container's PCID allocator.
#[verifier::opaque]
pub open spec fn thread_exit_destroy_transition(
    pre: KernelK, post: KernelK, cpu_id: CpuId, container_ptr: RwLockContainerPtr, process_ptr: RwLockProcessPtr, thread_ptr: RwLockThreadPtr,
    owner: RwLockContainerPtr, allocator_ptr: RwLockPageAllocatorPtr, proc_node_addr: usize, cache_node_addr: usize,
) -> bool {
    let page_index = page_ptr2page_index(thread_ptr);
    let thread = pre.thr_mp.spec_index(thread_ptr).view();
    let uppers = pre.ctn_mp.spec_index(container_ptr).view_ghost().uppertree_seq.view();
    let pre_process = pre.prc_mp.spec_index(process_ptr);
    let post_process = post.prc_mp.spec_index(process_ptr);
    let zombie = post_process.view().owned_threads.view().len() == 0;
    let pre_cpu = pre.cpu_arr.spec_index(cpu_id).view();
    let post_cpu = post.cpu_arr.spec_index(cpu_id).view();
    let pre_needflush = pre.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID);
    let post_needflush = post.pcid_needflush.spec_index(cpu_id, KERNEL_DEFAULT_PCID);
    let flushed = pre_needflush.view().needflush;
    let empty_tlb = SingleTLB { tlb_4k: Map::empty(), tlb_2m: Map::empty(), tlb_1g: Map::empty() };
    let pre_page = pre.pg_arr.spec_index(page_index).view();
    let post_page = post.pg_arr.spec_index(page_index).view();
    let free_state = PageState::Free4k { allocator_ptr: Ghost(allocator_ptr), state: FreePageAllocatorState::PreCpuCache { cpu_id } };
    let pre_allocator = pre.allc_4k_mp.spec_index(allocator_ptr);
    let post_allocator = post.allc_4k_mp.spec_index(allocator_ptr);
    let pre_cache = pre_allocator.cpu_caches.spec_index(cpu_id).view();
    let post_cache = post_allocator.cpu_caches.spec_index(cpu_id).view();
    let pcid_allocator_ptr = pre.ctn_mp.spec_index(container_ptr).view_rodata().view().pcid_allocator;
    let pre_pcid_allocator = pre.pcid_allc_mp.spec_index(pcid_allocator_ptr);
    let post_pcid_allocator = post.pcid_allc_mp.spec_index(pcid_allocator_ptr);
    &&& index_valid(NUM_CPUS, cpu_id)
    &&& page_ptr_valid(thread_ptr)
    &&& pre.thr_mp.dom().contains(thread_ptr)
    &&& !pre.thr_mp.spec_index(thread_ptr).being_killed()
    &&& thread.state == (ThreadState::RUNNING { cpu_id })
    &&& thread.owning_proc == process_ptr
    &&& thread.owning_container == container_ptr
    &&& thread.caller is None
    &&& thread.callee is None
    &&& forall|j: int| #![trigger thread.endpoint_descriptors.view().spec_index(j)] 0 <= j < MAX_NUM_ENDPOINT_DESCRIPTORS ==> thread.endpoint_descriptors.view().spec_index(j) is None
    &&& thread.temp_alloc_clean()
    &&& thread.free_quota_pending_clean()
    &&& thread.proc_linkedlist_node.addr() == proc_node_addr
    &&& pre.prc_mp.dom().contains(process_ptr)
    &&& pre_process.view().quota_4k + thread.quota_4k <= usize::MAX
    &&& pre_process.view().quota_2m + thread.quota_2m <= usize::MAX
    &&& pre_process.view().quota_1g + thread.quota_1g <= usize::MAX
    &&& pre.ctn_mp.dom().contains(container_ptr)
    &&& pre.ctn_mp.dom().contains(owner)
    &&& pre_page.view().owning_container == owner
    &&& pre_page.view().state == (PageState::Allocated4k { state: Allocated4KPageState::AsThread })
    &&& pre.ctn_mp.spec_index(owner).view_rodata().view().allocator_ptr_4k == allocator_ptr
    &&& pre.allc_4k_mp.dom().contains(allocator_ptr)
    &&& post == (KernelK {
        cpu_arr: post.cpu_arr, cpu_tlb: post.cpu_tlb, pcid_needflush: post.pcid_needflush, cpu_published: post.cpu_published, ctn_mp: post.ctn_mp, prc_mp: post.prc_mp,
        thr_mp: post.thr_mp, pg_arr: post.pg_arr, allc_4k_mp: post.allc_4k_mp, pcid_allc_mp: post.pcid_allc_mp, ..pre
    })
    &&& post.cpu_arr.entries_unchanged_except(&pre.cpu_arr, cpu_id)
    &&& post_cpu.locking_thread() == pre_cpu.locking_thread()
    &&& post_cpu.being_killed() == pre_cpu.being_killed()
    &&& post_cpu.killer_info() == pre_cpu.killer_info()
    &&& !pre_cpu.being_killed()
    &&& post_cpu.view_rodata() == pre_cpu.view_rodata()
    &&& post_cpu.view_ghost() == pre_cpu.view_ghost()
    &&& post_cpu.view().view() == (CpuView {
        state: CpuState::Idle, current_process: None, current_thread: None, current_pagetable: None, current_cr3: pre.dflt_pt.view().cr3, current_pcid: KERNEL_DEFAULT_PCID,
        ..pre_cpu.view().view()
    })
    &&& post.cpu_tlb.view() == if flushed { pre.cpu_tlb.view().insert((cpu_id, KERNEL_DEFAULT_PCID), empty_tlb) } else { pre.cpu_tlb.view() }
    &&& forall|c: CpuId, p: Pcid| #![trigger post.cpu_tlb.spec_index((c, p))]
        index_valid(NUM_CPUS, c) && pcid_valid(p) ==> post.cpu_tlb.spec_index((c, p)) == if flushed && c == cpu_id && p == KERNEL_DEFAULT_PCID { empty_tlb } else { pre.cpu_tlb.spec_index((c, p)) }
    &&& post_needflush.view() == (PcidNeedFlush { needflush: false, ..pre_needflush.view() })
    &&& post_needflush.is_init()
    &&& post_needflush.locking_thread() == pre_needflush.locking_thread()
    &&& post_needflush.view_ghost() == pre_needflush.view_ghost()
    &&& post_needflush.view_rodata() == pre_needflush.view_rodata()
    &&& post_needflush.being_killed() == pre_needflush.being_killed()
    &&& forall|c: CpuId, p: Pcid| #![trigger post.pcid_needflush.spec_index(c, p)]
        index_valid(NUM_CPUS, c) && pcid_valid(p) && (c != cpu_id || p != KERNEL_DEFAULT_PCID) ==> post.pcid_needflush.spec_index(c, p) == pre.pcid_needflush.spec_index(c, p)
    &&& post.cpu_published[cpu_id as int].view() == (pre.dflt_pt.view().cr3, KERNEL_DEFAULT_PCID)
    &&& post.cpu_published[cpu_id as int].owner_cpu() == pre.cpu_published[cpu_id as int].owner_cpu()
    &&& forall|c: CpuId| #![trigger post.cpu_published[c as int]] index_valid(NUM_CPUS, c) && c != cpu_id ==> post.cpu_published[c as int] == pre.cpu_published[c as int]
    &&& post.ctn_mp.dom() == pre.ctn_mp.dom()
    &&& forall|c: RwLockContainerPtr| #![trigger post.ctn_mp.spec_index(c)]
        pre.ctn_mp.dom().contains(c) ==> {
            let before = pre.ctn_mp.spec_index(c);
            let after = post.ctn_mp.spec_index(c);
            &&& after.is_init() == before.is_init()
            &&& after.view() == if c == container_ptr { Container { zombie: before.view().zombie || (zombie && before.view().root_process == process_ptr), ..before.view() } } else { before.view() }
            &&& after.view_rodata() == before.view_rodata()
            &&& after.locking_thread() == before.locking_thread()
            &&& after.being_killed() == before.being_killed()
            &&& after.view_ghost() == (ContainerGhost {
                owned_threads: if c == container_ptr { Ghost(before.view_ghost().owned_threads.view().remove(thread_ptr)) } else { before.view_ghost().owned_threads },
                owned_indirect_threads: if uppers.to_set().contains(c) { Ghost(before.view_ghost().owned_indirect_threads.view().remove(thread_ptr)) }
                    else { before.view_ghost().owned_indirect_threads },
                ..before.view_ghost()
            })
        }
    &&& post.prc_mp.dom() == pre.prc_mp.dom()
    &&& post.prc_mp.unchanged_except(&pre.prc_mp, process_ptr)
    &&& post_process.view() == (Process {
        zombie, state: if zombie { Ghost(ProcessState::Zombie) } else { pre_process.view().state }, quota_4k: (pre_process.view().quota_4k + thread.quota_4k) as usize,
        quota_2m: (pre_process.view().quota_2m + thread.quota_2m) as usize, quota_1g: (pre_process.view().quota_1g + thread.quota_1g) as usize,
        owned_threads: post_process.view().owned_threads, ..pre_process.view()
    })
    &&& pre_process.view().owned_threads.view().contains(thread_ptr)
    &&& post_process.view().owned_threads.view() == pre_process.view().owned_threads.view().remove_value(thread_ptr)
    &&& post_process.view().owned_threads.view().len() == pre_process.view().owned_threads.view().len() - 1
    &&& post_process.view().owned_threads.dom() == pre_process.view().owned_threads.dom().remove(proc_node_addr)
    &&& post_process.view().owned_threads.map() == pre_process.view().owned_threads.map().remove(proc_node_addr)
    &&& pre_process.view().owned_threads.map().dom().contains(proc_node_addr)
    &&& pre_process.view().owned_threads.map().spec_index(proc_node_addr) == thread_ptr
    &&& post_process.view_rodata() == pre_process.view_rodata()
    &&& post_process.view_ghost() == pre_process.view_ghost()
    &&& post_process.locking_thread() == pre_process.locking_thread()
    &&& post_process.being_killed() == pre_process.being_killed()
    &&& !pre_process.being_killed()
    &&& zombie ==> pre_process.view().state.view() is TablesEmptied
    &&& post.thr_mp.dom() == pre.thr_mp.dom().remove(thread_ptr)
    &&& forall|t: RwLockThreadPtr| #![trigger post.thr_mp.spec_index(t)] post.thr_mp.dom().contains(t) ==> post.thr_mp.spec_index(t) == pre.thr_mp.spec_index(t)
    &&& post.pg_arr.entries_unchanged_except(&pre.pg_arr, page_index)
    &&& forall|i: PageIndex| #![trigger pre.pg_arr.spec_index(i).view().view().state] #![trigger post.pg_arr.spec_index(i).view().view().state]
        index_valid(NUM_PAGES, i) ==> {
            &&& post.pg_arr.spec_index(i).view().view().state == if i == page_index { free_state } else { pre.pg_arr.spec_index(i).view().view().state }
            &&& post.pg_arr.spec_index(i).view().view().owning_container == pre.pg_arr.spec_index(i).view().view().owning_container
            &&& post.pg_arr.spec_index(i).view().view().mappings() == pre.pg_arr.spec_index(i).view().view().mappings()
        }
    &&& post_page.is_init() == pre_page.is_init()
    &&& post_page.view_rodata() == pre_page.view_rodata()
    &&& post_page.view_ghost() == pre_page.view_ghost()
    &&& post_page.locking_thread() == pre_page.locking_thread()
    &&& post_page.being_killed() == pre_page.being_killed()
    &&& pre_page.view().free_list_node_storage.addr() == cache_node_addr
    &&& post_page.view().free_list_node_storage.addr() == cache_node_addr
    &&& post_page.view() == (Page { state: free_state, free_list_node_storage: post_page.view().free_list_node_storage, perm_4k: post_page.view().perm_4k, ..pre_page.view() })
    &&& post.allc_4k_mp.dom() == pre.allc_4k_mp.dom()
    &&& post.allc_4k_mp.unchanged_except(&pre.allc_4k_mp, allocator_ptr)
    &&& post_allocator.total_free_pages.view() == pre_allocator.total_free_pages.view() + 1
    &&& post_cache.view().view() == pre_cache.view().view().insert(0, thread_ptr)
    &&& post_cache.view().map() == pre_cache.view().map().insert(cache_node_addr, thread_ptr)
    &&& !pre_cache.view().map().dom().contains(cache_node_addr)
    &&& post_allocator.cpu_caches.entries_unchanged_except(&pre_allocator.cpu_caches, cpu_id)
    &&& post_cache.locking_thread() == pre_cache.locking_thread()
    &&& post_allocator.global_pool == pre_allocator.global_pool
    &&& post_allocator.owning_container == pre_allocator.owning_container
    &&& post_allocator.quota.view().value == pre_allocator.quota.view().value + 1
    &&& post_allocator.quota.view() == (AllocatorQuota { value: post_allocator.quota.view().value, ..pre_allocator.quota.view() })
    &&& post_allocator.quota.is_init() == pre_allocator.quota.is_init()
    &&& post_allocator.quota.view_rodata() == pre_allocator.quota.view_rodata()
    &&& post_allocator.quota.view_ghost() == pre_allocator.quota.view_ghost()
    &&& post_allocator.quota.locking_thread() == pre_allocator.quota.locking_thread()
    &&& post_allocator.quota.being_killed() == pre_allocator.quota.being_killed()
    &&& pre.pcid_allc_mp.dom().contains(pcid_allocator_ptr)
    &&& post.pcid_allc_mp.dom() == pre.pcid_allc_mp.dom()
    &&& if zombie {
        &&& post.pcid_allc_mp.unchanged_except(&pre.pcid_allc_mp, pcid_allocator_ptr)
        &&& pcid_valid(pre_process.view().pcid)
        &&& pre_process.view().pcid != KERNEL_DEFAULT_PCID
        &&& pre_pcid_allocator.view().id_to_proc.view().spec_index(pre_process.view().pcid as int).contains(process_ptr)
        &&& post_pcid_allocator.view().release_ensures(&pre_pcid_allocator.view(), process_ptr, pre_process.view().pcid)
        &&& post_pcid_allocator.locking_thread() == pre_pcid_allocator.locking_thread()
        &&& post_pcid_allocator.being_killed() == pre_pcid_allocator.being_killed()
    } else { post.pcid_allc_mp == pre.pcid_allc_mp }
}

} // verus!
