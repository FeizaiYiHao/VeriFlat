#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_commit_spec::*;

verus! {
pub proof fn split_2m_commit_eof_implies_allocator_global_pool_4k_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
{
    assert(allocator_global_pool_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing);
        allocator_free_2m_pages_wf_at(pre.allc_2m_mp, pre.pg_arr, head);
        reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf);
        reveal(allocator_free_page_ptrs_wf); reveal(hugepage_2m_wf);
        page_ptr_roundtrip(); page_index_roundtrip(); page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn split_2m_commit_eof_implies_allocator_cpu_cache_4k_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
{
    assert(allocator_cpu_cache_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing);
        allocator_free_2m_pages_wf_at(pre.allc_2m_mp, pre.pg_arr, head);
        reveal(allocator_free_4k_pages_wf); reveal(allocator_global_pool_4k_pages_wf); reveal(allocator_cpu_cache_4k_pages_wf);
        reveal(allocator_free_page_ptrs_wf); reveal(hugepage_2m_wf);
        page_ptr_roundtrip(); page_index_roundtrip(); page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn split_2m_commit_eof_implies_allocator_global_pool_2m_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    assert(allocator_global_pool_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(allocator_free_2m_pages_wf); reveal(allocator_global_pool_2m_pages_wf);
        reveal(allocator_free_page_ptrs_wf); reveal(hugepage_2m_wf);
        page_index_roundtrip(); page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn split_2m_commit_eof_implies_allocator_cpu_cache_2m_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    assert(allocator_cpu_cache_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(allocator_free_2m_pages_wf); reveal(allocator_cpu_cache_2m_pages_wf);
        reveal(allocator_free_page_ptrs_wf); reveal(hugepage_2m_wf);
        page_index_roundtrip(); page_ptr_valid_imply_page_index_valid();
    };
}

pub proof fn split_2m_commit_eof_implies_page_array_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        page_array_wf(post.pg_arr),
{
    assert(page_array_wf(post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(page_array_wf); reveal(Page::mappings_va_valid); reveal(hugepage_2m_wf); assert(PAGE_SZ_4K == 4096) by (bit_vector); };
}

pub proof fn split_2m_commit_eof_implies_allocator_perms_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_perms_wf(post.allc_4k_mp),
        allocator_perms_wf(post.allc_2m_mp),
{
    assert(allocator_perms_wf(post.allc_4k_mp)) by { reveal(split_2m_commit_eof_transition_framing); reveal(allocator_perms_wf); };
    assert(allocator_perms_wf(post.allc_2m_mp)) by { reveal(split_2m_commit_eof_transition_framing); reveal(allocator_perms_wf); };
}

/// EOF closure of `split_2m_commit` for the allocator pages: no page enters or leaves an allocator-holding state, and both
/// allocator maps keep their domains.
proof fn split_2m_commit_eof_allocator_page_states(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        post.allc_4k_mp.dom() == pre.allc_4k_mp.dom() && post.allc_2m_mp.dom() == pre.allc_2m_mp.dom(),
        forall|p_i: PageIndex| #![trigger post.pg_arr.spec_index(p_i)] index_valid(NUM_PAGES, p_i) ==> {
            &&& (post.pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
                == (pre.pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As4KAllocator })
            &&& (post.pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
                == (pre.pg_arr.spec_index(p_i).view().view().state matches PageState::Allocated4k { state: Allocated4KPageState::As2MAllocator })
        },
{ reveal(split_2m_commit_eof_transition_framing); reveal(hugepage_2m_wf); }

pub proof fn split_2m_commit_eof_implies_allocator_4k_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
{
    split_2m_commit_eof_allocator_page_states(pre, post, thread, allocator_4k, allocator_2m, head, source);
    assert(allocator_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_4k_pages_wf); };
}

pub proof fn split_2m_commit_eof_implies_allocator_2m_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
{
    split_2m_commit_eof_allocator_page_states(pre, post, thread, allocator_4k, allocator_2m, head, source);
    assert(allocator_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_2m_pages_wf); };
}

pub proof fn split_2m_commit_eof_implies_allocator_1g_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    assert(allocator_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing); reveal(allocator_1g_pages_wf); reveal(hugepage_2m_wf); };
}

pub proof fn split_2m_commit_eof_implies_container_allocator_and_kill_retire_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    assert(container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(split_2m_commit_eof_transition_framing); reveal(container_allocator_wf); };
    assert(container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp)) by { reveal(split_2m_commit_eof_transition_framing); reveal(container_kill_retire_wf); };
}

pub proof fn split_2m_commit_eof_implies_allocator_free_page_ptrs_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
{
    assert(allocator_free_page_ptrs_wf(post.allc_4k_mp)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(allocator_free_page_ptrs_wf);
    };
    assert(allocator_free_page_ptrs_wf(post.allc_2m_mp)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(allocator_free_page_ptrs_wf);
        page_index_valid_imply_page_ptr_valid();
    };
}

pub proof fn split_2m_commit_eof_implies_allocator_page_representation_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        page_array_wf(post.pg_arr),
        allocator_perms_wf(post.allc_4k_mp),
        allocator_perms_wf(post.allc_2m_mp),
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    split_2m_commit_eof_implies_page_array_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_perms_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_4k_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_2m_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_1g_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_container_allocator_and_kill_retire_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_free_page_ptrs_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
}

pub proof fn split_2m_commit_eof_implies_allocator_free_1g_pages_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
{
    assert(allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(allocator_free_1g_pages_wf); reveal(allocator_global_pool_1g_pages_wf); reveal(allocator_cpu_cache_1g_pages_wf);
        reveal(allocator_free_page_ptrs_wf); reveal(hugepage_2m_wf);
    };
}

pub proof fn split_2m_commit_eof_implies_allocator_page_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        page_array_wf(post.pg_arr),
        allocator_perms_wf(post.allc_4k_mp),
        allocator_perms_wf(post.allc_2m_mp),
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    split_2m_commit_eof_implies_allocator_page_representation_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_global_pool_4k_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_cpu_cache_4k_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    assert(allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr)) by { reveal(allocator_free_4k_pages_wf); };
    split_2m_commit_eof_implies_allocator_global_pool_2m_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_cpu_cache_2m_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    assert(allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr)) by { reveal(allocator_free_2m_pages_wf); };
    split_2m_commit_eof_implies_allocator_free_1g_pages_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
}

pub proof fn split_2m_commit_eof_implies_allocator_quota_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.thrd_mp.spec_index(thread).view().quota_4k <= usize::MAX - 512,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
    ensures
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    assert(container_process_allocator_quota_4k_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(container_process_allocator_quota_4k_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
        one_member_changed_implies_thread_effective_quota_4k_fold_sum_changed_by_forall(thread, 512); unchanged_members_implies_thread_effective_quota_4k_fold_sum_eq_forall();
        unchanged_thread_pending_4k_implies_per_container_pending_4k_fold_sums_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(container_process_allocator_quota_2m_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_2m_mp)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(container_process_allocator_quota_2m_wf); reveal(container_thread_wf); reveal(container_allocator_wf);
        one_member_changed_implies_thread_effective_quota_2m_fold_sum_changed_by_forall(thread, -1); unchanged_members_implies_thread_effective_quota_2m_fold_sum_eq_forall();
        unchanged_thread_pending_2m_implies_per_container_pending_2m_fold_sums_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
    assert(container_process_allocator_quota_1g_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_1g_mp)) by { reveal(split_2m_commit_eof_transition_framing);
        reveal(container_process_allocator_quota_1g_wf); reveal(container_thread_wf);
        unchanged_members_implies_thread_effective_quota_1g_fold_sum_eq_forall(); unchanged_thread_pending_1g_implies_per_container_pending_1g_fold_sums_eq_forall(post.ctn_mp, pre.thrd_mp, post.thrd_mp);
    };
}

pub proof fn split_2m_commit_eof_implies_allocator_and_quota_wf(pre: KernelK, post: KernelK, thread: RwLockThreadPtr,
    allocator_4k: RwLockPageAllocatorPtr, allocator_2m: RwLockPageAllocatorPtr, head: PageIndex, source: usize)
    requires
        pre.inv(),
        pre.thrd_mp.dom().contains(thread),
        pre.thrd_mp.spec_index(thread).view().temp_alloc_clean(),
        pre.thrd_mp.spec_index(thread).view().quota_2m > 0,
        pre.thrd_mp.spec_index(thread).view().quota_4k <= usize::MAX - 512,
        pre.allc_4k_mp.dom().contains(allocator_4k),
        pre.allc_2m_mp.dom().contains(allocator_2m),
        pre.allc_4k_mp.spec_index(allocator_4k).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        pre.allc_2m_mp.spec_index(allocator_2m).owning_container == pre.thrd_mp.spec_index(thread).view().owning_container,
        page_index_2m_valid(head),
        source <= NUM_CPUS,
        pre.pg_arr.spec_index(head).view().view().state == (PageState::Free2m { allocator_ptr: Ghost(allocator_2m), state:
            if source < NUM_CPUS { FreePageAllocatorState::PreCpuCache { cpu_id: source } } else { FreePageAllocatorState::GlobalList } }),
        split_2m_commit_eof_transition_framing(pre, post, thread, allocator_4k, allocator_2m, head, source),
        post.pg_arr.inv(),
        post.allc_4k_mp.perms_wf(),
        post.allc_2m_mp.perms_wf(),
        post.allc_4k_mp.spec_index(allocator_4k).wf(),
        post.allc_2m_mp.spec_index(allocator_2m).wf(),
    ensures
        page_array_wf(post.pg_arr),
        allocator_perms_wf(post.allc_4k_mp),
        allocator_perms_wf(post.allc_2m_mp),
        allocator_pages_wf(post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp, post.pg_arr),
        allocator_free_page_ptrs_wf(post.allc_4k_mp),
        allocator_free_page_ptrs_wf(post.allc_2m_mp),
        allocator_free_4k_pages_wf(post.allc_4k_mp, post.pg_arr),
        allocator_free_2m_pages_wf(post.allc_2m_mp, post.pg_arr),
        allocator_free_1g_pages_wf(post.allc_1g_mp, post.pg_arr),
        container_allocator_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_kill_retire_wf(post.ctn_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
        container_process_allocator_quota_wf(post.ctn_mp, post.prc_mp, post.thrd_mp, post.allc_4k_mp, post.allc_2m_mp, post.allc_1g_mp),
{
    split_2m_commit_eof_implies_allocator_page_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
    split_2m_commit_eof_implies_allocator_quota_wf(pre, post, thread, allocator_4k, allocator_2m, head, source);
}
}
