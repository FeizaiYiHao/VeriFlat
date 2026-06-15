use vstd::prelude::*;
use crate::*;

verus! {

    /// User-level projection of the kernel state.
    ///
    /// This is a sound capture of the kernel user-level view because
    /// `LocalContext` does not provide any interface that allows
    /// Lock → Operate → Unlock → Lock on user-visible objects within a
    /// single syscall. Therefore, all operations on the user view can
    /// be seen as atomic from the syscall's perspective.
    pub ghost struct KernelU{
        pub cpu_array: Seq<CpuU>,
        pub process_map: Map<RwLockProcessPtr, ProcessU>,
    }

    /// Project a `KernelK` into its user-visible `KernelU`. This is the
    /// spec-level mapping that defines the user-view linearization point:
    /// at the moment the syscall declares it has reached its user-view
    /// linearization point, the user-visible state is exactly
    /// `kernel_k_to_kernel_u(kernel_k)`.
    pub open spec fn kernel_k_to_kernel_u(kernel_k: KernelK) -> KernelU {
        KernelU {
            cpu_array: Seq::new(
                kernel_k.cpu_array.view().len(),
                |i: int| {
                    let c = kernel_k.cpu_array.view()[i].view();
                    CpuU {
                        owning_container: c.owning_container,
                        state: c.state,
                        current_process: c.current_process,
                        current_thread: c.current_thread,
                    }
                },
            ),
            process_map: Map::new(
                |ptr: RwLockProcessPtr| kernel_k.process_map.dom().contains(ptr),
                |ptr: RwLockProcessPtr| {
                    let p = kernel_k.process_map.spec_index(ptr).view();
                    let p_ro = kernel_k.process_map.spec_index(ptr).view_rodata().view();
                    ProcessU {
                        pagetable: kernel_k.get_process_pagetable(ptr),
                        quota_4k: p.quota_4k,
                        quota_2m: p.quota_2m,
                        quota_1g: p.quota_1g,
                        parent: p_ro.parent,
                        children: p.children.view(),
                        depth: p_ro.depth,
                        uppertree_seq: p.uppertree_seq.view(),
                        subtree_set: p.subtree_set@,
                        owned_threads: p.owned_threads.view(),
                        killed: kernel_k.process_map.spec_index(ptr).being_killed(),
                    }
                },
            ),
        }
    }

    /// User-view delta predicate: `new_u` differs from `old_u` by exactly
    /// `process_map[process_ptr].quota_4k` increasing by `delta`. Every
    /// other field of `process_ptr`'s projection is preserved, every
    /// other process's projection is preserved, the process_map domain
    /// is preserved, and the cpu_array is preserved.
    ///
    /// Captures the user-visible effect of the success path of
    /// `syscall_alloc_quota_4k`.
    pub open spec fn kernel_u_only_process_quota_4k_changed(
        old_u: KernelU,
        new_u: KernelU,
        process_ptr: RwLockProcessPtr,
        delta: int,
    ) -> bool {
        &&& new_u.cpu_array == old_u.cpu_array
        &&& new_u.process_map.dom() == old_u.process_map.dom()
        &&& old_u.process_map.dom().contains(process_ptr)
        // The targeted process: only `quota_4k` increased by `delta`;
        // every other field preserved.
        &&& new_u.process_map[process_ptr].quota_4k as int
                == old_u.process_map[process_ptr].quota_4k as int + delta
        &&& new_u.process_map[process_ptr].pagetable      == old_u.process_map[process_ptr].pagetable
        &&& new_u.process_map[process_ptr].quota_2m       == old_u.process_map[process_ptr].quota_2m
        &&& new_u.process_map[process_ptr].quota_1g       == old_u.process_map[process_ptr].quota_1g
        &&& new_u.process_map[process_ptr].parent         == old_u.process_map[process_ptr].parent
        &&& new_u.process_map[process_ptr].children       == old_u.process_map[process_ptr].children
        &&& new_u.process_map[process_ptr].depth          == old_u.process_map[process_ptr].depth
        &&& new_u.process_map[process_ptr].uppertree_seq  == old_u.process_map[process_ptr].uppertree_seq
        &&& new_u.process_map[process_ptr].subtree_set    == old_u.process_map[process_ptr].subtree_set
        &&& new_u.process_map[process_ptr].owned_threads  == old_u.process_map[process_ptr].owned_threads
        &&& new_u.process_map[process_ptr].killed         == old_u.process_map[process_ptr].killed
        // Every other process: projection unchanged.
        &&& forall|p: RwLockProcessPtr|
            #![trigger new_u.process_map[p]]
            old_u.process_map.dom().contains(p) && p != process_ptr ==>
                new_u.process_map[p] == old_u.process_map[p]
    }

}
