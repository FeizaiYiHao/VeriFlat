use vstd::prelude::*;

use crate::*;

verus! {

/// Result of the two checks that precede PageTable construction for mmap(4K).
#[derive(Clone, Copy)]
pub enum Mmap4kPrecheck {
    Ready,
    NoQuota,
    Invalid,
    InUse,
}


    /// Check the conservative `4 * range.len` quota bound first, then check
    /// the entire inclusive VA interval for existing abstract 4K mappings.
    /// No kernel or LocalContext state changes.
    pub(super) fn mmap_4k_precheck(
        kernel: &KernelK,
        range: &VaRange4K,
        thread_ptr: RwLockThreadPtr,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&LocalContext>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Mmap4kPrecheck)
        requires
            kernel.inv(),
            range.wf(),
            range.len > 0,
            range.len <= usize::MAX / 4usize,
            kernel.thread_map.dom().contains(thread_ptr),
            kernel.thread_map.spec_index(thread_ptr).wlocked_by(lctx),
            thread_lock_perm.state() is WriteLock,
            thread_lock_perm.thread_id() == lctx.thread_id(),
            thread_lock_perm.lock_id()
                == kernel.thread_map.spec_index(thread_ptr)
                    .locking_thread()->Write_lock_id,
            kernel.pagetable_map.dom().contains(pagetable_ptr),
            kernel.pagetable_map.spec_index(pagetable_ptr).wlocked_by(lctx),
            pagetable_lock_perm.state() is WriteLock,
            pagetable_lock_perm.thread_id() == lctx.thread_id(),
            pagetable_lock_perm.lock_id()
                == kernel.pagetable_map.spec_index(pagetable_ptr)
                    .locking_thread()->Write_lock_id,
        ensures
            ret is Ready ==> {
                let end_va = range.view().spec_index((range.len - 1) as int);
                &&& kernel.thread_map.spec_index(thread_ptr).view().quota_4k
                    >= 4 * range.len
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    <= spec_va2index(range.start).0
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_mapping_4k_va_range_empty(range.start, end_va)
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                    .spec_mapping_4k_va_range_buildable(range)
            },
            ret is NoQuota ==>
                kernel.thread_map.spec_index(thread_ptr).view().quota_4k
                    < 4 * range.len,
            ret is Invalid ==> {
                &&& kernel.thread_map.spec_index(thread_ptr).view().quota_4k
                    >= 4 * range.len
                &&& spec_va2index(range.start).0
                    < kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .kernel_l4_end
            },
            ret is InUse ==> {
                let end_va = range.view().spec_index((range.len - 1) as int);
                &&& kernel.thread_map.spec_index(thread_ptr).view().quota_4k
                    >= 4 * range.len
                &&& kernel.pagetable_map.spec_index(pagetable_ptr).view()
                    .kernel_l4_end <= spec_va2index(range.start).0
                &&& (
                    !kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_mapping_4k_range_empty(
                            spec_va2index(range.start), spec_va2index(end_va),
                        )
                    || !kernel.pagetable_map.spec_index(pagetable_ptr).view()
                        .spec_mapping_4k_va_range_buildable(range)
                )
            },
    {
        let range_len = range.len;
        let range_start = range.start;
        let credit = 4usize * range_len;
        proof {
            assert(
                kernel.thread_map.perms_wf()
                    && kernel.thread_map.spec_index(thread_ptr).inv()
            ) by {
                reveal(thread_perms_wf);
            };
        }
        let thread = kernel.thread_map.borrow(
            thread_ptr,
            Tracked(thread_lock_perm),
        );
        if thread.quota_4k < credit {
            return Mmap4kPrecheck::NoQuota;
        }

        let end_index = range_len - 1;
        let end_va = range.index(end_index);
        assert(end_va == spec_va_add_range(range_start, end_index)) by {
            range.va_range_lemma();
        };
        assert(range_start <= end_va) by (bit_vector)
            requires
                range_len > 0,
                range_len <= usize::MAX / 4096usize,
                range_start < usize::MAX - range_len * 4096usize,
                end_index == range_len - 1,
                end_va == (range_start + end_index * 4096usize) as usize,
        ;
        let start_indices = va2index(range_start);
        proof {
            assert(
                kernel.pagetable_map.perms_wf()
                    && kernel.pagetable_map.spec_index(pagetable_ptr).inv()
            ) by {
                reveal(pagetable_perms_wf);
            };
        }
        let pagetable = kernel.pagetable_map.borrow(
            pagetable_ptr,
            Tracked(pagetable_lock_perm),
        );
        if start_indices.0 < pagetable.kernel_l4_end {
            return Mmap4kPrecheck::Invalid;
        }
        if !pagetable.mapping_4k_va_range_empty(range_start, end_va) {
            return Mmap4kPrecheck::InUse;
        }
        if !pagetable.mapping_4k_va_range_buildable(range) {
            return Mmap4kPrecheck::InUse;
        }
        Mmap4kPrecheck::Ready
    }


}
