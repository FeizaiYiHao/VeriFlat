use vstd::prelude::*;

use crate::*;
use super::mmap_4k_context::{
    mmap_4k_allocation_ready,
    mmap_4k_held_context,
};
use super::mmap_4k_create_entry_install::MissingPageTableLevel;

verus! {

#[derive(Clone, Copy)]
pub enum Mmap4kStructureBuild {
    Ready,
    NoQuota,
    InUse,
}

#[derive(Clone, Copy)]
enum Mmap4kDirectorySlot {
    Present,
    Missing,
    InUse,
}

impl<const TABLE_TYPE: PTType> PageTable<TABLE_TYPE> {
    fn mmap_4k_l4_directory_slot(
        &self,
        l4i: L4Index,
    ) -> (ret: Mmap4kDirectorySlot)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
        ensures
            ret is Present ==> self.spec_resolve_mapping_l4(l4i) is Some,
            ret is Missing ==> self.spec_resolve_mapping_l4(l4i) is None,
    {
        if self.get_entry_l4(l4i).is_some() {
            Mmap4kDirectorySlot::Present
        } else {
            Mmap4kDirectorySlot::Missing
        }
    }

    fn mmap_4k_l3_directory_slot(
        &self,
        l4i: L4Index,
        l3i: L3Index,
    ) -> (ret: Mmap4kDirectorySlot)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
        ensures
            ret is Present ==>
                self.spec_resolve_mapping_l3(l4i, l3i) is Some,
            ret is Missing ==> {
                &&& self.spec_resolve_mapping_l4(l4i) is Some
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is None
                &&& self.spec_resolve_mapping_1g_l3(l4i, l3i) is None
            },
    {
        let l4_entry = match self.get_entry_l4(l4i) {
            Some(entry) => entry,
            None => return Mmap4kDirectorySlot::InUse,
        };
        if self.get_entry_l3(l4i, l3i, &l4_entry).is_some() {
            return Mmap4kDirectorySlot::Present;
        }
        if self.get_entry_1g_l3(l4i, l3i, &l4_entry).is_some() {
            Mmap4kDirectorySlot::InUse
        } else {
            Mmap4kDirectorySlot::Missing
        }
    }

    fn mmap_4k_l2_directory_slot(
        &self,
        l4i: L4Index,
        l3i: L3Index,
        l2i: L2Index,
    ) -> (ret: Mmap4kDirectorySlot)
        requires
            self.wf(),
            self.kernel_l4_end <= l4i && pei_valid(l4i),
            pei_valid(l3i),
            pei_valid(l2i),
        ensures
            ret is Present ==>
                self.spec_resolve_mapping_l2(l4i, l3i, l2i) is Some,
            ret is Missing ==> {
                &&& self.spec_resolve_mapping_l3(l4i, l3i) is Some
                &&& self.spec_resolve_mapping_l2(l4i, l3i, l2i) is None
                &&& self.spec_resolve_mapping_2m_l2(l4i, l3i, l2i) is None
            },
    {
        let l4_entry = match self.get_entry_l4(l4i) {
            Some(entry) => entry,
            None => return Mmap4kDirectorySlot::InUse,
        };
        let l3_entry = match self.get_entry_l3(l4i, l3i, &l4_entry) {
            Some(entry) => entry,
            None => return Mmap4kDirectorySlot::InUse,
        };
        if self.get_entry_l2(l4i, l3i, l2i, &l3_entry).is_some() {
            return Mmap4kDirectorySlot::Present;
        }
        if self.get_entry_2m_l2(l4i, l3i, l2i, &l3_entry).is_some() {
            Mmap4kDirectorySlot::InUse
        } else {
            Mmap4kDirectorySlot::Missing
    }
}
}

impl KernelK {
    fn build_mmap_4k_l4_structure(
        &mut self,
        start_l4i: L4Index,
        end_l4i: L4Index,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Mmap4kStructureBuild)
        requires
            mmap_4k_held_context(
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            mmap_4k_allocation_ready(old(self), old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= start_l4i,
            pei_valid(start_l4i),
            pei_valid(end_l4i),
            start_l4i <= end_l4i,
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_allocation_ready(final(self), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(self).cpu_array.spec_index(cpu_id).view().locking_thread()
                == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
            final(self).cpu_array.lock_id_by_index(cpu_id)
                == old(self).cpu_array.lock_id_by_index(cpu_id),
            final(self).container_map.spec_index(container_ptr).locking_thread()
                == old(self).container_map.spec_index(container_ptr).locking_thread(),
            final(self).process_map.spec_index(process_ptr).locking_thread()
                == old(self).process_map.spec_index(process_ptr).locking_thread(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(self).pagetable_map.dom().contains(pagetable_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().user_view()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
    {
        let mut l4i = start_l4i;
        while l4i <= end_l4i
            invariant
                mmap_4k_held_context(
                    self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                    container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                    pagetable_lock_perm,
                ),
                steps.steps == old(steps).steps,
                steps.snap_shot == kernel_k_to_kernel_u(*self),
                mmap_4k_allocation_ready(self, &*lctx),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                self.cpu_array.spec_index(cpu_id).view().locking_thread()
                    == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
                self.cpu_array.lock_id_by_index(cpu_id)
                    == old(self).cpu_array.lock_id_by_index(cpu_id),
                self.container_map.spec_index(container_ptr).locking_thread()
                    == old(self).container_map.spec_index(container_ptr).locking_thread(),
                self.process_map.spec_index(process_ptr).locking_thread()
                    == old(self).process_map.spec_index(process_ptr).locking_thread(),
                self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                self.thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_clean(),
                self.pagetable_map.dom().contains(pagetable_ptr),
                self.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                self.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
                self.pagetable_map.spec_index(pagetable_ptr).view().user_view()
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
                old(self).pagetable_map.dom().contains(pagetable_ptr),
                old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    <= start_l4i,
                pei_valid(start_l4i),
                pei_valid(end_l4i),
                start_l4i <= l4i <= end_l4i + 1,
            decreases end_l4i + 1 - l4i,
        {
            proof {
                assert(
                    self.pagetable_map.perms_wf()
                        && self.pagetable_map.spec_index(pagetable_ptr).inv()
                ) by {
                    reveal(pagetable_perms_wf);
                };
            }
            let slot;
            {
                let pagetable = self.pagetable_map.borrow(
                    pagetable_ptr, Tracked(pagetable_lock_perm),
                );
                slot = pagetable.mmap_4k_l4_directory_slot(l4i);
            }
            match slot {
                Mmap4kDirectorySlot::Missing => {
                proof {
                    assert(
                        self.thread_map.perms_wf()
                            && self.thread_map.spec_index(thread_ptr).inv()
                    ) by {
                        reveal(thread_perms_wf);
                    };
                }
                let quota;
                {
                    let thread = self.thread_map.borrow(
                        thread_ptr, Tracked(thread_lock_perm),
                    );
                    quota = thread.quota_4k;
                }
                if quota == 0 {
                    return Mmap4kStructureBuild::NoQuota;
                }
                self.install_one_mmap_4k_directory_page(
                    MissingPageTableLevel::L4,
                    alloc_ptr_4k,
                    thread_ptr,
                    process_ptr,
                    container_ptr,
                    cpu_id,
                    pagetable_ptr,
                    (l4i, 0, 0),
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
                },
                Mmap4kDirectorySlot::Present => {},
                Mmap4kDirectorySlot::InUse => {
                    return Mmap4kStructureBuild::InUse;
                },
            }
            l4i = l4i + 1;
        }
        Mmap4kStructureBuild::Ready
    }
    fn build_mmap_4k_l3_structure(
        &mut self,
        start: (L4Index, L3Index, L2Index),
        end: (L4Index, L3Index, L2Index),
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Mmap4kStructureBuild)
        requires
            mmap_4k_held_context(
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            mmap_4k_allocation_ready(old(self), old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= start.0,
            pei_valid(start.0),
            pei_valid(start.1),
            pei_valid(start.2),
            pei_valid(end.0),
            pei_valid(end.1),
            pei_valid(end.2),
            spec_l4_structure_path_le(start, end),
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_allocation_ready(final(self), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(self).cpu_array.spec_index(cpu_id).view().locking_thread()
                == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
            final(self).cpu_array.lock_id_by_index(cpu_id)
                == old(self).cpu_array.lock_id_by_index(cpu_id),
            final(self).container_map.spec_index(container_ptr).locking_thread()
                == old(self).container_map.spec_index(container_ptr).locking_thread(),
            final(self).process_map.spec_index(process_ptr).locking_thread()
                == old(self).process_map.spec_index(process_ptr).locking_thread(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(self).pagetable_map.dom().contains(pagetable_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().user_view()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
    {
        let mut l4i = start.0;
        while l4i <= end.0
            invariant
                mmap_4k_held_context(
                    self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                    container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                    pagetable_lock_perm,
                ),
                steps.steps == old(steps).steps,
                steps.snap_shot == kernel_k_to_kernel_u(*self),
                mmap_4k_allocation_ready(self, &*lctx),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                self.cpu_array.spec_index(cpu_id).view().locking_thread()
                    == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
                self.cpu_array.lock_id_by_index(cpu_id)
                    == old(self).cpu_array.lock_id_by_index(cpu_id),
                self.container_map.spec_index(container_ptr).locking_thread()
                    == old(self).container_map.spec_index(container_ptr).locking_thread(),
                self.process_map.spec_index(process_ptr).locking_thread()
                    == old(self).process_map.spec_index(process_ptr).locking_thread(),
                self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                self.thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_clean(),
                self.pagetable_map.dom().contains(pagetable_ptr),
                self.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                self.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
                self.pagetable_map.spec_index(pagetable_ptr).view().user_view()
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
                old(self).pagetable_map.dom().contains(pagetable_ptr),
                old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    <= start.0,
                pei_valid(start.0),
                pei_valid(start.1),
                pei_valid(start.2),
                pei_valid(end.0),
                pei_valid(end.1),
                pei_valid(end.2),
                spec_l4_structure_path_le(start, end),
                start.0 <= l4i <= end.0 + 1,
            decreases end.0 + 1 - l4i,
        {
            let l3_start = if l4i == start.0 { start.1 } else { 0 };
            let l3_end = if l4i == end.0 { end.1 } else { 511 };
            let mut l3i = l3_start;
            while l3i <= l3_end
                invariant
                    mmap_4k_held_context(
                        self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                        container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                        pagetable_lock_perm,
                    ),
                    steps.steps == old(steps).steps,
                    steps.snap_shot == kernel_k_to_kernel_u(*self),
                    mmap_4k_allocation_ready(self, &*lctx),
                    lctx.lock_id_set() == old(lctx).lock_id_set(),
                    lctx.lock_id_set() == old(lctx).lock_id_set(),
                    self.cpu_array.spec_index(cpu_id).view().locking_thread()
                        == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
                    self.cpu_array.lock_id_by_index(cpu_id)
                        == old(self).cpu_array.lock_id_by_index(cpu_id),
                    self.container_map.spec_index(container_ptr).locking_thread()
                        == old(self).container_map.spec_index(container_ptr).locking_thread(),
                    self.process_map.spec_index(process_ptr).locking_thread()
                        == old(self).process_map.spec_index(process_ptr).locking_thread(),
                    self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                    self.thread_map.spec_index(thread_ptr).view()
                        .free_quota_pending_clean(),
                    self.pagetable_map.dom().contains(pagetable_ptr),
                    self.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                    self.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                        == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
                    self.pagetable_map.spec_index(pagetable_ptr).view().user_view()
                        == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
                    self.pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                        =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
                    self.pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                        =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
                    self.pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                        =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
                    old(self).pagetable_map.dom().contains(pagetable_ptr),
                    old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                        <= start.0,
                    pei_valid(start.0),
                    pei_valid(start.1),
                    pei_valid(start.2),
                    pei_valid(end.0),
                    pei_valid(end.1),
                    pei_valid(end.2),
                    spec_l4_structure_path_le(start, end),
                    start.0 <= l4i <= end.0,
                    l3_start <= l3i <= l3_end + 1,
                    l3_start <= l3_end,
                    pei_valid(l3_start),
                    pei_valid(l3_end),
                decreases l3_end + 1 - l3i,
            {
                proof {
                    assert(
                        self.pagetable_map.perms_wf()
                            && self.pagetable_map.spec_index(pagetable_ptr).inv()
                    ) by {
                        reveal(pagetable_perms_wf);
                    };
                }
                let slot;
                {
                    let pagetable = self.pagetable_map.borrow(
                        pagetable_ptr, Tracked(pagetable_lock_perm),
                    );
                    slot = pagetable.mmap_4k_l3_directory_slot(l4i, l3i);
                }
                match slot {
                    Mmap4kDirectorySlot::Present => {},
                    Mmap4kDirectorySlot::InUse => {
                        return Mmap4kStructureBuild::InUse;
                    },
                    Mmap4kDirectorySlot::Missing => {
                        proof {
                            assert(
                                self.thread_map.perms_wf()
                                    && self.thread_map.spec_index(thread_ptr).inv()
                            ) by {
                                reveal(thread_perms_wf);
                            };
                        }
                        let quota;
                        {
                            let thread = self.thread_map.borrow(
                                thread_ptr, Tracked(thread_lock_perm),
                            );
                            quota = thread.quota_4k;
                        }
                        if quota == 0 {
                            return Mmap4kStructureBuild::NoQuota;
                        }
                        self.install_one_mmap_4k_directory_page(
                            MissingPageTableLevel::L3,
                            alloc_ptr_4k,
                            thread_ptr,
                            process_ptr,
                            container_ptr,
                            cpu_id,
                            pagetable_ptr,
                            (l4i, l3i, 0),
                            Tracked(&mut *lctx),
                            Tracked(&mut *steps),
                            Tracked(thread_lock_perm),
                            Tracked(pagetable_lock_perm),
                        );
                    },
                }
                l3i = l3i + 1;
            }
            l4i = l4i + 1;
        }
        Mmap4kStructureBuild::Ready
    }
    fn build_mmap_4k_l2_structure(
        &mut self,
        start: (L4Index, L3Index, L2Index),
        end: (L4Index, L3Index, L2Index),
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Mmap4kStructureBuild)
        requires
            mmap_4k_held_context(
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            mmap_4k_allocation_ready(old(self), old(lctx)),
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= start.0,
            pei_valid(start.0),
            pei_valid(start.1),
            pei_valid(start.2),
            pei_valid(end.0),
            pei_valid(end.1),
            pei_valid(end.2),
            spec_l4_structure_path_le(start, end),
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_allocation_ready(final(self), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(self).cpu_array.spec_index(cpu_id).view().locking_thread()
                == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
            final(self).cpu_array.lock_id_by_index(cpu_id)
                == old(self).cpu_array.lock_id_by_index(cpu_id),
            final(self).container_map.spec_index(container_ptr).locking_thread()
                == old(self).container_map.spec_index(container_ptr).locking_thread(),
            final(self).process_map.spec_index(process_ptr).locking_thread()
                == old(self).process_map.spec_index(process_ptr).locking_thread(),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            final(self).pagetable_map.dom().contains(pagetable_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().user_view()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
    {
        let mut l4i = start.0;
        while l4i <= end.0
            invariant
                mmap_4k_held_context(
                    self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                    container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                    pagetable_lock_perm,
                ),
                steps.steps == old(steps).steps,
                steps.snap_shot == kernel_k_to_kernel_u(*self),
                mmap_4k_allocation_ready(self, &*lctx),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                lctx.lock_id_set() == old(lctx).lock_id_set(),
                self.cpu_array.spec_index(cpu_id).view().locking_thread()
                    == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
                self.cpu_array.lock_id_by_index(cpu_id)
                    == old(self).cpu_array.lock_id_by_index(cpu_id),
                self.container_map.spec_index(container_ptr).locking_thread()
                    == old(self).container_map.spec_index(container_ptr).locking_thread(),
                self.process_map.spec_index(process_ptr).locking_thread()
                    == old(self).process_map.spec_index(process_ptr).locking_thread(),
                self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                self.thread_map.spec_index(thread_ptr).view()
                    .free_quota_pending_clean(),
                self.pagetable_map.dom().contains(pagetable_ptr),
                self.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                self.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
                self.pagetable_map.spec_index(pagetable_ptr).view().user_view()
                    == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
                self.pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                    =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
                old(self).pagetable_map.dom().contains(pagetable_ptr),
                old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                    <= start.0,
                pei_valid(start.0),
                pei_valid(start.1),
                pei_valid(start.2),
                pei_valid(end.0),
                pei_valid(end.1),
                pei_valid(end.2),
                spec_l4_structure_path_le(start, end),
                start.0 <= l4i <= end.0 + 1,
            decreases end.0 + 1 - l4i,
        {
            let l3_start = if l4i == start.0 { start.1 } else { 0 };
            let l3_end = if l4i == end.0 { end.1 } else { 511 };
            let mut l3i = l3_start;
            while l3i <= l3_end
                invariant
                    mmap_4k_held_context(
                        self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                        container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                        pagetable_lock_perm,
                    ),
                    steps.steps == old(steps).steps,
                    steps.snap_shot == kernel_k_to_kernel_u(*self),
                    mmap_4k_allocation_ready(self, &*lctx),
                    lctx.lock_id_set() == old(lctx).lock_id_set(),
                    lctx.lock_id_set() == old(lctx).lock_id_set(),
                    self.cpu_array.spec_index(cpu_id).view().locking_thread()
                        == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
                    self.cpu_array.lock_id_by_index(cpu_id)
                        == old(self).cpu_array.lock_id_by_index(cpu_id),
                    self.container_map.spec_index(container_ptr).locking_thread()
                        == old(self).container_map.spec_index(container_ptr).locking_thread(),
                    self.process_map.spec_index(process_ptr).locking_thread()
                        == old(self).process_map.spec_index(process_ptr).locking_thread(),
                    self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                    self.thread_map.spec_index(thread_ptr).view()
                        .free_quota_pending_clean(),
                    self.pagetable_map.dom().contains(pagetable_ptr),
                    self.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                    self.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                        == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
                    self.pagetable_map.spec_index(pagetable_ptr).view().user_view()
                        == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
                    self.pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                        =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
                    self.pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                        =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
                    self.pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                        =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
                    old(self).pagetable_map.dom().contains(pagetable_ptr),
                    old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                        <= start.0,
                    pei_valid(start.0),
                    pei_valid(start.1),
                    pei_valid(start.2),
                    pei_valid(end.0),
                    pei_valid(end.1),
                    pei_valid(end.2),
                    spec_l4_structure_path_le(start, end),
                    start.0 <= l4i <= end.0,
                    l3_start <= l3i <= l3_end + 1,
                    l3_start <= l3_end,
                    pei_valid(l3_start),
                    pei_valid(l3_end),
                decreases l3_end + 1 - l3i,
            {
                let l2_start = if l4i == start.0 && l3i == start.1 {
                    start.2
                } else {
                    0
                };
                let l2_end = if l4i == end.0 && l3i == end.1 {
                    end.2
                } else {
                    511
                };
                let mut l2i = l2_start;
                while l2i <= l2_end
                    invariant
                        mmap_4k_held_context(
                            self, &*lctx, alloc_ptr_4k, thread_ptr, process_ptr,
                            container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                            pagetable_lock_perm,
                        ),
                        steps.steps == old(steps).steps,
                        steps.snap_shot == kernel_k_to_kernel_u(*self),
                        mmap_4k_allocation_ready(self, &*lctx),
                        lctx.lock_id_set() == old(lctx).lock_id_set(),
                        lctx.lock_id_set() == old(lctx).lock_id_set(),
                        self.cpu_array.spec_index(cpu_id).view().locking_thread()
                            == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
                        self.cpu_array.lock_id_by_index(cpu_id)
                            == old(self).cpu_array.lock_id_by_index(cpu_id),
                        self.container_map.spec_index(container_ptr).locking_thread()
                            == old(self).container_map.spec_index(container_ptr).locking_thread(),
                        self.process_map.spec_index(process_ptr).locking_thread()
                            == old(self).process_map.spec_index(process_ptr).locking_thread(),
                        self.thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
                        self.thread_map.spec_index(thread_ptr).view()
                            .free_quota_pending_clean(),
                        self.pagetable_map.dom().contains(pagetable_ptr),
                        self.pagetable_map.spec_index(pagetable_ptr).view().wf(),
                        self.pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                            == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
                        self.pagetable_map.spec_index(pagetable_ptr).view().user_view()
                            == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
                        self.pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                            =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
                        self.pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                            =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
                        self.pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                            =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
                        old(self).pagetable_map.dom().contains(pagetable_ptr),
                        old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                            <= start.0,
                        pei_valid(start.0),
                        pei_valid(start.1),
                        pei_valid(start.2),
                        pei_valid(end.0),
                        pei_valid(end.1),
                        pei_valid(end.2),
                        spec_l4_structure_path_le(start, end),
                        start.0 <= l4i <= end.0,
                        l3_start <= l3i <= l3_end,
                        pei_valid(l3i),
                        l2_start <= l2i <= l2_end + 1,
                        l2_start <= l2_end,
                        pei_valid(l2_start),
                        pei_valid(l2_end),
                    decreases l2_end + 1 - l2i,
                {
                    proof {
                        assert(
                            self.pagetable_map.perms_wf()
                                && self.pagetable_map.spec_index(pagetable_ptr).inv()
                        ) by {
                            reveal(pagetable_perms_wf);
                        };
                    }
                    let slot;
                    {
                        let pagetable = self.pagetable_map.borrow(
                            pagetable_ptr, Tracked(pagetable_lock_perm),
                        );
                        slot = pagetable.mmap_4k_l2_directory_slot(
                            l4i, l3i, l2i,
                        );
                    }
                    match slot {
                        Mmap4kDirectorySlot::Present => {},
                        Mmap4kDirectorySlot::InUse => {
                            return Mmap4kStructureBuild::InUse;
                        },
                        Mmap4kDirectorySlot::Missing => {
                            proof {
                                assert(
                                    self.thread_map.perms_wf()
                                        && self.thread_map.spec_index(thread_ptr).inv()
                                ) by {
                                    reveal(thread_perms_wf);
                                };
                            }
                            let quota;
                            {
                                let thread = self.thread_map.borrow(
                                    thread_ptr, Tracked(thread_lock_perm),
                                );
                                quota = thread.quota_4k;
                            }
                            if quota == 0 {
                                return Mmap4kStructureBuild::NoQuota;
                            }
                            self.install_one_mmap_4k_directory_page(
                                MissingPageTableLevel::L2,
                                alloc_ptr_4k,
                                thread_ptr,
                                process_ptr,
                                container_ptr,
                                cpu_id,
                                pagetable_ptr,
                                (l4i, l3i, l2i),
                                Tracked(&mut *lctx),
                                Tracked(&mut *steps),
                                Tracked(thread_lock_perm),
                                Tracked(pagetable_lock_perm),
                            );
                        },
                    }
                    l2i = l2i + 1;
                }
                l3i = l3i + 1;
            }
            l4i = l4i + 1;
        }
        Mmap4kStructureBuild::Ready
    }
    pub(super) fn mmap_4k_build_structure(
        &mut self,
        range: &VaRange4K,
        alloc_ptr_4k: RwLockPageAllocatorPtr,
        thread_ptr: RwLockThreadPtr,
        process_ptr: RwLockProcessPtr,
        container_ptr: RwLockContainerPtr,
        cpu_id: CpuId,
        pagetable_ptr: RwLockPageTableRoot,
        Tracked(lctx): Tracked<&mut LocalContext>,
        Tracked(steps): Tracked<&mut KernelSteps>,
        Tracked(thread_lock_perm): Tracked<&LockPerm>,
        Tracked(pagetable_lock_perm): Tracked<&LockPerm>,
    ) -> (ret: Mmap4kStructureBuild)
        requires
            mmap_4k_held_context(
                old(self), old(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            old(steps).snap_shot == kernel_k_to_kernel_u(*old(self)),
            mmap_4k_allocation_ready(old(self), old(lctx)),
            range.wf(),
            range.len > 0,
            range.len <= usize::MAX / 4usize,
            old(self).thread_map.dom().contains(thread_ptr),
            old(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            old(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            old(self).thread_map.spec_index(thread_ptr).view().quota_4k
                >= 4 * range.len,
            old(self).pagetable_map.dom().contains(pagetable_ptr),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                <= spec_v2l4index(range.start),
            old(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_mapping_4k_va_range_empty(
                    range.start,
                    range.view().spec_index((range.len - 1) as int),
                ),
        ensures
            mmap_4k_held_context(
                final(self), final(lctx), alloc_ptr_4k, thread_ptr, process_ptr,
                container_ptr, cpu_id, pagetable_ptr, thread_lock_perm,
                pagetable_lock_perm,
            ),
            final(steps).steps == old(steps).steps,
            final(steps).snap_shot == kernel_k_to_kernel_u(*final(self)),
            mmap_4k_allocation_ready(final(self), final(lctx)),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(lctx).lock_id_set() == old(lctx).lock_id_set(),
            final(self).cpu_array.spec_index(cpu_id).view().locking_thread()
                == old(self).cpu_array.spec_index(cpu_id).view().locking_thread(),
            final(self).cpu_array.lock_id_by_index(cpu_id)
                == old(self).cpu_array.lock_id_by_index(cpu_id),
            final(self).container_map.spec_index(container_ptr).locking_thread()
                == old(self).container_map.spec_index(container_ptr).locking_thread(),
            final(self).process_map.spec_index(process_ptr).locking_thread()
                == old(self).process_map.spec_index(process_ptr).locking_thread(),
            final(self).thread_map.dom().contains(thread_ptr),
            final(self).thread_map.spec_index(thread_ptr).view().temp_alloc_clean(),
            final(self).thread_map.spec_index(thread_ptr).view()
                .free_quota_pending_clean(),
            ret is Ready ==> final(self).thread_map.spec_index(thread_ptr)
                .view().quota_4k >= range.len,
            final(self).pagetable_map.dom().contains(pagetable_ptr),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().wf(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().kernel_l4_end,
            final(self).pagetable_map.spec_index(pagetable_ptr).view().user_view()
                == old(self).pagetable_map.spec_index(pagetable_ptr).view().user_view(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_4k(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_2m(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g()
                =~= old(self).pagetable_map.spec_index(pagetable_ptr).view().mapping_1g(),
            final(self).pagetable_map.spec_index(pagetable_ptr).view()
                .spec_mapping_4k_va_range_empty(
                    range.start,
                    range.view().spec_index((range.len - 1) as int),
                ),
            ret is Ready ==> final(self).pagetable_map.spec_index(pagetable_ptr)
                .view().spec_va_range_structure_present(
                    range.start,
                    range.view().spec_index((range.len - 1) as int),
                ),
    {
        let range_len = range.len;
        let range_start = range.start;
        let end_i = range_len - 1;
        let end_va = range.index(end_i);
        assert(end_va == spec_va_add_range(range_start, end_i)) by {
            range.va_range_lemma();
        };
        assert(range_start <= end_va) by (bit_vector)
            requires
                range_len > 0,
                range_len <= usize::MAX / 4096usize,
                range_start < usize::MAX - range_len * 4096usize,
                end_i == range_len - 1,
                end_va == (range_start + end_i * 4096usize) as usize,
        ;
        let start_indices = va2index(range_start);
        let end_indices = va2index(end_va);
        assert(spec_l4_structure_path_le(
            (
                spec_v2l4index(range_start),
                spec_v2l3index(range_start),
                spec_v2l2index(range_start),
            ),
            (
                spec_v2l4index(end_va),
                spec_v2l3index(end_va),
                spec_v2l2index(end_va),
            ),
        )) by (bit_vector)
            requires
                spec_va_4k_valid(range_start),
                spec_va_4k_valid(end_va),
                range_start <= end_va,
        ;
        assert(spec_v2l4index(range_start) <= spec_v2l4index(end_va))
            by (bit_vector)
            requires
                spec_va_4k_valid(range_start),
                spec_va_4k_valid(end_va),
                range_start <= end_va,
        ;
        let l4_result = self.build_mmap_4k_l4_structure(
            start_indices.0,
            end_indices.0,
            alloc_ptr_4k,
            thread_ptr,
            process_ptr,
            container_ptr,
            cpu_id,
            pagetable_ptr,
            Tracked(&mut *lctx),
            Tracked(&mut *steps),
            Tracked(thread_lock_perm),
            Tracked(pagetable_lock_perm),
        );
        let result;
        match l4_result {
            Mmap4kStructureBuild::NoQuota => {
                result = Mmap4kStructureBuild::NoQuota;
            },
            Mmap4kStructureBuild::InUse => {
                result = Mmap4kStructureBuild::InUse;
            },
            Mmap4kStructureBuild::Ready => {
                let l3_result = self.build_mmap_4k_l3_structure(
                    (start_indices.0, start_indices.1, start_indices.2),
                    (end_indices.0, end_indices.1, end_indices.2),
                    alloc_ptr_4k,
                    thread_ptr,
                    process_ptr,
                    container_ptr,
                    cpu_id,
                    pagetable_ptr,
                    Tracked(&mut *lctx),
                    Tracked(&mut *steps),
                    Tracked(thread_lock_perm),
                    Tracked(pagetable_lock_perm),
                );
                match l3_result {
                    Mmap4kStructureBuild::NoQuota => {
                        result = Mmap4kStructureBuild::NoQuota;
                    },
                    Mmap4kStructureBuild::InUse => {
                        result = Mmap4kStructureBuild::InUse;
                    },
                    Mmap4kStructureBuild::Ready => {
                        let l2_result = self.build_mmap_4k_l2_structure(
                            (start_indices.0, start_indices.1, start_indices.2),
                            (end_indices.0, end_indices.1, end_indices.2),
                            alloc_ptr_4k,
                            thread_ptr,
                            process_ptr,
                            container_ptr,
                            cpu_id,
                            pagetable_ptr,
                            Tracked(&mut *lctx),
                            Tracked(&mut *steps),
                            Tracked(thread_lock_perm),
                            Tracked(pagetable_lock_perm),
                        );
                        match l2_result {
                            Mmap4kStructureBuild::NoQuota => {
                                result = Mmap4kStructureBuild::NoQuota;
                            },
                            Mmap4kStructureBuild::InUse => {
                                result = Mmap4kStructureBuild::InUse;
                            },
                            Mmap4kStructureBuild::Ready => {
                                proof {
                                    assert(
                                        self.pagetable_map.perms_wf()
                                            && self.pagetable_map.spec_index(
                                                pagetable_ptr,
                                            ).inv()
                                    ) by {
                                        reveal(pagetable_perms_wf);
                                    };
                                }
                                let prepared;
                                {
                                    let pagetable = self.pagetable_map.borrow(
                                        pagetable_ptr,
                                        Tracked(pagetable_lock_perm),
                                    );
                                    prepared = pagetable.va_range_structure_present(
                                        range.start, end_va,
                                    );
                                }
                                if prepared {
                                    proof {
                                        assert(
                                            self.thread_map.perms_wf()
                                                && self.thread_map.spec_index(
                                                    thread_ptr,
                                                ).inv()
                                        ) by {
                                            reveal(thread_perms_wf);
                                        };
                                    }
                                    let quota;
                                    {
                                        let thread = self.thread_map.borrow(
                                            thread_ptr,
                                            Tracked(thread_lock_perm),
                                        );
                                        quota = thread.quota_4k;
                                    }
                                    if quota >= range_len {
                                        result = Mmap4kStructureBuild::Ready;
                                    } else {
                                        result = Mmap4kStructureBuild::NoQuota;
                                    }
                                } else {
                                    result = Mmap4kStructureBuild::InUse;
                                }
                            },
                        }
                    },
                }
            },
        }
        proof {
            assert(self.pagetable_map.spec_index(pagetable_ptr).view()
                .spec_mapping_4k_va_range_empty(range.start, end_va)) by {
                reveal(PageTable::spec_mapping_4k_va_range_empty);
            };
        }
        result
    }
}

} // verus!
