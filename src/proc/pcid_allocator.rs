use vstd::prelude::*;
verus! {

use crate::*;

/// PCID allocator payload. Each of the 4096 PCIDs has one machine-word
/// reference counter; ownership and lock-ordering metadata are ghost state.
/// The allocator and its generic `RwLock` header are backed by one 2MiB page.
#[repr(C)]
pub struct PcidAllocator {
    pub owning_container: Ghost<RwLockContainerPtr>,
    pub container_depth: Ghost<usize>,
    pub ref_counters: Array<usize, PCID_MAX>,
    pub id_to_proc: Ghost<Seq<Set<RwLockProcessPtr>>>,
}

impl PcidAllocator {
    pub open spec fn wf(&self) -> bool {
        &&& self.ref_counters.wf()
        &&& self.id_to_proc.view().len() == PCID_MAX
        &&& forall|id: usize|
            #![trigger self.ref_counters.spec_index(id)]
            #![trigger self.id_to_proc.view().spec_index(id as int)]
            usize_in_range::<PCID_MAX>(id)
            ==>
            self.ref_counters.spec_index(id)
                == self.id_to_proc.view().spec_index(id as int).len()
    }

    pub open spec fn process_is_unallocated(&self, process_ptr: RwLockProcessPtr) -> bool {
        forall|id: usize|
            #![trigger self.id_to_proc.view().spec_index(id as int).contains(process_ptr)]
            usize_in_range::<PCID_MAX>(id)
            ==>
            self.id_to_proc.view().spec_index(id as int).contains(process_ptr) == false
    }

    pub open spec fn alloc_ensures(
        &self,
        old: &Self,
        process_ptr: RwLockProcessPtr,
        id: usize,
    ) -> bool {
        &&& usize_in_range::<PCID_MAX>(id)
        &&& old.process_is_unallocated(process_ptr)
        &&& old.ref_counters.spec_index(id) < usize::MAX
        &&& self.owning_container.view() == old.owning_container.view()
        &&& self.container_depth.view() == old.container_depth.view()
        &&& self.ref_counters.view()
            =~= old.ref_counters.view().update(
                id as int,
                (old.ref_counters.spec_index(id) + 1) as usize,
            )
        &&& self.id_to_proc.view()
            =~= old.id_to_proc.view().update(
                id as int,
                old.id_to_proc.view().spec_index(id as int).insert(process_ptr),
            )
    }

    pub fn alloc(&mut self, id: usize, process_ptr: RwLockProcessPtr)
        requires
            old(self).wf(),
            usize_in_range::<PCID_MAX>(id),
            old(self).process_is_unallocated(process_ptr),
            old(self).ref_counters.spec_index(id) < usize::MAX,
        ensures
            final(self).wf(),
            final(self).alloc_ensures(old(self), process_ptr, id),
    {
        let old_counter = *self.ref_counters.get(id);
        self.ref_counters.set(id, old_counter + 1);
        self.id_to_proc = Ghost(
            self.id_to_proc.view().update(
                id as int,
                self.id_to_proc.view().spec_index(id as int).insert(process_ptr),
            ),
        );
        proof {
            vstd::set::lemma_set_insert_len(
                old(self).id_to_proc.view().spec_index(id as int),
                process_ptr,
            );
            assert forall|other_id: usize|
                #![trigger self.ref_counters.spec_index(other_id)]
                #![trigger self.id_to_proc.view().spec_index(other_id as int)]
                usize_in_range::<PCID_MAX>(other_id)
                implies
                self.ref_counters.spec_index(other_id)
                    == self.id_to_proc.view().spec_index(other_id as int).len()
            by {
                if other_id != id {
                    assert(self.ref_counters.spec_index(other_id)
                        == old(self).ref_counters.spec_index(other_id));
                    assert(self.id_to_proc.view().spec_index(other_id as int)
                        == old(self).id_to_proc.view().spec_index(other_id as int));
                }
            };
        }
    }
}

impl LockInvTrait for PcidAllocator {
    open spec fn inv(&self) -> bool {
        self.wf()
    }
}

impl LockMajorTrait for PcidAllocator {
    open spec fn lock_major_1(&self) -> LockMajorId {
        PCID_ALLOCATOR_LOCK_MAJOR
    }

    open spec fn lock_major_2(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_3(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_default(&self) -> LockMajorId {
        233
    }

    open spec fn lock_major_1_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_2_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_3_predicate(&self) -> bool {
        true
    }

    open spec fn lock_major_default_predicate(&self) -> bool {
        true
    }
}

impl LockOwnerIdTrait for PcidAllocator {
    open spec fn container_depth(&self) -> LockOwnerId {
        LockOwnerId::Some(self.container_depth.view())
    }

    open spec fn process_depth(&self) -> LockOwnerId {
        LockOwnerId::NotApp
    }
}

impl LockUserVisibilityTrait for PcidAllocator {
    open spec fn is_user_visible() -> bool {
        false
    }
}

} // verus!

const ASSERT_PCID_ALLOCATOR_PAYLOAD_SIZE: [(); PCID_MAX * core::mem::size_of::<usize>()] =
    [(); core::mem::size_of::<PcidAllocator>()];
const ASSERT_PCID_ALLOCATOR_LOCK_FITS_2M: [(); 1] = [();
    (core::mem::size_of::<RwLock<
        PcidAllocator,
        (),
        (),
        (),
        PCID_ALLOCATOR_HAS_KILL_STATE,
    >>() <= PAGE_SZ_2M) as usize
];
