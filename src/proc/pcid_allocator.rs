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
    pub fn new_boot_root(
        owning_container: RwLockContainerPtr,
        root_process: RwLockProcessPtr,
    ) -> (ret: Self)
        ensures
            ret.inv(),
            ret.owning_container.view() == owning_container,
            ret.container_depth.view() == 0,
            ret.ref_counters.spec_index(1) == 1,
            ret.id_to_proc.view().spec_index(1)
                =~= set![root_process],
            forall|id: Pcid|
                #![trigger ret.ref_counters.spec_index(id)]
                pcid_valid(id)
                && id != 1
                ==> ret.ref_counters.spec_index(id) == 0,
            forall|id: Pcid|
                #![trigger ret.id_to_proc.view()
                    .spec_index(id as int)]
                pcid_valid(id)
                && id != 1
                ==> ret.id_to_proc.view()
                    .spec_index(id as int).is_empty(),
    {
        let mut ret = Self::new_empty(owning_container, 0);
        assert(ret.process_is_unallocated(root_process)) by {
        }
        ret.alloc(1, root_process);
        ret
    }

    pub fn new_empty(owning_container: RwLockContainerPtr, container_depth: usize) -> (ret: Self)
        ensures
            ret.inv(),
            ret.owning_container.view() == owning_container,
            ret.container_depth.view() == container_depth,
            ret.id_to_proc.view() == Seq::new(PCID_MAX as nat, |_id: int| Set::<RwLockProcessPtr>::empty()),
            forall|id: Pcid| #![auto] pcid_valid(id) ==> ret.ref_counters.spec_index(id) == 0,
    {
        Self {
            owning_container: Ghost(owning_container),
            container_depth: Ghost(container_depth),
            ref_counters: Array::new_with_init_value(0),
            id_to_proc: Ghost(Seq::new(PCID_MAX as nat, |_id: int| Set::<RwLockProcessPtr>::empty())),
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.ref_counters.wf()
        &&& self.id_to_proc.view().len() == PCID_MAX
        &&& self.ref_counters.spec_index(KERNEL_DEFAULT_PCID) == 0
        &&& self.id_to_proc.view().spec_index(KERNEL_DEFAULT_PCID as int).is_empty()
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

    pub open spec fn pcid_is_free(&self, id: Pcid) -> bool {
        &&& usize_in_range::<PCID_MAX>(id)
        &&& id != KERNEL_DEFAULT_PCID
        &&& self.ref_counters.spec_index(id) == 0
    }

    pub fn find_lowest_free_nonzero(&self) -> (ret: Option<Pcid>)
        requires
            self.wf(),
        ensures
            ret is Some ==> self.pcid_is_free(ret->Some_0),
            ret is Some ==> forall|id: Pcid|
                #![trigger self.ref_counters.spec_index(id)]
                KERNEL_DEFAULT_PCID < id < ret->Some_0 ==> !self.pcid_is_free(id),
            ret is None ==> forall|id: Pcid|
                #![trigger self.ref_counters.spec_index(id)]
                usize_in_range::<PCID_MAX>(id) ==> !self.pcid_is_free(id),
    {
        let mut id = KERNEL_DEFAULT_PCID + 1;
        while id < PCID_MAX
            invariant
                self.wf(),
                KERNEL_DEFAULT_PCID < id <= PCID_MAX,
                forall|candidate: Pcid|
                    #![trigger self.ref_counters.spec_index(candidate)]
                    KERNEL_DEFAULT_PCID < candidate < id ==> !self.pcid_is_free(candidate),
            decreases PCID_MAX - id,
        {
            if *self.ref_counters.get(id) == 0 {
                return Some(id);
            }
            id = id + 1;
        }
        None
    }

    pub open spec fn alloc_ensures(
        &self,
        old: &Self,
        process_ptr: RwLockProcessPtr,
        id: usize,
    ) -> bool {
        &&& self.owning_container.view() == old.owning_container.view()
        &&& self.container_depth.view() == old.container_depth.view()
        &&& self.ref_counters.view()
            =~= old.ref_counters.view().update(id as int, (old.ref_counters.spec_index(id) + 1) as usize)
        &&& self.id_to_proc.view()
            =~= old.id_to_proc.view().update(id as int, old.id_to_proc.view().spec_index(id as int).insert(process_ptr))
    }

    pub fn alloc(&mut self, id: usize, process_ptr: RwLockProcessPtr)
        requires
            old(self).wf(),
            usize_in_range::<PCID_MAX>(id),
            id != KERNEL_DEFAULT_PCID,
            old(self).process_is_unallocated(process_ptr),
            old(self).ref_counters.spec_index(id) < usize::MAX,
        ensures
            final(self).wf(),
            final(self).alloc_ensures(old(self), process_ptr, id),
    {
        let old_counter = *self.ref_counters.get(id);
        self.ref_counters.set(id, old_counter + 1);
        self.id_to_proc = Ghost(
            self.id_to_proc.view().update(id as int, self.id_to_proc.view().spec_index(id as int).insert(process_ptr)),
        );
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

const ASSERT_PCID_ALLOCATOR_PAYLOAD_SIZE: [(); PCID_MAX * core::mem::size_of::<usize>()] = [(); core::mem::size_of::<PcidAllocator>()];
const ASSERT_PCID_ALLOCATOR_LOCK_FITS_2M: [(); 1] = [();
    (core::mem::size_of::<RwLock<
        PcidAllocator,
        (),
        (),
        PCID_ALLOCATOR_HAS_KILL_STATE,
    >>() <= PAGE_SZ_2M) as usize
];
