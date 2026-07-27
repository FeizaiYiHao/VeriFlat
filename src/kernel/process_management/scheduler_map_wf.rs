use vstd::prelude::*;
use crate::*;

verus! {
    #[verifier::opaque]
    pub open spec fn scheduler_perms_wf(scheduler_map: SchedulerLockedMap) -> bool{
        &&&
        scheduler_map.perms_wf()
        &&&
        schedulers_inv(scheduler_map)
    }
    pub open spec fn schedulers_inv(scheduler_map: SchedulerLockedMap) -> bool{
        &&&
        forall|scheduler_p:RwLockSchedulerPtr|
            #![auto]
            scheduler_map.dom().contains(scheduler_p)
            ==>
            scheduler_map[scheduler_p].inv()
    }

    /// A scheduler's ordering id is independent of its mutable queue.  The
    /// pointer is its minor id, and all remaining fields are fixed by the
    /// Scheduler lock traits.
    pub proof fn scheduler_lock_id_is_static()
        ensures
            forall|scheduler_map: SchedulerLockedMap, scheduler_ptr: RwLockSchedulerPtr|
                #![trigger scheduler_map.lock_id_by_key(scheduler_ptr)]
                scheduler_map.dom().contains(scheduler_ptr)
                    && scheduler_map.perms_wf()
                ==> scheduler_map.lock_id_by_key(scheduler_ptr) == (LockId{
                    container: LockOwnerId::NotApp,
                    process: LockOwnerId::NotApp,
                    major: SCHEDULER_LOCK_MAJOR,
                    minor: scheduler_ptr,
                }),
    {
        lock_id_fields_eq_imply_eq();
        assert forall|scheduler_map: SchedulerLockedMap, scheduler_ptr: RwLockSchedulerPtr|
            #![trigger scheduler_map.lock_id_by_key(scheduler_ptr)]
            scheduler_map.dom().contains(scheduler_ptr)
                && scheduler_map.perms_wf()
            implies scheduler_map.lock_id_by_key(scheduler_ptr) == (LockId{
                container: LockOwnerId::NotApp,
                process: LockOwnerId::NotApp,
                major: SCHEDULER_LOCK_MAJOR,
                minor: scheduler_ptr,
            }) by {
            if scheduler_map.dom().contains(scheduler_ptr)
                && scheduler_map.perms_wf() {
                let ghost scheduler_id = LockId{
                    container: LockOwnerId::NotApp,
                    process: LockOwnerId::NotApp,
                    major: SCHEDULER_LOCK_MAJOR,
                    minor: scheduler_ptr,
                };
                assert(scheduler_map.lock_id_by_key(scheduler_ptr).container
                    == scheduler_id.container);
                assert(scheduler_map.lock_id_by_key(scheduler_ptr).process
                    == scheduler_id.process);
                assert(scheduler_map.lock_id_by_key(scheduler_ptr).major
                    == scheduler_id.major);
                assert(scheduler_map.view()[scheduler_ptr].addr() == scheduler_ptr);
                assert(scheduler_map.lock_id_by_key(scheduler_ptr).minor
                    == scheduler_id.minor);
            }
        }
    }
}
