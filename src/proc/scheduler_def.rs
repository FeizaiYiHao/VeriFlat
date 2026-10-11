use vstd::prelude::*;
use vstd::simple_pptr::*;
verus! {
use crate::*;

/// One cpu's run queue in a container's scheduler.
pub struct SchedulerShard {
    pub queue: LinkedList<RwLockThreadPtr, 233>,
}

pub type SchedulerShardArray = LockedArray<SchedulerShard, (), (), NUM_CPUS, NO_KILL_STATE>;

/// Per-container scheduler: one independently locked run queue per cpu. Shard `c` is locked with
/// major `SCHEDULER_LOCK_MAJOR` and minor `c`.
pub struct Scheduler {
    pub shards: SchedulerShardArray,
    pub owning_container: RwLockContainerPtr,
}

pub type SchedulerUnLockedMap = UnLockedMap<RwLockSchedulerPtr, Scheduler>;

/// The run queues of `scheduler`, indexed by shard cpu id; shard lock state is not part of it.
#[verifier::opaque]
pub open spec fn scheduler_shards_of(scheduler: Scheduler) -> Seq<Seq<RwLockThreadPtr>> {
    Seq::new(NUM_CPUS as nat, |i: int| scheduler.shards.spec_index(i as usize).view().view().queue.view())
}

/// The lowest shard index at or above `from`, other than `skip`, whose run queue is nonempty.
pub open spec fn first_nonempty_shard(shards: Seq<Seq<RwLockThreadPtr>>, from: int, skip: CpuId) -> Option<CpuId>
    decreases NUM_CPUS - from,
{
    if from < 0 || from >= NUM_CPUS { None }
    else if from != skip as int && shards[from].len() > 0 { Some(from as CpuId) }
    else { first_nonempty_shard(shards, from + 1, skip) }
}

impl LockInvTrait for SchedulerShard {
    open spec fn inv(&self) -> bool { self.queue.inv() }
}

impl LockMajorTrait for SchedulerShard {
    open spec fn lock_major_1(&self) -> LockMajorId { SCHEDULER_LOCK_MAJOR }
    open spec fn lock_major_2(&self) -> LockMajorId { SCHEDULER_LOCK_MAJOR }
    open spec fn lock_major_3(&self) -> LockMajorId { SCHEDULER_LOCK_MAJOR }
    open spec fn lock_major_default(&self) -> LockMajorId { SCHEDULER_LOCK_MAJOR }
    open spec fn lock_major_1_predicate(&self) -> bool { true }
    open spec fn lock_major_2_predicate(&self) -> bool { false }
    open spec fn lock_major_3_predicate(&self) -> bool { false }
    open spec fn lock_major_default_predicate(&self) -> bool { false }
}

impl LockOwnerIdTrait for SchedulerShard {
    open spec fn container_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
    open spec fn process_depth(&self) -> LockOwnerId { LockOwnerId::NotApp }
}

impl LockUserVisibilityTrait for SchedulerShard {
    open spec fn is_user_visible() -> bool { true }
}

impl Scheduler {
    #[verifier::inline]
    pub open spec fn shard(&self, cpu_id: CpuId) -> SchedulerShard { self.shards.spec_index(cpu_id).view().view() }

    pub open spec fn inv(&self) -> bool {
        &&& self.shards.inv()
        &&& forall|cpu_id: CpuId| #![trigger self.shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> self.shards.spec_index(cpu_id).view().inv()
    }

    pub fn new_empty(owning_container: RwLockContainerPtr) -> (ret: Self)
        ensures
            ret.inv(),
            ret.owning_container == owning_container,
            forall|cpu_id: CpuId| #![trigger ret.shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
                &&& !ret.shards.spec_index(cpu_id).view().locked()
                &&& ret.shard(cpu_id).queue.view() == Seq::<RwLockThreadPtr>::empty()
                &&& ret.shard(cpu_id).queue.map() == Map::<usize, RwLockThreadPtr>::empty()
            },
            scheduler_shards_of(ret) == Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty()),
    {
        let mut shard_array: Array<RwLock<SchedulerShard, (), (), NO_KILL_STATE>, NUM_CPUS> = Array::new();
        let mut cpu_id = 0;
        while cpu_id < NUM_CPUS
            invariant
                shard_array.wf(),
                0 <= cpu_id <= NUM_CPUS,
                forall|i: CpuId| #![trigger shard_array.view()[i as int]] index_valid(NUM_CPUS, i) && i < cpu_id ==> {
                    &&& shard_array.view()[i as int].inv()
                    &&& !shard_array.view()[i as int].locked()
                    &&& shard_array.view()[i as int].view().queue.view() == Seq::<RwLockThreadPtr>::empty()
                    &&& shard_array.view()[i as int].view().queue.map() == Map::<usize, RwLockThreadPtr>::empty()
                },
            decreases NUM_CPUS - cpu_id,
        {
            shard_array.set(cpu_id, RwLock::new_unlocked(SchedulerShard { queue: LinkedList::new(None, None) }, (), Ghost(())));
            cpu_id = cpu_id + 1;
        }
        let ret = Self { shards: LockedArray::from_array(shard_array), owning_container };
        assert(scheduler_shards_of(ret) =~= Seq::new(NUM_CPUS as nat, |i: int| Seq::<RwLockThreadPtr>::empty())) by { reveal(scheduler_shards_of); };
        ret
    }

    pub fn new_boot_root(owning_container: RwLockContainerPtr, root_thread: RwLockThreadPtr, thread_node_addr: usize, thread_node_perm: Tracked<PointsTo<Node<RwLockThreadPtr>>>) -> (ret: Self)
        requires
            thread_node_perm.view().is_init(),
            thread_node_perm.view().addr() == thread_node_addr,
            thread_node_perm.view().value().view() == root_thread,
        ensures
            ret.inv(),
            ret.owning_container == owning_container,
            forall|cpu_id: CpuId| #![trigger ret.shards.spec_index(cpu_id)] index_valid(NUM_CPUS, cpu_id) ==> {
                &&& !ret.shards.spec_index(cpu_id).view().locked()
                &&& ret.shard(cpu_id).queue.view() == if cpu_id == 0 { seq![root_thread] } else { Seq::<RwLockThreadPtr>::empty() }
                &&& ret.shard(cpu_id).queue.map() == if cpu_id == 0 { Map::<usize, RwLockThreadPtr>::empty().insert(thread_node_addr, root_thread) } else { Map::<usize, RwLockThreadPtr>::empty() }
            },
    {
        let mut root_queue = LinkedList::new(None, None);
        root_queue.push_tail(thread_node_addr, thread_node_perm);
        let mut shard_array: Array<RwLock<SchedulerShard, (), (), NO_KILL_STATE>, NUM_CPUS> = Array::new();
        shard_array.set(0, RwLock::new_unlocked(SchedulerShard { queue: root_queue }, (), Ghost(())));
        let mut cpu_id = 1;
        while cpu_id < NUM_CPUS
            invariant
                shard_array.wf(),
                1 <= cpu_id <= NUM_CPUS,
                forall|i: CpuId| #![auto] index_valid(NUM_CPUS, i) && i < cpu_id ==> {
                    &&& shard_array.spec_index(i).inv()
                    &&& !shard_array.spec_index(i).locked()
                    &&& shard_array.spec_index(i).view().queue.view() == if i == 0 { seq![root_thread] } else { Seq::<RwLockThreadPtr>::empty() }
                    &&& shard_array.spec_index(i).view().queue.map() == if i == 0 { Map::<usize, RwLockThreadPtr>::empty().insert(thread_node_addr, root_thread) } else { Map::<usize, RwLockThreadPtr>::empty() }
                },
            decreases NUM_CPUS - cpu_id,
        {
            shard_array.set(cpu_id, RwLock::new_unlocked(SchedulerShard { queue: LinkedList::new(None, None) }, (), Ghost(())));
            cpu_id = cpu_id + 1;
        }
        Self { shards: LockedArray::from_array(shard_array), owning_container }
    }
}
}

const ASSERT_SCHEDULER_FITS_4K: [(); 1] = [(); (core::mem::size_of::<Scheduler>() <= PAGE_SZ_4K) as usize];
