use vstd::prelude::*;
use crate::*;
verus! {
    impl KernelK{
        pub fn syscall_alloc_quota_4k(&mut self, tracked mut lctx: Tracked<LocalContext>, cpu_id: CpuId, alloc_amount: usize)
            requires
                cpu_id_valid(cpu_id),
                old(self).inv(),
                old(self).all_objects_unlocked(&lctx),
                old(self).cpu_array.spec_index(cpu_id).view().view().state == CpuState::Running,
                lctx.lock_seq() == Seq::<LockId>::empty(),
                lctx.kernel_view_locking_state() is Acquire,
                lctx.user_view_locking_state() is Acquire,
        {
            let Tracked(cpu_lock_perm) = self.cpu_array.wlock(cpu_id, Tracked(&mut lctx), Ghost(LockId{ 
                container: self.cpu_array.spec_index(cpu_id).container_depth(), 
                process: self.cpu_array.spec_index(cpu_id).process_depth(), 
                major: CPU_LOCK_MAJOR_RUNNING, 
                minor: cpu_id }));
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let thread_ptr = cpu.current_thread.unwrap();
            let process_ptr = cpu.current_process.unwrap();
            let container_ptr = cpu.owning_container;

            // let Tracked(container_perm) = self.container_map.wlock(container_ptr, Tracked(&mut lctx), Ghost(LockId{ 
            //     container: LockOwnerId::NotApp, 
            //     process: LockOwnerId::NotApp, 
            //     major: CONTAINER_LOCK_MAJOR, 
            //     minor: container_ptr }));
            // (cpu_id, Tracked(&mut lctx), Ghost(LockId{ 
            //     container: self.cpu_array.spec_index(cpu_id).container_depth(), 
            //     process: self.cpu_array.spec_index(cpu_id).process_depth(), 
            //     major: CPU_LOCK_MAJOR_RUNNING, 
            //     minor: cpu_id }));
        }
    }
}