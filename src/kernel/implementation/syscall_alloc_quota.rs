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
            assert(self.container_map.dom().contains(self.cpu_array.spec_index(cpu_id).view().view().owning_container)) by {
                container_cpu_wf_proof();
            };

            let cpu_lock_id = Ghost(LockId{ 
                container: self.cpu_array.spec_index(cpu_id).container_depth(), 
                process: self.cpu_array.spec_index(cpu_id).process_depth(), 
                major: CPU_LOCK_MAJOR_RUNNING, 
                minor: cpu_id });

            assert(self.cpu_array.spec_index(cpu_id).view().view().container_depth == self.container_map.spec_index(self.cpu_array.spec_index(cpu_id).view().view().owning_container).view_rodata().view().depth) by {
                container_cpu_wf_proof();
            };

            let Tracked(cpu_lock_perm) = self.cpu_array.wlock(cpu_id, Tracked(&mut lctx), cpu_lock_id);
            let cpu = self.cpu_array.borrow(cpu_id, Tracked(&cpu_lock_perm));
            let thread_ptr = cpu.current_thread.unwrap();
            let process_ptr = cpu.current_process.unwrap();
            let container_ptr = cpu.owning_container;
            
            assert(self.container_map.dom().contains(container_ptr)) by {
                container_cpu_wf_proof();
            };
            // assert(self.container_map.spec_index(container_ptr).locked_by(&lctx@) == false);

            let container_lock_id = Ghost(LockId{ 
                container: self.cpu_array.spec_index(cpu_id).container_depth(), 
                process: LockOwnerId::NotApp, 
                major: CONTAINER_LOCK_MAJOR, 
                minor: container_ptr });

            let res = self.container_map.try_wlock(container_ptr, Tracked(&mut lctx), container_lock_id);
            if let (false, _) = res{
                assert(self.container_map.spec_index(container_ptr).being_killed() == true);
                return;
            }
            let Tracked(container_lock_perm) = res.1.unwrap();
            let container = self.container_map.borrow(container_ptr, Tracked(&container_lock_perm));

        }
    }
}