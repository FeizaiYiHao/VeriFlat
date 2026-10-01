use vstd::prelude::*;
use crate::*;
use super::syscall_new_container_cpu_spec::new_container_cpu_transfer_transition;
use super::syscall_new_container_cpu_eof::new_container_cpu_transfer_eof;

verus! {
/// Moves the write-held Off CPU from the parent CPU set into the child CPU set,
/// then releases that CPU and both CPU sets.
#[verifier::spinoff_prover]
pub(super) fn transfer_new_container_cpu(
    krnl: &mut KernelK, Tracked(lctx): Tracked<&mut LocalContext>, parent_container_ptr: RwLockContainerPtr, child_container_ptr: RwLockContainerPtr,
    parent_cpu_set: RwLockCpuSetPtr, child_cpu_set: RwLockCpuSetPtr, transfer_cpu_id: CpuId, Tracked(transfer_cpu_lock_perm): Tracked<LockPerm>,
    Tracked(parent_cpu_set_lock_perm): Tracked<LockPerm>, Tracked(child_cpu_set_lock_perm): Tracked<LockPerm>,
)
    requires
        old(krnl).inv(),
        typed_lock_maps_aligned(old(krnl), old(lctx)),
        old(krnl).cpu_published[transfer_cpu_id as int].view() == (old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_cr3, old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view().current_pcid),
        parent_container_ptr != child_container_ptr,
        old(krnl).ctn_mp.dom().contains(parent_container_ptr),
        old(krnl).ctn_mp.dom().contains(child_container_ptr),
        old(krnl).ctn_mp.spec_index(parent_container_ptr).view_rodata().view().cpu_set == parent_cpu_set,
        old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().cpu_set == child_cpu_set,
        old(krnl).cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.closed_view().contains(transfer_cpu_id),
        old(lctx).cpu_set_lock_map().dom() =~= set![parent_cpu_set, child_cpu_set],
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), parent_cpu_set, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_set_lock_map(), child_cpu_set, TypedLockMode::Write),
        typed_lock_map_contains_mode(old(lctx).cpu_lock_map(), transfer_cpu_id, TypedLockMode::Write),
        transfer_cpu_lock_perm.state() is WriteLock,
        transfer_cpu_lock_perm.thread_id() == old(lctx).thread_id(),
        transfer_cpu_lock_perm.lock_id() == old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().locking_thread()->Write_lock_id,
        parent_cpu_set_lock_perm.state() is WriteLock,
        parent_cpu_set_lock_perm.thread_id() == old(lctx).thread_id(),
        parent_cpu_set_lock_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(parent_cpu_set).locking_thread()->Write_lock_id,
        child_cpu_set_lock_perm.state() is WriteLock,
        child_cpu_set_lock_perm.thread_id() == old(lctx).thread_id(),
        child_cpu_set_lock_perm.lock_id() == old(krnl).cpu_set_mp.spec_index(child_cpu_set).locking_thread()->Write_lock_id,
    ensures
        final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view() == (CpuView {
            owning_container: child_container_ptr, container_depth: old(krnl).ctn_mp.spec_index(child_container_ptr).view_rodata().view().depth,
            ..old(krnl).cpu_arr.spec_index(transfer_cpu_id).view().view().view()
        }),
        final(krnl).cpu_arr.spec_index(transfer_cpu_id).view().locking_thread() is None,
        final(krnl).inv(),
        final(lctx).cpu_id() == old(lctx).cpu_id(),
        final(lctx).thread_id() == old(lctx).thread_id(),
        typed_lock_maps_aligned(final(krnl), final(lctx)),
        final(lctx).cpu_lock_map() == old(lctx).cpu_lock_map().remove(transfer_cpu_id),
        final(lctx).cpu_set_lock_map().dom().is_empty(),
        final(lctx).page_lock_map() == old(lctx).page_lock_map(),
        final(lctx).pcid_needflush_lock_map() == old(lctx).pcid_needflush_lock_map(),
        final(lctx).container_lock_map() == old(lctx).container_lock_map(),
        final(lctx).process_lock_map() == old(lctx).process_lock_map(),
        final(lctx).thread_lock_map() == old(lctx).thread_lock_map(),
        final(lctx).endpoint_lock_map() == old(lctx).endpoint_lock_map(),
        final(lctx).scheduler_lock_map() == old(lctx).scheduler_lock_map(),
        final(lctx).pcid_allocator_lock_map() == old(lctx).pcid_allocator_lock_map(),
        final(lctx).pagetable_lock_map() == old(lctx).pagetable_lock_map(),
        final(lctx).iommu_table_lock_map() == old(lctx).iommu_table_lock_map(),
        final(lctx).allocator_4k_lock_maps() == old(lctx).allocator_4k_lock_maps(),
        final(lctx).allocator_2m_lock_maps() == old(lctx).allocator_2m_lock_maps(),
        final(lctx).allocator_1g_lock_maps() == old(lctx).allocator_1g_lock_maps(),
        *final(krnl) == (KernelK { cpu_arr: final(krnl).cpu_arr, cpu_set_mp: final(krnl).cpu_set_mp, ..*old(krnl) }),
        final(krnl).cpu_set_mp.spec_index(parent_cpu_set).locking_thread() is None,
        final(krnl).cpu_set_mp.spec_index(child_cpu_set).locking_thread() is None,
        forall|p: RwLockCpuSetPtr| #![trigger final(krnl).cpu_set_mp.spec_index(p)] old(krnl).cpu_set_mp.dom().contains(p) && p != parent_cpu_set && p != child_cpu_set ==>
            final(krnl).cpu_set_mp.spec_index(p) == old(krnl).cpu_set_mp.spec_index(p),
        forall|cpu_id: CpuId| #![trigger final(krnl).cpu_arr.spec_index(cpu_id)]
            index_valid(NUM_CPUS, cpu_id) && cpu_id != transfer_cpu_id ==> final(krnl).cpu_arr.spec_index(cpu_id) == old(krnl).cpu_arr.spec_index(cpu_id),
        forall|pt: RwLockPageTableRoot| #![trigger pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view())]
            pagetable_tlb_entries_present(old(krnl).cpu_tlb, old(krnl).cpu_arr, old(krnl).pcid_needflush, pt, old(krnl).pt_mp.spec_index(pt).view())
            ==> pagetable_tlb_entries_present(final(krnl).cpu_tlb, final(krnl).cpu_arr, final(krnl).pcid_needflush, pt, final(krnl).pt_mp.spec_index(pt).view()),
{
    proof {
        assert({
            &&& krnl.ctn_mp.view().spec_index(child_container_ptr).is_init()
            &&& krnl.ctn_mp.view().spec_index(child_container_ptr).addr() == child_container_ptr
        }) by { container_perms_wf_at(krnl.ctn_mp, child_container_ptr); };
        assert({
            &&& krnl.cpu_set_mp.dom().contains(parent_cpu_set)
            &&& krnl.cpu_set_mp.dom().contains(child_cpu_set)
            &&& parent_cpu_set != child_cpu_set
        }) by { reveal(container_cpu_set_wf); };
        assert({
            &&& krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().state is Off
            &&& krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().view().owning_container == parent_container_ptr
            &&& !krnl.cpu_set_mp.spec_index(child_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& krnl.cpu_set_mp.spec_index(parent_cpu_set).view().owned_cpus.view().contains(transfer_cpu_id)
            &&& krnl.cpu_set_mp.spec_index(parent_cpu_set).inv()
            &&& krnl.cpu_set_mp.spec_index(child_cpu_set).inv()
            &&& krnl.cpu_set_mp.perms_wf()
            &&& krnl.cpu_arr.inv()
            &&& krnl.cpu_arr.spec_index(transfer_cpu_id).view().is_init()
            &&& krnl.cpu_arr.spec_index(transfer_cpu_id).view().view().wf()
        }) by { reveal(container_cpu_set_wf); reveal(cpu_set_perms_wf); reveal(container_cpu_wf); reveal(cpu_array_wf); };
    }
    let child_container_depth = krnl.ctn_mp.borrow_rodata(child_container_ptr).borrow().depth;
    let ghost locked_k = *krnl;
    {
        let parent_set = krnl.cpu_set_mp.borrow_mut_typed(parent_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&parent_cpu_set_lock_perm));
        parent_set.owned_cpus.remove(transfer_cpu_id);
        let child_set = krnl.cpu_set_mp.borrow_mut_typed(child_cpu_set, Ghost(lctx.cpu_set_lock_map()), Tracked(&*lctx), Tracked(&child_cpu_set_lock_perm));
        child_set.owned_cpus.insert_closed(transfer_cpu_id);
        let transfer_cpu = krnl.cpu_arr.borrow_mut_typed(transfer_cpu_id, Ghost(lctx.cpu_lock_map()), Tracked(&*lctx), Tracked(&transfer_cpu_lock_perm));
        transfer_cpu.transfer_off_cpu_to_container(child_container_ptr, child_container_depth);
    }
    proof {
        assert(new_container_cpu_transfer_transition(locked_k, *krnl, parent_container_ptr, child_container_ptr, parent_cpu_set, child_cpu_set, transfer_cpu_id, lctx.thread_id())) by {
            reveal(new_container_cpu_transfer_transition); reveal(cpu_set_perms_wf);
        };
        new_container_cpu_transfer_eof(locked_k, *krnl, parent_container_ptr, child_container_ptr, parent_cpu_set, child_cpu_set, transfer_cpu_id, lctx.thread_id());
    }
    krnl.wunlock_cpu(transfer_cpu_id, Tracked(&mut *lctx), Tracked(transfer_cpu_lock_perm));
    krnl.wunlock_cpu_set(child_cpu_set, Tracked(&mut *lctx), Tracked(child_cpu_set_lock_perm));
    krnl.wunlock_cpu_set(parent_cpu_set, Tracked(&mut *lctx), Tracked(parent_cpu_set_lock_perm));

}
}
