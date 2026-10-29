use vstd::prelude::*;
use crate::*;
use super::cpu_cr3_pcid::CpuCr3Pcid;

// Platform implementation: send the maskable running-to-idle IPI to `cpu_id` and spin until it acknowledges. The target
// takes the IPI anywhere outside a kernel step, where its interrupt flag is set; it loads `cr3` with the default PCID,
// marks its next trap exit to divert to the idle loop, and acknowledges.
unsafe extern "C" {
    fn veriflat_ipi_running_to_idle(cpu_id: usize, cr3: usize);
}

verus! {
pub struct AtomicPcidCr3 {
    atomic: TrustedAtomicUsize,
}

impl AtomicPcidCr3 {
    pub closed spec fn view(&self) -> (PageTableRoot, Pcid) { (self.atomic.view() & MEM_MASK as usize, self.atomic.view() & 0xfffusize) }
    pub closed spec fn owner_cpu(&self) -> CpuId { self.atomic.owner_cpu() }
    pub closed spec fn inv(&self) -> bool {
        &&& page_ptr_valid(self.view().0)
        &&& pcid_valid(self.view().1)
        &&& self.atomic.view() & !(MEM_MASK as usize | 0xfffusize) == 0
    }

    pub fn new(cr3: PageTableRoot, pcid: Pcid, Ghost(owner_cpu): Ghost<CpuId>) -> (ret: Self)
        requires
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            index_valid(NUM_CPUS, owner_cpu),
        ensures
            ret.inv(),
            ret.view() == (cr3, pcid),
            ret.owner_cpu() == owner_cpu,
    {
        let packed = pack_pcid_cr3(cr3, pcid);
        Self { atomic: TrustedAtomicUsize::new(packed, Ghost(owner_cpu)) }
    }

    pub fn load(&self, Tracked(lctx): Tracked<&mut LocalContext>) -> (ret: (PageTableRoot, Pcid))
        requires
            old(lctx).kernel_view_locking_state() is Acquire,
        ensures
            ret == self.view(),
            self.inv() ==> page_ptr_valid(ret.0) && pcid_valid(ret.1),
            final(lctx).cpu_id() == old(lctx).cpu_id(),
            final(lctx).thread_id() == old(lctx).thread_id(),
            final(lctx).kernel_view_locking_state() is Release,
            typed_lock_maps_unchanged(old(lctx), final(lctx)),
    {
        let packed = self.atomic.load(Tracked(&mut *lctx));
        (packed & MEM_MASK as usize, packed & 0xfffusize)
    }

    /// Platform running-to-idle IPI to the remote cpu `cpu_id` that owns this entry: a maskable IPI whose acknowledgement
    /// this cpu awaits. The target takes the IPI with its interrupt flag set, which holds exactly outside a kernel step:
    /// in user mode, on its trap path, or in its idle loop. There it loads `cr3` with the default PCID, marks its next trap
    /// exit to divert to the idle loop, and acknowledges. `target_lock` is the target's cpu lock, which the caller
    /// write-holds and marked: the target runs a thread, is not in a kernel step, and every kernel path of it that would
    /// lock its own cpu sees the mark and returns at once, so the wait ends. This cpu then stores the default context in
    /// the target's hardware cr3/pcid word. Sending the IPI uses the target's kernel-call permission `perm`; the target
    /// rests in `Idle` afterwards.
    // TODO: model the IPI wait as a virtual lock in the lock order.
    #[verifier::external_body]
    pub(super) fn ipi_remote_running_to_idle_raw(
        &mut self, hardware: &mut CpuCr3Pcid, cpu_id: CpuId, cr3: PageTableRoot, Tracked(cpu_op): Tracked<&mut CpuOpArray>, perm: Tracked<&KernelCallPerm>,
        Ghost(target_lock): Ghost<RwLock<Cpu, (), Option<CpuId>, CPU_HAS_KILL_STATE>>, Tracked(lctx): Tracked<&LocalContext>,
    )
        requires
            old(hardware).wf(),
            perm.view().cpu_id() == cpu_id,
            target_lock.being_killed(),
            target_lock.view().view().state is Running,
            !(old(cpu_op).view()[cpu_id as int] is InStep),
            index_valid(NUM_CPUS, cpu_id),
            cpu_id != lctx.cpu_id(),
            page_ptr_valid(cr3),
            old(self).owner_cpu() == cpu_id,
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(hardware).wf(),
            final(hardware).cr3() == cr3,
            final(hardware).pcid() == KERNEL_DEFAULT_PCID,
            final(self).inv(),
            final(self).view() == (cr3, KERNEL_DEFAULT_PCID),
            final(self).owner_cpu() == cpu_id,
            final(cpu_op).view() == old(cpu_op).view().update(cpu_id as int, CpuOpState::Idle),
    {
        unsafe { veriflat_ipi_running_to_idle(cpu_id, cr3); }
        proof { cpu_op.ipi_running_to_idle(cpu_id); }
        hardware.hardware = Ghost((cr3, KERNEL_DEFAULT_PCID));
        hardware.current_cr3 = cr3;
        hardware.current_pcid = KERNEL_DEFAULT_PCID;
        self.atomic.store(pack_pcid_cr3(cr3, KERNEL_DEFAULT_PCID), Tracked(lctx));
    }

    pub fn store(&mut self, cr3: PageTableRoot, pcid: Pcid, Tracked(lctx): Tracked<&LocalContext>)
        requires
            page_ptr_valid(cr3),
            pcid_valid(pcid),
            old(self).owner_cpu() == lctx.cpu_id(),
            lctx.kernel_view_locking_state() is Release,
        ensures
            final(self).inv(),
            final(self).view() == (cr3, pcid),
            final(self).owner_cpu() == old(self).owner_cpu(),
    {
        let packed = pack_pcid_cr3(cr3, pcid);
        self.atomic.store(packed, Tracked(lctx));
    }
}

fn pack_pcid_cr3(cr3: PageTableRoot, pcid: Pcid) -> (ret: usize)
    requires
        page_ptr_valid(cr3),
        pcid_valid(pcid),
    ensures
        ret & MEM_MASK as usize == cr3,
        ret & 0xfffusize == pcid,
        ret & !(MEM_MASK as usize | 0xfffusize) == 0,
{
    assert({
        &&& (cr3 | pcid) & 0x0000_ffff_ffff_f000usize == cr3
        &&& (cr3 | pcid) & 0xfffusize == pcid
        &&& (cr3 | pcid) & !(MEM_MASK as usize | 0xfffusize) == 0
    }) by (bit_vector)
        requires
            cr3 % 4096 == 0,
            cr3 / 4096 < 2 * 1024 * 1024,
            pcid < 4096,
    ;
    cr3 | pcid
}
}
