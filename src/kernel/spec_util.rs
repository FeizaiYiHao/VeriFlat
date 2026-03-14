use vstd::prelude::*;
use crate::*;
use super::*;
verus! {

impl Kernel{
    pub open spec fn get_cpu(&self, cpu_id: CpuId) -> RwLock<Cpu, CPU_HAS_KILL_STATE>
        recommends
            cpu_id_valid(cpu_id),
            self.cpu_array.inv(),
    {
        self.cpu_array.get_cpu(cpu_id)
    }

    pub open spec fn get_pagetable_dom(&self) -> Set<RwLockPageTableRoot>
    {
        self.pagetable_dom.dom()
    }

    pub open spec fn get_pagetable(&self, pagetable_root: RwLockPageTableRoot) -> RwLock<PageTable<PT_TYPE>, PAGE_TABLE_HAS_KILL_STATE>
        recommends
            self.get_pagetable_dom().contains(pagetable_root),
            self.pagetable_dom.inv(),
    {
        self.pagetable_dom.spec_index(pagetable_root)
    }
}

}