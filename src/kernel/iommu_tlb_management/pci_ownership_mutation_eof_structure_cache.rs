use vstd::prelude::*;
verus! {
use crate::*;
use super::pci_ownership_mutation_eof::*;

/// EOF closure of `KernelK::update_pci_entry` for the IOMMU paging-structure caches: no context entry, DID, IOMMU table, or
/// cache moves.
pub(super) proof fn update_pci_entry_eof_structure_cache(pre: KernelK, post: KernelK, root: RwLockPageTableRoot, index: int, update: PciEntryUpdate)
    requires
        pre.inv(),
        update_pci_entry_eof_transition_framing(pre, post, root, index, update),
        update_pci_entry_eof_owner_update(pre, post, root, index, update),
    ensures iommu_structure_cache_wf(post.iommu_tlb, post.irt.view(), post.it_mp),
{ reveal(update_pci_entry_eof_transition_framing); reveal(update_pci_entry_eof_owner_update); reveal(iommu_structure_cache_wf); }
}
