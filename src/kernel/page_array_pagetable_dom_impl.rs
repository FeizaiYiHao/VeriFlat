use vstd::prelude::*;
use crate::define::*;
use crate::page_array::*;
use crate::pagetable_map::*;
use crate::primitive::*;
use crate::util::page_ptr_util_u::*;
use crate::locks::*;
use crate::util::*;

use super::kernel_define_spec::Kernel;
verus! {

    impl Kernel{
        pub fn kernel_add_mapping_4k(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, pagetable_root: RwLockPageTableRoot, page_index: PageIndex, pagetable_lock_perm: Tracked<LockPerm>)
            requires
                old(self).inv(),
                page_index_wf(page_index),
                forall|i:PageIndex|
                    #![auto]
                    page_index_wf(i) ==> wlock_requires(old(self).page_array[i]@, old(lctx)),
                old(self).page_array[page_index]@@.is_mapped(),
                old(lctx).lock_seq().len() != 0,
                old(lctx).lock_seq().last() == pagetable_root.to_lock_id(),

                old(self).pagetable_dom.dom().contains(pagetable_root),
                old(self).pagetable_dom[pagetable_root].wlocked_by(old(lctx)) == true,

                pagetable_lock_perm.state() is WriteLock,
                pagetable_lock_perm.thread_id() == old(lctx).thread_id(),
                pagetable_lock_perm.lock_id() == old(self).pagetable_dom[pagetable_root].locking_thread() -> Write_lock_id,
        {
            let page_lock_perm = self.page_array.wlock_page(page_index, Tracked(lctx), Ghost(LockId{container: LockOwnerId::none(), process: LockOwnerId::none(), major: MAPPED_PAGE_LOCK_MAJOR, minor: page_index}));
        }
    }
}