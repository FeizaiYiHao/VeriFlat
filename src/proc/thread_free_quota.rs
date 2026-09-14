use vstd::prelude::*;
use crate::*;

verus! {
impl Thread {
    pub open spec fn free_quota_pending_4k_at_depth(&self, depth: usize) -> usize
        recommends self.inv(), depth <= self.container_depth,
    {
        if depth == self.container_depth { self.direct_free_quota_pending_4k.view() }
        else { self.indirect_free_quota_pending_4k.view().spec_index(depth as int) }
    }

    pub fn add_free_quota_pending_4k(&mut self, depth: usize, counter: &mut usize)
        requires
            old(self).inv(),
            depth <= old(self).container_depth,
            *old(counter) == old(self).free_quota_pending_4k_at_depth(depth),
            *old(counter) < usize::MAX,
        ensures
            final(self).inv(),
            *final(counter) == *old(counter) + 1,
            *final(counter) == final(self).free_quota_pending_4k_at_depth(depth),
            final(self).direct_free_quota_pending_4k.view() == old(self).direct_free_quota_pending_4k.view() + if depth == old(self).container_depth { 1int } else { 0int },
            final(self).indirect_free_quota_pending_4k.view() == if depth < old(self).container_depth { old(self).indirect_free_quota_pending_4k.view().update(depth as int, *final(counter)) } else { old(self).indirect_free_quota_pending_4k.view() },
            *final(self) == (Thread { direct_free_quota_pending_4k: final(self).direct_free_quota_pending_4k, indirect_free_quota_pending_4k: final(self).indirect_free_quota_pending_4k, ..*old(self) }),
    {
        *counter = *counter + 1;
        if depth == self.container_depth {
            self.direct_free_quota_pending_4k = Ghost(*counter);
        } else {
            self.indirect_free_quota_pending_4k = Ghost(self.indirect_free_quota_pending_4k.view().update(depth as int, *counter));
        }
    }

    pub fn clear_free_quota_pending_4k(&mut self, depth: usize, counter: &mut usize)
        requires
            old(self).inv(),
            depth <= old(self).container_depth,
            *old(counter) == old(self).free_quota_pending_4k_at_depth(depth),
        ensures
            final(self).inv(),
            *final(counter) == 0,
            final(self).free_quota_pending_4k_at_depth(depth) == 0,
            final(self).direct_free_quota_pending_4k.view() == if depth == old(self).container_depth { 0usize } else { old(self).direct_free_quota_pending_4k.view() },
            final(self).indirect_free_quota_pending_4k.view() == if depth < old(self).container_depth { old(self).indirect_free_quota_pending_4k.view().update(depth as int, 0usize) } else { old(self).indirect_free_quota_pending_4k.view() },
            *final(self) == (Thread { direct_free_quota_pending_4k: final(self).direct_free_quota_pending_4k, indirect_free_quota_pending_4k: final(self).indirect_free_quota_pending_4k, ..*old(self) }),
    {
        *counter = 0;
        if depth == self.container_depth {
            self.direct_free_quota_pending_4k = Ghost(0usize);
        } else {
            self.indirect_free_quota_pending_4k = Ghost(self.indirect_free_quota_pending_4k.view().update(depth as int, 0usize));
        }
    }
}
}
