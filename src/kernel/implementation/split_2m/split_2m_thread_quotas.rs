#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_commit_spec::*;
#[cfg(verus_keep_ghost)]
use super::split_2m_commit_eof::*;

verus! {
pub fn split_2m_exchange_thread_quotas(thread: &mut Thread)
    requires
        old(thread).inv(),
        old(thread).temp_alloc_clean(),
        old(thread).quota_2m > 0,
        old(thread).quota_4k <= usize::MAX - 512,
    ensures
        final(thread).inv(),
        split_2m_exchange_thread_quotas_eof_transition_framing(*old(thread), *final(thread)),
{
    thread.quota_2m = thread.quota_2m - 1;
    thread.quota_4k = thread.quota_4k + 512;
    proof { split_2m_exchange_thread_quotas_eof_implies_thread_inv(*old(thread), *thread); }
}
}
