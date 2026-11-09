use vstd::prelude::*;
use crate::*;

verus! {
/// TCB: zeros the bytes exclusively owned by the matching 4K permission.
#[verifier::external_body]
pub fn zero_4k_page(pg_ptr: PagePtr, Tracked(perm): Tracked<&mut PagePerm4k>)
    requires
        page_ptr_valid(pg_ptr),
        old(perm).is_init(),
        old(perm).addr() == pg_ptr,
    ensures
        final(perm).is_init(),
        final(perm).addr() == old(perm).addr(),
        final(perm).value().view() == Seq::new(PAGE_SZ_4K as nat, |i: int| 0u8),
{
    unsafe { core::ptr::write_bytes(pg_ptr as *mut u8, 0u8, PAGE_SZ_4K); }
}

/// TCB: zeros the bytes exclusively owned by the matching 2M permission.
#[verifier::external_body]
pub fn zero_2m_page(pg_ptr: PagePtr, Tracked(perm): Tracked<&mut PagePerm2m>)
    requires
        page_ptr_2m_valid(pg_ptr),
        old(perm).is_init(),
        old(perm).addr() == pg_ptr,
    ensures
        final(perm).is_init(),
        final(perm).addr() == old(perm).addr(),
        final(perm).value().view() == Seq::new(PAGE_SZ_2M as nat, |i: int| 0u8),
{
    unsafe { core::ptr::write_bytes(pg_ptr as *mut u8, 0u8, PAGE_SZ_2M); }
}

/// TCB: zeros the bytes exclusively owned by the matching 1G permission.
#[verifier::external_body]
pub fn zero_1g_page(pg_ptr: PagePtr, Tracked(perm): Tracked<&mut PagePerm1g>)
    requires
        page_ptr_1g_valid(pg_ptr),
        old(perm).is_init(),
        old(perm).addr() == pg_ptr,
    ensures
        final(perm).is_init(),
        final(perm).addr() == old(perm).addr(),
        final(perm).value().view() == Seq::new(PAGE_SZ_1G as nat, |i: int| 0u8),
{
    unsafe { core::ptr::write_bytes(pg_ptr as *mut u8, 0u8, PAGE_SZ_1G); }
}
}
