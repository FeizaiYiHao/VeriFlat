use vstd::prelude::*;
use crate::*;

verus! {
/// TCB: writes zeros over the 4K page's bytes; page contents are outside the model.
#[verifier::external_body]
pub fn zero_4k_page(pg_ptr: PagePtr)
    requires
        page_ptr_valid(pg_ptr),
{
    unsafe { core::ptr::write_bytes(pg_ptr as *mut u8, 0u8, PAGE_SZ_4K); }
}

/// TCB: writes zeros over the 2M page's bytes; page contents are outside the model.
#[verifier::external_body]
pub fn zero_2m_page(pg_ptr: PagePtr)
    requires
        page_ptr_2m_valid(pg_ptr),
{
    unsafe { core::ptr::write_bytes(pg_ptr as *mut u8, 0u8, PAGE_SZ_2M); }
}

/// TCB: writes zeros over the 1G page's bytes; page contents are outside the model.
#[verifier::external_body]
pub fn zero_1g_page(pg_ptr: PagePtr)
    requires
        page_ptr_1g_valid(pg_ptr),
{
    unsafe { core::ptr::write_bytes(pg_ptr as *mut u8, 0u8, PAGE_SZ_1G); }
}
}
