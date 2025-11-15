# VeriFlat

## TODO
Add a user view() of the page table and a kernel view() of the page table.

The user view() of the page table cannot be locked, hence triggering an inv() check whenever it's updated. 

## Verifying concurrent invariants

### Concurrent invariant
Each invariant in VeriFlat is always `true` through out the concurrent execution of each thread. 
A invariants can only be broken when all the objects under the invariant are all write-locked (or spinlocked) by the same thread.
Since no other thread can even potentially observe the state of the objects under a broken invariant, it is OK. 

### Verifying the kernel invariants
When the a object under a broken invariant becomes `visible` to other threads again, (i.e., the write-lock is released),
we trigger a assertion on `inv()` on the kernel to make sure all invariants are preserved.  

#### TODO
Talk about how to modify Verus to enforce this check. 