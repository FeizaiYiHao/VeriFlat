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

### Objects with atomic interfaces
Page table `view()` update and maybe page table updates in general have an immediate effect on the observable state of the kernel hence should trigger a 
global kernel-level `inv()` check similar to unlocking a write-lock. Also any update to the PCI root table too.

## Providing an atomic system call spec interface

### Reordering of action
For a kernel object that is locked at most once for the duration of the entire system call, its state change can be described as a single,
atomic operation using pre- and postcondition. 

For a kernel object that is locked more than once for the duration of the system call, we can still report its last-seen state in the postcondition, 
but it shouldn't be super useful. 

### Nullifying the pre state of re-locked object. 
When a kernel object is locked twice, for the second time the lock is acquired, since the object can be modified by other threads in the time window between 
`unlock()` and `lock()`, the `lock()` function will make the state of the object `undefined`.
Therefore, Verus wouldn't be able to infer and connection between the state of the object before the system call and the state of the object when 
it's re-locked. 

### Ensuring invariants when objects are re-locked.
Since we nullify the pre-state of a re-locked object, Verus wouldn't be able to infer that all the invariants still hold after this re-`lock()`. 
However, the invariants still hold, we insert an `assume(self.inv())` after each `lock()` to let Verus know that the invariants are still true, 
after the second `lock()` returns. 

#### TODO
Talk about how to modify Verus to enforce this assume. 