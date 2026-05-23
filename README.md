# VeriFlat

## System call, kernel call, internal function

### System call 
System calls are function interfaces marked with `veriflat_system_call` that are callable by the user programs.
System calls maintain the abstract operational specifications and can only call kernel calls and internal functions.

### Kernel call
Kernel calls are functions that take `&mut Kernel` or `& Kernel`.
Kernel calls are not callable by the user program.

### Internal functions
Internal functions do not take `&mut kernel` or `& kernel`, hence unable to perform a global level `inv()` check. 
Each internal function can be marked with `push` and/or `pull`. 
A push function means that the function releases some locks, which requires to return all the way back to an kernel call or system call to perform the `inv()` check.
A pull function means that the function acquires some locks, which means the before calling this function, the caller must have entered `locking` state. 
If an internal function calls a `push` or `pull` function, the function must be marked as `push` or `pull` too.
After a `push` call, the function must return immediately (`assert()` and `proof{}` are allowed). 

## Verifying concurrent invariants

### Concurrent invariant
Each invariant in VeriFlat is always `true` through out the concurrent execution of each thread. 
An invariants can only be broken when all the objects under the invariant are all write-locked (or spinlocked) by the same thread.
Since no other thread can even potentially observe the state of the objects under a broken invariant, it is OK. 

### Verifying the kernel invariants
After a push operation, all execution returns to a kernel level call, and immediately we perform an `inv()` check.

#### TODO
Talk about how to modify Verus to enforce this check. 

## Providing system call specification

### Visible kernel state
Container tree structure
Process tree structure
Scheduler state
Endpoint state
Address spaces
IO address spaces 
Root table state 
Container quota
CPU state

### Atomic kernel spec
All changes to the above kernel objects in a given invocation to a syscall need to 
appear to be atomic -- No other thread shall observe partial changes of a system call.
To achieve this, all visible kernel objects locked by a system call 
will need to be locked before any `push` operation and cannot be re-locked.
The logic is simple -- before any change to the visible kernel objects becomes visible to other threads, 
all changed (including changed in the future) objects must be invisible.

## Deadlock freedom
See [LockId](LockId.md)


### User accessible kernel objects
Page table `view()` update and maybe page table updates in general have an immediate effect on the observable state of the kernel hence should trigger a 
global kernel-level `inv()` check similar to unlocking a write-lock. Also any update to the PCI root table too.

### Kernel objects with atomic interfaces 
Each operation on these objects is both `rlock` and `wlock`.

## Providing an atomic system call spec interface

### Reordering of action
For a kernel object that is locked at most once for the duration of the entire system call, its state change can be described as a single,
atomic operation using pre- and postcondition. 

For a kernel object that is locked more than once for the duration of the system call, we can still report its last-seen state in the postcondition, 
but it shouldn't be super useful. 

### Nullifying the pre state of unlocked object. 
After the first `unlock()` operation, each `lock()` triggers a change of the global state -- all the kernel objects that are not locked will have 
their states nullified. Since they could be changed by other threads.

### Squash changes on tracked maps.
There exists a few tracked maps whose domains determine the domains of `alive` objects in the kernel. For example, the domain of all `Container`
in the kernel. These maps has zero impact on the actual state of the kernel other than aiding the proofs. Since all the objects under these 
maps are protected by locks, it's safe to reorder their operations and squash the changes into one big atomic change. 

### Ensuring invariants when objects are re-locked.
Since we nullify the pre-state of a re-locked object, Verus wouldn't be able to infer that all the invariants still hold after this re-`lock()`. 
However, the invariants still hold, we insert an `assume(self.inv())` after each `lock()` to let Verus know that the invariants are still true, 
after the second `lock()` returns. 

#### TODO
Talk about how to modify Verus to enforce this assume. 

## TODO
Add a user view() of the page table and a kernel view() of the page table.

The user view() of the page table cannot be locked, hence triggering an inv() check whenever it's updated. 