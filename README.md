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

- [x] After completing EOF optimization, optimize proof performance across the repository.

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

### Concurrent interleaving between kernel sections

[`KernelK::kernel_step_boundary`](src/kernel/kernel_k_define_spec.rs) models
concurrent interleaving between a completed `Release` section and the next
`Acquire` section. Its contract preserves objects whose locks remain held and
allows other state to change subject to the boundary's explicit guarantees.
Proofs across this boundary use those guarantees and subsequent lock contracts
to determine which earlier facts remain available.

[`LocalContext`](src/locks/local_context.rs) records held locks in typed maps and
an exact `Set<(LockId, KernelObjId)>` ledger. `typed_lock_maps_aligned` relates the
typed maps to the kernel objects; `lock_id_set_aligned` relates them to the ledger.
Lock operations maintain both alignments, and the boundary preserves them.

### Invariant obligations and trusted boundaries

The caller must establish `KernelK::inv()` and both lock alignments before
`kernel_step_boundary`. The boundary guarantees them again after the modeled
interleaving and restores the `Acquire` phase. It is an `external_body` proof
function: preservation by concurrent execution is part of the trusted model.
The current source contains no explicit `assume(...)` or `admit()` calls.

[`KernelSteps`](src/kernel/kernel_total_define_spec.rs) records changes to the
user projection, `kernel_k_to_kernel_u`. At a boundary, it records the completed
section's change before refreshing the snapshot after interleaving. At syscall
exit, `end_kernel_step` records the final section without introducing another
interleaving point. Sections whose user projection is unchanged add no user step.
Both recording operations are trusted `external_body` functions.

The trusted code also includes low-level lock and memory primitives, permission
construction using `Tracked::assume_new()` inside `external_body` functions, and
the explicit
[cardinality](src/kernel/lemma/kernel_cardinality_axioms.rs) axioms (the fold lemmas in
`src/kernel/lemma/kernel_fold_lemmas.rs` are proven). Verification
results depend on these contracts and axioms.
