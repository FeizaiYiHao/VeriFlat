# B0 — API freeze + kernel_core compile pass

**Goal.** Put the new L2 entry-lock structures, TCB primitives, the U `pagetable_window_locks` field, the three window-map helpers and the `Share4k.directory` field in place. Then make crate `veriflat_kernel_core` **typecheck**. You write all new exec bodies and change signatures, field names and spec definitions. You do **not** repair proofs; B1 and B2 do that next, and syscall crates are fixed later. You are the only agent running now.

**Owned files** (all under `src/`; edit only these):
- `pagetable_concurrent/` — every file
- `pagetable_seq/pagetable_spec.rs`, `pagetable_seq/pagetable_window_stale_eof.rs`, `pagetable_seq/pagetable_util_t.rs`
- `proc/thread_def.rs`
- `kernel/kernel_u_define_spec.rs`, `kernel/kernel_step_spec/kernel_u_steps.rs`, `kernel/init.rs`
- `kernel/kernel_step_wrappers.rs`, `kernel/kernel_step_wrappers/*.rs`
- `kernel/memory_management/{pagetable_map_spec,subsystem_mutation_pagetable_map,subsystem_mutation_eof}.rs`
- `kernel/implementation/locker_unlocker/{locker_unlocker_pagetable,locker_unlocker_pagetable_eof,locker_unlocker_pagetable_window,locker_unlocker_pagetable_range_windows}.rs`

**What to change.**
1. `src/pagetable_concurrent/l2_page_map.rs`: rewrite exactly as in the copied §A.1, §B.1 and §B.2 below. This file is final after B0 and **must verify**.
2. `PageTableLower` (pagetable_concurrent_spec.rs:28-38) and accessors (:319/:322): as in the copied §A.2. Rewrite every spec fn that reads a deleted field (`l2_ghost`, `l2_lock`, `l2_lock_of`, `l1_tables`, `locked_windows`) to the new accessors. Rewrite the invariant bodies to the new text in the copied §E.1 (definitions only; B1 proves them).
3. Exec bodies in pagetable_concurrent: `lock_window`/`unlock_window` (§B.3); the write path (§B.4) for `create_entry_l2` (impl_base:175), `remove_l2_entry` (remove_base:116), `map_4k_page` (impl_map:9), `map_2m_page` (:72), `unmap_4k_page_user_view`/`_kernel` (remove_base:9/:65), and `remove_structure_page` L1 branch (structure_scan:132).
   - Each of these 7 gains a `Tracked(window_perm): Tracked<&LockPerm>` parameter.
   - `create_entry_l3` (impl_base:66) locks `lo..=hi` one by one with `L2EntryLock::lock` after `page_perm_to_l2_page_map` (loop with `decreases`). It still returns `Tracked<Map<L2Index, LockPerm>>`.
   - `remove_l3_entry` (:182) calls the new `l2_page_map_to_page_perm`.
   - `get_entry_l1` (util.rs:146) gains `l2i` / L2-page arguments and reads `l1_perm(l3.addr, l2i)`.
   - `spec_empty`/`tracked_empty` (util :178/:186) and `retype_page_to_pagetable_c_and_insert` (util_t:10) lose the deleted fields and gain `pagetable_window_locks: Ghost(Map::empty())`.
4. U side (copied §D.1-§D.3): add `PageTableU.pagetable_window_locks`, the projection copy, and `Map::empty()` in the 6 literals.
5. Helpers: add the three `pagetable_window_locks_after_*` spec fns to `pagetable_seq/pagetable_spec.rs` exactly as copied in §D.4. Their names are user-approved (D7).
6. `proc/thread_def.rs:83`: add `directory: Mmap4kDirectory` to `Share4k`, placed before `origin`, exactly as in the copied §D.4a. Fix kernel_core uses only; there are no exhaustive literals in kernel_core besides :83.
7. Wrappers: every `pagetable_map_*` wrapper in `kernel/memory_management/subsystem_mutation_pagetable_map.rs` (:9 :86 :174 :259 :448 :583 :663 :742 :809 :878) that reaches one of the 7 primitives gains `Tracked(window_perm): Tracked<&LockPerm>`. Replace its `lower.l2_lock ==` ensures with `lower.pagetable_window_locks ==` (or the `pagetable_window_locks_after_new_l2_page` delta for `create_entry_l3`).
8. Mechanical renames elsewhere in owned files: `locked_windows` → `pagetable_window_locks@.dom()` / `pagetable_window_locks@[w]`; `l2_lock_of(p).locked_by_thread(i, t)` → `l2_owner(p, i) is Some && l2_owner(p, i)->Some_thread_id == t`; `l1_tables` → `l1_perm`/`l1_rev_map`. If a term no longer typechecks inside a proof, replace it with its new counterpart, even if the proof then fails.

**Must not change.** Any file outside the owned list. Model semantics beyond this design. No `admit`, no `assume`, no `external_body` other than the six in §B.1/§B.2 (`lock`, `unlock`, `load_acquire`, `store_release`, `page_perm_to_l2_page_map`, `l2_page_map_to_page_perm`). If array `index_mut` does not work in the fork, stop and report; do not add the `entry_mut` fallback yourself. Leave failing proofs failing; do not weaken contracts to make the typecheck pass.

**Runs (2 total).**
1. Typecheck: `systemd-run --user --scope -p MemoryMax=30G ./verify-workspace.sh --package veriflat_kernel_core -- --no-verify`. If `--no-verify` is rejected, use `--verify-only-module pagetable_concurrent::l2_page_map`; Verus typechecks the whole crate before verifying.
2. `... --package veriflat_kernel_core -- --verify-only-module pagetable_concurrent::l2_page_map` must be green.

Report additionally: the final signature of every changed fn (one line each) so B1/B2/B3 can copy it.

## Copied design text (authoritative for this batch)

### A.1 `pagetable_concurrent/l2_page_map.rs` (rewrite, ~315 → ~260 lines)

```rust
pub const L2_ENTRY_LOCK_MASK: usize = 0x200;              // keep (:9)
pub enum SpinLockState { … }                              // keep (:11)
pub open spec fn l2_word_hw_equiv(..)                     // keep (:18)

#[repr(C)]
pub struct L2EntryLock {
    word: AtomicUsize,
    l1: Tracked<Option<PointsTo<PageMap>>>,
    entry: Ghost<PageEntry>,
    owner: Ghost<SpinLockState>,
}
#[repr(C)]
pub struct L2PageMap { ar: [L2EntryLock; 512], addr: Ghost<PageMapPtr> }
```
Deleted: `L2PageGhost` (:33), `L2LockGhost` (:40), and the old `L2PageMap { ar: [AtomicUsize;512] }` (:27).

Closed per-type accessors. The fields are private, so these are the only way to read them from outside the module:
- `L2EntryLock::view(&self) -> PageEntry` (= `entry@`)
- `L2EntryLock::owner(&self) -> SpinLockState`
- `L2EntryLock::l1(&self) -> Option<PointsTo<PageMap>>`
- `L2EntryLock::inv(&self) -> bool`: `l2_word_hw_equiv(word, entry, owner)` and `l1 is Some ⇒ l1->Some_0.addr() == entry.addr && entry.perm.present && !entry.perm.ps`. This is the per-entry ghost/hardware equivalence that the `l2_ghost` side map used to carry.
- `L2PageMap::addr(&self)`
- `L2PageMap::entry_lock(&self, i: L2Index) -> &L2EntryLock` (spec `self.ar@[i]`)
- `L2PageMap::wf(&self)`: `forall i < 512. ar[i].inv()`

### A.2 `pagetable_concurrent/pagetable_concurrent_spec.rs` — `PageTableLower` (:28-38)

| field | fate |
|---|---|
| `l2_perms: Tracked<Map<PageMapPtr, PointsTo<L2PageMap>>>` | kept; becomes the single owner of L2 *and* L1 permissions |
| `l2_ghost: Ghost<Map<PageMapPtr, L2PageGhost>>` | **deleted**, subsumed by `ar[i].entry` |
| `l2_lock: Ghost<Map<PageMapPtr, L2LockGhost>>` | **deleted**, subsumed by `ar[i].owner` |
| `l1_tables: Tracked<Map<PageMapPtr, PointsTo<PageMap>>>` | **deleted**, moved into `ar[i].l1` |
| `l1_rev_map` | kept; `l1_rev_map.dom()` is now the L1 page set |
| `mapping_4k`, `mapping_2m`, `window_stale_cpus` | kept |
| `locked_windows: Ghost<Set<WindowVa>>` | **replaced** by `pagetable_window_locks: Ghost<Map<WindowVa, LockStateU>>` (decision D1) |

New `#[verifier::inline]` open accessors on `PageTableLower`, following the 2026-10-13 rule that a non-inline accessor over `self.lower` breaks congruence of old/new trigger terms. They replace `l2_page` (:319) and `l2_lock_of` (:322):
- `l2_page(p) = self.l2_perms@[p].value()` (kept name)
- `l2_entry(p, i) = self.l2_page(p).entry_lock(i).view()`
- `l2_owner(p, i) = self.l2_page(p).entry_lock(i).owner()`
- `l1_perm(p, i) = self.l2_page(p).entry_lock(i).l1()->Some_0`
- `l1_page(p, i) = self.l1_perm(p, i).value()`

`PageTableWindowView` (:48), `WindowVa` (:58), `window_lock_id` (:72) and `va_range_2m_windows` (:88) are unchanged.

### A.3 Access path (back to `&mut`)
`l2_perms.tracked_borrow_mut(p)` → `PPtr::<L2PageMap>::from_usize(p).borrow_mut(Tracked(perm))` → `&mut l2.ar[i]` (vstd array `index_mut`, i.e. `array[i] = v` / `&mut array[i]` under the fork's `final()` mut-ref syntax). This follows the `PPtr::borrow_mut` pattern of `pagetable_seq/pagemap_util_t.rs:35`.

**This reverses the 2026-10-13 `&self` pilot.** Under that pilot `L2PageMap` methods took `&self` and the ghost state lived in side maps `l2_ghost`/`l2_lock`. Now every mutation takes `&mut L2EntryLock`, and the ghost fields live in the entry. Fallback if `index_mut` on `[L2EntryLock;512]` is not supported by the fork: an `external_body` `L2PageMap::entry_mut(&mut self, i) -> &mut L2EntryLock` with `final(self).ar@ == self.ar@.update(i, final(ret))` (+1 TCB function, Array-style).

`pagetable_seq` is unchanged.

---

### B.1 Entry TCB (`l2_page_map.rs`)
Each contract mentions only this entry's ghost fields plus the `lctx` lock maps that `lock_ensures` already uses.

```rust
// TCB word primitives: one-line, entry-local contracts (hw_inv only, D10)
#[verifier::external_body]
fn load_acquire(&self) -> (w: usize)
    ensures usize2page_entry(w) == self.view()
#[verifier::external_body]
fn store_release(&mut self, w: usize)
    requires (w & L2_ENTRY_LOCK_MASK != 0) == (self.owner() is Some)
    ensures final(self).view() == usize2page_entry(w), final(self).owner() == self.owner(), final(self).l1() == self.l1()

// TCB lock primitives: same shape as RwLock::wlock (rwlock.rs:620, also external_body; Tracked::assume_new)
#[verifier::external_body]
// Mirrors wlock_requires / wlock_ensures (rwlock.rs:977-:983 / :985-:1000): the caller must not already hold this entry;
// "free at acquisition" is an ensures (like `old.locked() == false`, :995), because other threads' contention is physical.
pub fn lock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, Ghost(lock_id): Ghost<LockId>, Ghost(obj_id): Ghost<KernelObjId>) -> (lp: Tracked<LockPerm>)
    requires
        !(old(self).owner() is Some && old(self).owner()->Some_thread_id == old(lctx).thread_id()),
        old(lctx).kernel_view_locking_state() is Acquire,
    ensures
        old(self).owner() is None,
        final(self).view() == old(self).view(),
        final(self).l1() == old(self).l1(),
        final(self).owner() == (SpinLockState::Some { thread_id: final(lctx).thread_id(), lock_id: lp@.lock_id() }),
        lp@.state() is WriteLock,
        lp@.ordering_lock_id() == lock_id,
        lp@.thread_id() == final(lctx).thread_id(),
        lock_ensures(old(lctx), final(lctx), lock_id, obj_id),   // local_context.rs:591
#[verifier::external_body]
pub fn unlock(&mut self, Tracked(lctx): Tracked<&mut LocalContext>, Tracked(lp): Tracked<LockPerm>, Ghost(lock_id): Ghost<LockId>, Ghost(obj_id): Ghost<KernelObjId>)
    requires
        old(self).owner() == (SpinLockState::Some { thread_id: old(lctx).thread_id(), lock_id: lp@.lock_id() }),
        lp@.state() is WriteLock,
        lp@.thread_id() == old(lctx).thread_id(),
        old(lctx).lock_entry_contains(lock_id, obj_id),
    ensures
        final(self).view() == old(self).view(),
        final(self).l1() == old(self).l1(),
        final(self).owner() is None,
        unlock_ensures(old(lctx), final(lctx), obj_id, lock_id),   // local_context.rs:613

// Verified, as today
pub fn get(&self) -> (e: PageEntry) ensures e == self.view()
{ usize2page_entry(self.load_acquire()) }

pub fn set_published_locked(&mut self, Tracked(lp): Tracked<&LockPerm>, value: PageEntry, Tracked(lctx): Tracked<&mut LocalContext>)
    requires self.owner() is Some, lp.obj() == <this entry>, mem_valid(value.addr), old(lctx).kernel_view_locking_state() is Acquire
    ensures final(self).view() == value, final(self).owner() == self.owner(), final(self).l1() == self.l1(),
        final(lctx).cpu_id() == old(lctx).cpu_id(), final(lctx).thread_id() == old(lctx).thread_id(),
        final(lctx).kernel_view_locking_state() is Release, typed_lock_maps_unchanged(old(lctx), final(lctx))
{   // body = today's l2_page_map.rs:222-:239: proof { lctx.enter_kernel_view_release(); }, the bit_vector proof that
    // w = u | L2_ENTRY_LOCK_MASK keeps every page_entry field and has bit 9 set, then self.store_release(w)
}
```
- `lock` does **not** require `lock_id_acyclic` (decision D2). Like `wlock_requires`, it requires only that the caller does not hold this entry and is in the Acquire phase; the entry being free at acquisition is an ensures (D12). The deadlock-freedom obligation stays in verified `lock_window` (B.3).
- `set_published_locked` stays **verified** (bit_vector proof + `store_release`, as at l2_page_map.rs:199-:239 today) and keeps `lctx` in its signature and its internal `lctx.enter_kernel_view_release()` exactly as today (D4 withdrawn by the user).
- `l1` ordering: TCB contracts state only `hw_inv` (word ≡ `entry`, lock bit ≡ `owner`). `l1_inv` (`l1` Some ⇔ entry present ∧ ¬ps, with matching address) is verified and re-established by the caller through `borrow_l1_mut` after `set_published_locked` (D10).

```rust
pub fn borrow_l1_mut(&mut self, Tracked(lp): Tracked<&LockPerm>) -> (r: &mut Tracked<Option<PointsTo<PageMap>>>)
    requires self.owner() is Some, lp.obj() == <this entry>
    ensures final(self).view() == self.view(), final(self).owner() == self.owner(), final(self).l1() == final(r)@
    // body: &mut self.l1  (verified; private field access inside the module)
```

### B.2 Page-level TCB
```rust
#[verifier::external_body]
pub fn page_perm_to_l2_page_map(Tracked(pp): Tracked<PagePerm4k>) -> (r: Tracked<PointsTo<L2PageMap>>)
    ensures r@.addr() == pp.addr(), r@.is_init(), r@.value().addr() == pp.addr(), r@.value().wf(),
        forall|i| i < 512 ==> r@.value().entry_lock(i).view() == PageEntry::empty() && owner is None && l1 is None
#[verifier::external_body]
pub fn l2_page_map_to_page_perm(Tracked(p): Tracked<PointsTo<L2PageMap>>) -> (r: Tracked<PagePerm4k>)
    requires p.is_init(), forall|i| entry_lock(i).view() is empty, owner None, l1 None
```
Compared with today (:246), the new version mints no `LockPerm`s, has no `lctx` and no `lo..hi` pre-locked range.

### B.3 `pagetable_concurrent_lock.rs` rewrite
`lock_window(&self, Tracked(lower): Tracked<&mut PageTableLower>, lctx, l4i, l3i, l2i, lock_id) -> Tracked<LockPerm>` (:10):
- Requires: as today, including `lock_id_acyclic` and `!window_locked_by_thread`.
- Body:
  1. `let tracked perm = lower.l2_perms.tracked_remove(p)`. Removing and re-inserting keeps the `l2_perms` map edit flat; `tracked_borrow_mut` on a `Map` is not available.
  2. `PPtr::borrow_mut(p).ar[l2i].lock(lctx, lock_id, obj)`.
  3. `lower.l2_perms.tracked_insert(p, perm)`.
  4. `lower.pagetable_window_locks@ = pagetable_window_locks.insert(w, WriteLocked)`.
- Ensures `lock_window_eof_transition_framing` + `lock_perm_match` + `lock_ensures`.

`unlock_window` (:53) is symmetric.

New S (`pagetable_concurrent_lock_eof.rs:7/:31`), with the old clauses for `l2_ghost`, `l2_lock`, `l1_tables` and `locked_windows` deleted:
```
lock_window_eof_transition_framing(old, new, p, i, w, t) =
  &&& new.l2_perms@.dom() == old.l2_perms@.dom()
  &&& forall|q| q != p ==> new.l2_perms@[q] == old.l2_perms@[q]       // trigger new.l2_perms@[q]
  &&& new.l2_perms@[p].addr() == old.l2_perms@[p].addr() && new.l2_page(p).addr() == old.l2_page(p).addr()
  &&& forall|j| j != i ==> new.l2_page(p).entry_lock(j) == old.l2_page(p).entry_lock(j)
  &&& new.l2_entry(p, i) == old.l2_entry(p, i) && new.l2_page(p).entry_lock(i).l1() == old.l2_page(p).entry_lock(i).l1()
  &&& new.l2_owner(p, i) == Some(t)
  &&& new.pagetable_window_locks@ == old.pagetable_window_locks@.insert(w, LockStateU::WriteLocked)
  &&& new.l1_rev_map, mapping_4k, mapping_2m, window_stale_cpus == old
```
The EOF closures `lock_window_eof` (:51), `lock_window_eof_window_locks` (:79), `unlock_window_eof` (:103) and `unlock_window_eof_window_locks` (:130) keep their names and are re-proved `[X]`.

### B.4 Write path for L1 / L2 entries (7 lower primitives)
Pattern used by `create_entry_l2` (impl_base:175), `remove_l2_entry` (remove_base:116), `map_2m_page` (impl_map:72) and `remove_structure_page` L1 (structure_scan:132):
```
remove l2 perm → borrow_mut page → e.set_published_locked(&lp, v, lctx)
→ *e.borrow_l1_mut(&lp) = Tracked(Some(l1perm)) | Tracked(None) → reinsert l2 perm
```
`map_4k_page` (:9) and `unmap_4k_page_*` (:9/:65) write into L1. They obtain `&mut PointsTo<PageMap>` through `borrow_l1_mut`, then do `PPtr::<PageMap>::borrow_mut` as in seq. Old: `lower.l1_tables.tracked_borrow_mut` (not available) → `tracked_remove`/`insert`.

These 7 primitives gain `Tracked(window_perm): Tracked<&LockPerm>` (decision D5).

---

### D.1 Field
`pagetable_seq/pagetable_spec.rs:59` `PageTableU` gains `pub pagetable_window_locks: Map<WindowVa, LockStateU>`. Its domain is the windows of existing L2 pages, each `(l4i,l3i,l2i)` with an L2 page under (l4i,l3i). It is `Map::empty()` for IOMMU tables and for any table with no L2 page. The seq `user_view` (:69) sets `Map::empty()`.

### D.2 Projection
`kernel_u_define_spec.rs:5` `pagetable_map_user_view`: `pagetable_window_locks: pt_lower[p].pagetable_window_locks@` (verbatim copy). `iommu_table_map_user_view` :9 gets `Map::empty()`. The process projection :80-:100 hides the table of a zombie, so kill-retire window changes on zombie tables are invisible.

### D.3 Literals without `..`
syscall_new_process_spec.rs :130, syscall_new_process_trace.rs :196, kernel_u_steps.rs :587/:650, projection_publish.rs :98/:269, projection.rs :919/:934 → `pagetable_window_locks: Map::empty()`.

### D.4 Step table
Three spec helpers live in `pagetable_seq/pagetable_spec.rs`. They are shared by the K lockers and the U steps. **D7 (user-approved): use exactly these three names.**
```
pub open spec fn pagetable_window_locks_after_locking_range(m: Map<WindowVa, LockStateU>, range: VaRange4K) -> Map<WindowVa, LockStateU> {
    Map::new(|w: WindowVa| m.dom().contains(w), |w: WindowVa| if va_range_2m_windows(range).contains(w) { LockStateU::WriteLocked } else { m[w] })
}
pub open spec fn pagetable_window_locks_after_unlocking_range(m: Map<WindowVa, LockStateU>, range: VaRange4K) -> Map<WindowVa, LockStateU> {
    Map::new(|w: WindowVa| m.dom().contains(w), |w: WindowVa| if va_range_2m_windows(range).contains(w) { LockStateU::Unlocked } else { m[w] })
}
pub open spec fn pagetable_window_locks_after_new_l2_page(m: Map<WindowVa, LockStateU>, l4i: L4Index, l3i: L3Index, locked_range: VaRange4K) -> Map<WindowVa, LockStateU> {
    Map::new(|w: WindowVa| m.dom().contains(w) || (w.wf() && spec_v2l4index(w.va) == l4i && spec_v2l3index(w.va) == l3i),
        |w: WindowVa| if m.dom().contains(w) { m[w] } else if va_range_2m_windows(locked_range).contains(w) { LockStateU::WriteLocked } else { LockStateU::Unlocked })
}
```
`locked_range` must give the same window set as the `lo..=hi` that `install_one_mmap_4k_directory_page` passes to `pagetable_map_create_entry_l3` (mmap_4k_install_one.rs:175-:184, mmap_4k_create_entry_install.rs:259). B3b confirms this from live code and reports any mismatch before changing a spec.

| syscall / step (file:line) | pagetable_window_locks clause on the caller's table `t` |
|---|---|
| mmap `enter_step` Read (mmap spec :94) | `pagetable_window_locks_after_locking_range(old, range)` |
| mmap `enter_step` Fill (:94) | `pagetable_window_locks_after_locking_range(old, range)` (existing windows only; the enter boundary moves below the lock, D6) |
| mmap `hold`/`release`/`downgrade`/`leaf` (:136/:161/:185/:216) | unchanged (folded into the existing frame clause) |
| mmap `exit_step` (:257) | `pagetable_window_locks_after_unlocking_range(old, range)` |
| map_4k `mmap_4k_directory_step` (build_structure_spec :78) | **exact**: `new_progress.directory is L3 ⇒ pagetable_window_locks_after_new_l2_page(old, v2l4(range[mapped]), v2l3(range[mapped]), range)`, else unchanged. `MissingPageTableLevel::L3` is the only level that calls `pagetable_map_create_entry_l3` (mmap_4k_create_entry_install.rs:78/:259); L4 (new L3 page) and L2 (new L1 page) add no keys; the level is already recorded (:88-:89) |
| share `share_4k_directory_step` (share spec :112) | **exact** (D8, user decision): `Share4k` progress gains `directory: Mmap4kDirectory` (§D.4a). `new_progress.directory is L3 ⇒ pagetable_window_locks_after_new_l2_page(old, v2l4(target_range[shared]), v2l3(target_range[shared]), target_range)` on the target table; L4/L2 ⇒ unchanged. The rank must rise: `mmap_4k_directory_rank(progress.directory) < mmap_4k_directory_rank(new_progress.directory)`, mirroring build_structure_spec.rs:89 |
| unmap enter/exit (:63/:96) | `pagetable_window_locks_after_locking_range` / `pagetable_window_locks_after_unlocking_range` |
| iommu_map enter/exit (:91/:190) | same, on the process pagetable side |
| ipc `lock_tables` (:469) | source and target tables `pagetable_window_locks_after_locking_range` |
| ipc `check` failure (:505) / `unlock_tables` (:586) | `pagetable_window_locks_after_unlocking_range` on both |
| ipc `downgrade` (:555) | unchanged |
| new_process enter (:79) / finish (:205) | source `pagetable_window_locks_after_locking_range` / `pagetable_window_locks_after_unlocking_range`; child table: windows created at publish (:122) via the share step, all Unlocked at finish |
| new_container enter (:102) / finish (:219) | as for new_process |
| **kill `KillProcessPagetableWindowsChanged` (new; drain path only, §D.4b)** | target `t` only: dom unchanged; `changed = dom.filter(|w| new[w] != old[w])`, `changed.len() <= 2`, at most one changed key goes `Unlocked → WriteLocked` and at most one goes `WriteLocked → Unlocked` (filter-len pattern of `kill_process_leaf_step` :354); everything else in `KernelU` unchanged |
| kill `refund` (new kill-local `kill_process_refund_step`, D9) | optional single-window `WriteLocked → Unlocked` on `t` + `kernel_u_container_quota_4k_increased(KernelU { process_map: new.process_map, ..old }, new, owner)` |
| **thread_exit `ThreadExitPagetableWindowsChanged` (new; drain path only, §D.4b; user-approved)** | same shape as `KillProcessPagetableWindowsChanged`, on the exiting process's table |
| thread_exit `refund` (new local `thread_exit_refund_step`; user-approved) | optional single-window unlock + `kernel_u_container_quota_4k_increased(..)` as today (theorem.rs:193) |
| kill retire on zombie tables | invisible (process projection hides the table) |

Share directory step: exact through the new `Share4k.directory` field (§D.4a).

**L2 removal.** The only producer is `l2_page_map_to_page_perm` (l2_page_map.rs:301). Its call chain is:
`remove_l3_entry` (pagetable_concurrent_impl_remove_base.rs:241) ← `remove_structure_page` L2 branch (structure_scan.rs:175) ← `pagetable_map_remove_table_page` (subsystem_mutation_pagetable_map.rs:954; the IOMMU twin at subsystem_mutation_iommu_table.rs:449 is seq). That wrapper has exactly 2 callers, both in kill_process (also run by kill_container):
- `kill_retire_table_page_to_cache` (syscall_kill_process_retire_pages.rs:714, call :834). Its only caller is :616, in `kill_retire_table_page_and_unlock` (:510), which requires `prc_mp[target].view().zombie` (:562).
- `kill_retire_table_page_scoped_to_cache` (retire_pages_scoped.rs:293, call :400). Its only caller is :273, in `kill_retire_table_page_scoped_and_unlock` (:178). That function's only caller is :163, in `kill_retire_next_table_page_scoped` (:19), which requires zombie (:50). That one is reached from retire_pages.rs:353, inside `kill_retire_table_pages` (:152), which requires zombie (:174).

In both chains the table belongs to a zombie target, and the projection (kernel_u_define_spec.rs:87) sets `pagetable: None` for zombies. **No visible step deletes window keys.** `unmap_4k`, `thread_exit`, `iommu_unmap` and every other syscall have no call to `pagetable_map_remove_table_page` or `remove_structure_page` (grep), so they never free an L2 page and need no remove clause. By contrast, the kill reclaim window lock (reclaim_scoped.rs:146) runs on a target that is `being_killed`, not zombie (:30), so it stays visible and needs `KillProcessPagetableWindowsChanged` on its drain path (§D.4b). L2 creation: the mmap directory, share directory and new_process/new_container publish steps add 512 keys, stated exactly through `add_l2_page`.

### D.4a `Share4k` directory level (D8, user decision)
- `proc/thread_def.rs:83`: `Share4k { source_range, target_range, shared, origin }` → `Share4k { source_range: VaRange4K, target_range: VaRange4K, shared: usize, directory: Mmap4kDirectory, origin: Share4kOrigin }`. This mirrors `IommuMap4k { .., directory: Mmap4kDirectory }` (:77) and `Mmap4k` (:73).
- New `share_4k_progress_after_directory(progress, level)` in map_4k/share_mapping_4k_spec.rs. It is the twin of `mmap_4k_progress_after_directory` (mmap_4k_build_structure_spec.rs:28-:33) and sets `directory: mmap_4k_installed_directory(level)`. `share_4k_progress_after_leaf` (:6-:11) resets `directory: Mmap4kDirectory::None`.
- `share_4k_directory_at` (:26) / `share_4k_directory_step` (:112):
  - the progress thread's `syscall_progress` becomes `share_4k_progress_after_directory`;
  - add the rank clause `mmap_4k_directory_rank(old.directory) < mmap_4k_directory_rank(new.directory)`;
  - add the target-table window clause from §D.4. The `post == KernelU { thread_map: .., container_map: .., ..pre }` form gains `process_map: pre.process_map.insert(target, ProcessU { pagetable: Some(PageTableU { pagetable_window_locks: <clause>, ..t }), ..})`.
- Exec: `install_one_mmap_4k_directory_page` (mmap_4k_install_one.rs:132 says the progress thread's progress is unchanged in the Share4k case) gains one ghost-only `set_thread_syscall_progress(progress_thread, Ghost(share_4k_progress_after_directory(..)))` under the held progress-thread write lock. It has no runtime cost (the argument is `Ghost`).
- Every exhaustive `Share4k { … }` literal or pattern gets `directory: Mmap4kDirectory::None`. Accessor uses (`->Share4k_*`) and `{ .. }` patterns are unchanged.
  - **B0:** proc/thread_def.rs:83.
  - **B3b (map_4k):** share_mapping_4k_spec.rs:8 (+ new fn, :26, :112); share_mapping_4k_trace.rs (directory trace lemma); share_mapping_4k.rs:874/:1006/:1149; share_mapping_4k_child_structure.rs:101/:341/:571; mmap_4k_install_one.rs:132 (+ :329-:355 Share4k branch).
  - **B3d (ipc):** syscall_ipc_spec.rs:514; syscall_ipc_pages_trace.rs:359/:543/:566/:631/:813; syscall_ipc_pages_share.rs:225/:408; syscall_ipc_pages_prepare.rs:57/:218/:366/:556/:716/:1076/:1196.
  - **B3e (new_process):** syscall_new_process_spec.rs:134; syscall_new_process_trace.rs:199/:256; syscall_new_process_publish_step.rs:122/:139; syscall_new_process_publish.rs:165; syscall_new_process_with_iommu_publish.rs:181; syscall_new_process_helpers/finish.rs:80/:281; syscall_new_process_share_finish.rs:112.
  - **B3e (new_container):** syscall_new_container_spec.rs:166; syscall_new_container_trace.rs:138/:176; syscall_new_container_publish.rs:157/:259/:384; syscall_new_container_commit.rs:455/:772/:889; syscall_new_container_commit_share.rs:131; syscall_new_container_share.rs:258/:369/:521/:774/:934.
  - **B4 (NI):** ni_share_4k.rs:8/:19 (`share_4k_directory_step_lr/_iso`); theorem.rs:118/:331 keep the label.
  - Sites that read no `directory` and use `{ .. }` or accessors need no edit: projection_at.rs:406, kernel_u_steps.rs:665-:709, kernel_step_spec.rs:812-:825, syscall_ipc_pages_fill.rs:32-:36, mmap_4k_build_structure.rs:93/:391/:688, ni_share_4k.rs:53-:65, theorem.rs:245.

### E.1 Invariant changes (`pagetable_concurrent_spec.rs`)
| predicate | new body | approval |
|---|---|---|
| `wf_l2` :514 | per (p∈l2_perms.dom, i): `l2_page(p).wf()`; `addr` matches; clause 2: present ∧ ¬ps ⇔ `l1()` Some, then `l1_perm.addr()==entry.addr` ∧ `l1_rev_map.contains(entry.addr)` | restatement of existing |
| `l2_tokens_paired` :497 | **deleted** (entry `inv` carries it) | delete |
| `wf_l1` :542, `user_only` :555, `rwx_upper_level_entries` :567 | quantify `(p,i)` with `l1() is Some` instead of `l1_tables.dom` | restatement |
| `table_pages_wf` :577 | L1 disjointness over `l1_rev_map.dom()` | restatement |
| `tables_reachable_wf` :589 | L1 part over `l1_rev_map.dom()` | restatement |
| `wf_mapping_4k` :622 | read through `l1_page` | restatement |
| `wf_window_locks` :651 | (a) `forall w ∈ pagetable_window_locks.dom ⇒ window_exists(w) ∧ w ≥ kernel_l4_end ∧ pagetable_window_locks[w] == (owner is Some ? WriteLocked : Unlocked)`; (b) **new dom clause**: `forall p∈l2_perms.dom, i<512 ⇒ pagetable_window_locks.contains_key(w(p,i))` | approved by the user (D1) |
| `pagetable_window_stale_cpus_only_when_locked` (pagetable_map_spec :33) | `l2_owner(p,i) is Some` | restatement |
| `pagetable_window_typed_lock_map_aligned` (:117) | entry owner vs lctx typed map | restatement |

The old "every locked slot ∈ `locked_windows`" two-way alignment becomes clause (a).

## Rules (repository AGENTS.md + skills; read `AGENTS.md` and invoke the `veriflat-proof`, `veriflat-kernel-model` and `veriflat-build` skills before editing)
- Worktree: `/home/xiangdc/VeriFlat/.claude/worktrees/concurrent-pagetable-kill-container-598619` (run all commands from it). Edit **only** the files listed under "Owned files". Never touch other files, never reset/stash/clean, and **never commit**.
- Design reference (read only the sections named here): `/tmp/claude-1000/-home-xiangdc-VeriFlat--claude-worktrees-concurrent-pagetable-kill-container-598619/242142bb-2dbe-4203-89c7-86f8a4fe7835/scratchpad/l2_entry_lock_design.md`.
- **U step span (user principle 2026-10-29):** "所有的 U 步都尽量跨度大一点。每个 syscall 的设计都是性能最优先，然后在不改 exec 代码的前提下 U 跨度尽可能大。runtime 性能是第一优先级."
  - Never reorder locks or add runtime exec work for the U model. Ghost-only exec calls (a `Ghost(..)` argument) are allowed.
  - Between each window lock and its unlock, list every boundary call. A stutter (`kernel_step_boundary_nonlock_fields_unchanged`, `rebase_snapshot_k_if_unchanged`, a u_eq lemma call) that becomes false because of `pagetable_window_locks` is deleted or moved, so the delta folds into the next recorded step. Do not turn it into a new step.
  - If you find a recorded or exec-forced boundary inside a held window that the design's §D.4b table does not list, **stop and report**; do not add a step.
- Exec equations are K-only: no `reveal` of `*_wf`/`*_inv`, no U reasoning. Use wrapper K→U lemmas and the operation's `*_trace.rs` lemmas.
- No `exists`/`choose`, no `assert(forall ..)` in kernel `src/` (the NI crate may use `assert(forall ..)`), no `#[verifier::spinoff_prover]`, and no invariants keyed on `SyscallProgress`.
- New lemmas: only `*_wf_at` point lemmas, EOF closures, fold lemmas, EOL loop summaries, wrapper-layer K→U lemmas, or operation-local trace lemmas (`<op>_<step>_from_u`, `_pre_from_k`, composition) are allowed without approval. Name them `<premise>_implies_<conclusion>`. Any other new lemma, framing spec, or invariant: stop and report. List every added lemma or closure in your report.
- Dense canonical style (proof skill `style-and-discipline.md`; reference: `src/kernel/implementation/syscall_alloc_quota/`).
  - One contract clause per line. Short proofs go on one line.
  - Blocks with `let`: each `let` and each `&&&` on its own line.
  - Pack parameters and arguments into balanced groups; no staircased expressions.
  - Remove diagnostic code before you report.
  - Finish with a style pass over every `src/**/*.rs` file you changed.
- Verification: focused runs only. Command shape (one blocking call; chain all modules of a batch into one run):
  `systemd-run --user --scope -p MemoryMax=30G ./verify-workspace.sh --package <pkg> -- --verify-only-module <mod> [--verify-only-module <mod2> ...]`
  - Module names are rooted at the crate's lib module, e.g. `syscall_ipc::syscall_ipc_pages_lock`, `map_4k::share_mapping_4k_spec`, `pagetable_concurrent::l2_page_map`, `kernel::memory_management::subsystem_mutation_pagetable_map`.
  - Dependencies are built unverified. All runs serialize on one flock, so expect queueing.
  - Do not run whole-package, workspace, NI-wide or monolith runs; the integration agent does those.
- Token economy: wait for your own run inside one blocking shell call (foreground with a timeout, or one polling loop). Do not hand back mid-wait. Grep logs (`error`, `rlimit`, `verified`) instead of reading them whole. Batch all edits before each run, and fix all errors together.
- Kill stray Verus processes only by exact name (`pkill -x rust_verify`, `pkill -x z3`); never use `pkill -f`. Run ad-hoc scripts under `timeout`.
- Frozen API (from B0, do not change): everything in `src/pagetable_concurrent/l2_page_map.rs`; the `PageTableLower` field list and inline accessors in `pagetable_concurrent_spec.rs`; `PageTableU.pagetable_window_locks`; the three `pagetable_window_locks_after_*` helpers; the `Share4k.directory` field. If one of them is wrong, report; do not edit.

## Report (hand back as your final message, ≤40 lines)
- Changed files (absolute paths).
- Every added or deleted lemma, closure, or spec, with file:line.
- Verification run numbers, each with verified/errors counts.
- Module rlimit before → after for every touched module (use the base numbers from the first run's log, or say "no base").
- Any deviation from this brief, any stop-and-report item, and any boundary the §D.4b table missed.
