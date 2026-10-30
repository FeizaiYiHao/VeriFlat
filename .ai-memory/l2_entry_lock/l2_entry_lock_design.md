# L2 entry locks + window locks in U — implementation design

Base: worktree `concurrent-pagetable-kill-container-598619`, HEAD 7e6f538 (nonlock U layer already deleted).
Supersedes §2 of `window_locks_in_u_design.md`; its §1 inventory and §3 step table remain valid and are refined in §D.4.
Paths are relative to `src/` unless they start with `noninterference/`. `[A]` = needs user approval. `[X]` = exempt (EOF closure, `*_wf_at`, fold, or K→U wrapper/trace lemma).

---

## A. Structures and accessors

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

## B. TCB contracts and `lock_window`/`unlock_window`

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

## C. Touched sites, by file

Counts are approximate. "hits" = textual occurrences of `l2_ghost|l2_lock|l1_tables|locked_windows|l2_lock_of`.

### C.1 crate `veriflat_kernel_core` — module `pagetable_concurrent` (B1)
- `l2_page_map.rs`: rewrite (§A.1, §B.1–B.2).
- `pagetable_concurrent_spec.rs`:
  - struct :28; accessors :319/:322.
  - `is_empty` :351 → `pagetable_window_locks@.dom().is_empty()`, `l1_rev_map.dom().is_empty()`.
  - `page_closure` :365 → `l1_rev_map@.dom()` replaces `l1_tables@.dom()`. **This is a cross-crate contract (allocator/page closure)**: the value is equal under `wf`, but the term changes.
  - `spec_resolve_mapping_4k_l1` :407 → `l1_page(l3.addr, l2i)`.
  - `window_locked_by_thread` :437 → `l2_owner(p,i) is Some && l2_owner(p,i)->Some_thread_id == t`.
  - `window_locked` :444 → `pagetable_window_locks@[w] == WriteLocked`.
  - `hidden_leaves_in_locked_windows` :449, `window_view` :465, `window_free_for` :479.
  - wf: `l2_tokens_paired` :497 (delete; covered by `L2PageMap::wf`), `wf_l2` :514, `wf_l1` :542, `user_only` :555, `rwx_upper_level_entries` :567, `table_pages_wf` :577, `tables_reachable_wf` :589, `wf_mapping_4k` :622, `wf_window_locks` :651, `wf` :668 (§E).
- `pagetable_concurrent_lock.rs` :10/:53 and `pagetable_concurrent_lock_eof.rs` :7-:130: §B.3.
- `pagetable_concurrent_impl_base.rs`:
  - `create_entry_l3` :66: no longer receives minted perms. After `page_perm_to_l2_page_map` it locks `lo..=hi` one by one with `e.lock(lctx, window_lock_id(..), ..)`. The loop has `decreases hi+1-k` and runs on the unpublished page, so it has no acyclic obligation. It returns `Tracked<Map<L2Index, LockPerm>>` as today.
  - `pagetable_window_locks@ = pagetable_window_locks_after_new_l2_page(..)` (§D.4) replaces `locked_windows.union`.
  - EOF `create_entry_l3_eof*` re-proved `[X]`.
  - `create_entry_l2` :175 (set_published :229): pattern B.4.
  - `create_entry_l4` :10: unchanged except the S fields.
- `pagetable_concurrent_impl_remove_base.rs`: `unmap_4k_page_user_view` :9, `unmap_4k_page_kernel` :65, `remove_l2_entry` :116 (:166), `remove_l3_entry` :182 (L2 page → `l2_page_map_to_page_perm`, requires all owners None, `pagetable_window_locks` minus 512 keys), `remove_l4_entry` :256.
- `pagetable_concurrent_impl_map.rs`: `map_4k_page` :9, `map_2m_page` :72 (:115).
- `pagetable_concurrent_util.rs`:
  - `get_entry_l2` :100 / `get_entry_2m_l2` :123: `.ar[i].get()`.
  - `get_entry_l1` :146 gains an `l3_entry: &PageEntry` / `l2i` argument and reads `l1_perm(l3.addr, l2i)`.
  - `spec_empty` :178 / `tracked_empty` :186 lose 3 fields.
  - `resolve_mapping_4k_l2/_l1` :266/:299.
- `pagetable_concurrent_structure_scan.rs`: `remove_structure_page` :132 (L1 branch: window perm; L2 branch requires `forall i. l2_owner(p,i) is None`; ensures `pagetable_window_locks@ ==` / `.remove_keys`); `scan_l2_table` :219; `l1_table_has_no_leaf` :265.
- `pagetable_concurrent_range.rs` :188-:586 (`get_entry_l1` argument), :689, :778.
- `pagetable_concurrent_lemma.rs`: `l2_tokens_paired_at` :131 (delete), `wf_l2_at` :147, `wf_l1_at` :157, `tables_reachable_wf_l1_at` :178, `wf_mapping_4k_at` :189, `wf_window_locks_va_at` :220, `wf_window_locks_slot_at` :231. All are restated `[X]`.
- `pagetable_concurrent_util_t.rs:10` `retype_page_to_pagetable_c_and_insert`: empty-lower construction.

### C.2 crate `veriflat_kernel_core` — other modules (B2)
- `memory_management/pagetable_map_spec.rs`:
  - `pagetable_hidden_leaves_only_when_locked` :16.
  - `pagetable_window_stale_cpus_only_when_locked` :33: `l2_lock.dom()`/`l2_lock_of(p).locked(i)` → `l2_perms@.dom()`/`l2_owner(p,i) is Some`.
  - `pagetable_lower_wf` :59.
  - `pagetable_window_holders_hold_pagetable` :80.
  - `pagetable_lower_backup_wf` :101. The backup `view_ghost()` is a `PageTableLower`, so it carries the new fields automatically.
  - `pagetable_window_typed_lock_map_aligned` :117: owner from the entry, not `l2_lock`.
- `locker_unlocker/locker_unlocker_pagetable_window.rs` :11/:134: ensures frame list `l2_ghost`/`l1_tables` → `l2_perms`-except-entry (reuse the S clauses of B.3 through `lock_window`'s ensures), plus `pagetable_window_locks` insert.
- `locker_unlocker/locker_unlocker_pagetable_range_windows.rs`:
  - `lock_pagetable_range_windows` :24 (loop :232), `unlock` :263 (:442), `_existing` :470 (:693), `unlock_existing` :723 (:919).
  - Each loop invariant gains `pagetable_window_locks@ == pagetable_window_locks_after_locking_range(old, prefix_k)` (or `_after_unlocking_range`).
  - EOL loop summary `[X]` if the loops exceed 5 s.
  - `pagetable_l3_entry_links_l2` :946.
- `kernel_step_wrappers/subsystem_mutation_pagetable_map.rs`:
  - The 11 KernelK wrappers (:9 :86 :174 :259 :355 :448 :583 :663 :742 :809 :878). Each loses its `lower.l2_lock ==` ensures; the 9 window-writing ones gain `Tracked<&LockPerm>`.
  - `remove_table_page` :878 uses `pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows` (:948); its body changes from `l2_lock` to `l2_owner`. It is an existing lemma, restated, not new.
- `kernel_step_wrappers/` U-eq lemmas (9 sites, §E.3).
- `kernel/kernel_u_define_spec.rs` :5/:9 projection (§D.2); `kernel_u_steps.rs` :587/:650 literals.
- `pagetable_seq/pagetable_spec.rs` :59 `PageTableU` field (§D.1).
- `kernel/init.rs`:
  - `boot_dom0_pagetable_model` :92-:96: `l1_tables` → placed into entries.
  - :276/:288 ensures `locked_windows == empty` → `pagetable_window_locks@ == all-unlocked over boot L2 windows`.
  - :640, :872-:953 (cpu tables).
  - The boot builder needs a verified loop that moves `l1_tables[l1]` into `ar[i].l1`. It has an exec `decreases` and is bounded by 512 × (#L2 pages).
- `kernel/cpu_tlb_management/tlb_wf_spec.rs` :72/:80: `window_l2_page` is unchanged; no edit beyond the re-proof.
- `pagetable_seq/pagetable_window_stale_eof.rs`: `l2_lock` → `l2_owner` reads.
- `kernel/projection*.rs` literals: projection.rs :919/:934, projection_publish.rs :98/:269 → `pagetable_window_locks: Map::empty()`.

### C.3 Syscall crates (B3a–f)
Each item lists window-perm plumbing (D5), U-eq/step edits (§D) and `get_entry_l1` argument edits.
- **mmap_4k** (B3a):
  - read_enter.rs :269/:274.
  - syscall_mmap_4k_fill_enter.rs: move the proof-only enter boundary block (:134-:146) below the window lock at :148 and delete the u_eq + rebase at :149 (D6; no exec statement moves).
  - map_range.rs :360.
  - syscall_mmap_4k_map_owned.rs :154.
  - `mmap_4k_create_entry_install.rs` :259/:266/:269 (create_entry_l3 window delta → directory step).
  - spec/trace syscall_mmap_4k_spec.rs :94-:329.
- **map_4k share/structure** (B3b, crate `veriflat_map_4k`): share_mapping_4k_leaf_copy.rs :146/:149; mmap_4k_build_structure_spec.rs :78; share_mapping_4k_spec.rs :26/:112 (+ trace).
- **unmap_4k + iommu_map_4k** (B3c):
  - unmap_4k_pagetable.rs :175/:181, unmap_4k_helpers.rs :206, unmap_4k_present.rs :68/:84/:89/:166.
  - unmap_4k_reclaim_one.rs :89/:91/:199/:333, unmap_4k_reclaim.rs :148/:150, unmap_4k_remove.rs :89/:187.
  - syscall_unmap_4k_spec.rs :63/:96.
  - iommu check.rs :372/:409, exit.rs :121; syscall_iommu_map_4k_spec.rs :91/:190.
- **ipc** (B3d): ipc_pages_lock.rs :125/:126/:134/:135/:231/:342; syscall_ipc_spec.rs :469/:505/:555/:586 + trace.
- **new_process + new_container** (B3e):
  - lock_helpers.rs :585/:589, finish_release.rs :156/:158; syscall_new_process_spec.rs :79/:122/:130/:205; trace :196.
  - lock_owners.rs :337, share_helpers.rs :466/:468, release_source.rs :77; syscall_new_container_spec.rs :102/:159/:219.
- **kill_process + kill_container + thread_exit** (B3f):
  - syscall_kill_process_retire_pages.rs :465/:479/:622/:834; retire_pages_scoped.rs :117/:131/:280/:400.
  - syscall_kill_process_reclaim_scoped.rs :128/:237/:245/:262; reclaim_scoped_last.rs :131/:163/:166-:170.
  - syscall_kill_process_spec.rs :343-:554 + trace; syscall_kill_container_spec.rs :313.
  - thread_exit: reclaim path only (perm plumbing).

### C.4 NI (B4) — `noninterference/src/`
- theorem.rs: `StepLabel` :23-:55 (+`KillProcessPagetableWindowsChanged`, +`ThreadExitPagetableWindowsChanged`), mapping :154-:193 (KillProcessRefund :172 → `kill_process_refund_step`, ThreadExitRefund :193 → `thread_exit_refund_step`), dispatch :331/:382+/:400/:420.
- ni_kill_process.rs: new `window_locked_lr/_iso`; patch `refund` :789/:810.
- ni_mmap_4k, ni_unmap_4k, ni_iommu_map_4k, ni_ipc (:317/:328), ni_share_4k, ni_new_process, ni_new_container, ni_kill_container: re-prove `_lr`/`_iso` over the window delta. `domain.rs:26` `domain_view` copies `ProcessU`, so it needs no edit.

---

## D. U side

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

### D.4b U step span (user principle 2026-10-29)
**Principle.** "所有的 U 步都尽量跨度大一点。每个 syscall 的设计都是性能最优先，然后在不改 exec 代码的前提下 U 跨度尽可能大。runtime 性能是第一优先级."
- Exec code is fixed by runtime performance. Never reorder locks or add exec work for the U model.
- Given that exec code, U boundaries are as coarse as possible. Lock/unlock and ghost-only changes fold into the adjacent recorded step.
- A u_eq / `rebase_snapshot_k_if_unchanged` / `kernel_step_boundary_nonlock_fields_unchanged` stutter that becomes false under `pagetable_window_locks` is deleted or moved, so the stretch merges into the next recorded step. It is not turned into a new step.
- A new step is allowed only when an exec-forced boundary sits between a window lock and its unlock. An exec-forced boundary is one where 2PL forces a boundary because a lock is taken after an unlock.

**Stutter vs. recorded.**
- `kernel_step_boundary_nonlock_fields_unchanged` (kernel_step_wrappers/boundary_steps.rs:9) is a stutter: it records nothing and needs U equality with the snapshot.
- `drain_4k_cache_batch` (free_4k_page/drain_4k_cache_batch.rs:6) opens with `record_user_view_change(steps, snapshot_u, U(old krnl))` (kernel_total_define_spec.rs:15). Its per-page loop (:150 `wlock_page` / :152 `wunlock_page` / :163 boundary) is exec-forced: a page unlock is followed by the next page lock.

**D6 (mmap Fill) has no exec change.** In syscall_mmap_4k_fill_enter.rs, lines :128-:147 between `set_thread_syscall_progress` (:131, ghost-only) and the window lock (:148) are proof blocks only. The `kernel_step_boundary_thread_syscall_progress_changed` block (:134-:146) moves below :148, and the u_eq + `rebase_snapshot_k_if_unchanged` at :149 is deleted. The enter step then covers "progress set + existing range windows locked". No exec statement moves.

**Kill reclaim, analysed in full.** `kill_reclaim_unmapped_4k_page_scoped` (syscall_kill_process_reclaim_scoped.rs:146) runs on a `being_killed`, non-zombie (:30), hence U-visible table. It locks the window at :237.
- *Shared branch* (:258-:275): unlock at :262, then a stutter at :273-:274. Lock and unlock are net-zero, so the u_eq still holds and needs a `pagetable_window_locks` equality fact. **No new step.**
- *Last branch* (`kill_reclaim_last_4k_mapping_scoped`, syscall_kill_process_reclaim_scoped_last.rs:18), between lock (:237) and unlock (:163):
  - (1) stutter :129-:132. It is proof-only (state was Acquire and nothing is published), so delete it.
  - (2) `kill_retire_lock_cache` (syscall_kill_process_retire_pages.rs:638). It requires `steps.snapshot_k() == *old(krnl)` and ends with a stutter at :704-:707.
    - No-drain path (else :700-:702): proof-only, deletable.
    - Drain path (:672-:697): `drain_4k_cache_batch` → its exec-forced per-page boundaries. The pool unlock (:696) before the next lock (`wlock_allocator_quota_4k`, _last.rs:151) is also exec-forced.
  - (3) The recorded credit step at :166-:171 (`kernel_page_freed_to_owner_quota_implies_u_step` + `kernel_step_boundary_user_view_changed`, label `KillProcessRefund`).
  - **Result:** on the no-drain path the lock and unlock fold net-zero into the credit step, which then needs no window clause. On the drain path, drain's opening `record_user_view_change` records `{pre, window locked}`. That step is `KillProcessPagetableWindowsChanged`, and the credit step absorbs the unlock (D9). So `KillProcessWindowLocked` cannot be dropped; it shrinks to the drain path.
  - Contract edits (proof-only, no exec change): delete the :129-:132 stutter. `kill_retire_lock_cache` drops `snapshot_k() == *old(krnl)` in favour of the stutter-precondition set (as `drain_4k_cache_batch` :17-:28 states it) and ensures `steps.view() == record_user_view_change(old.view, old.snapshot_u, U(old krnl))` on the drain path, otherwise unchanged. Its 6 callers must keep proving that: kill_container_retire_root.rs:216, _last.rs:138/:297, retire_pages_scoped.rs:144, retire.rs:273, retire_pages.rs:492. The zombie-table callers see no window change.
- **New finding, same shape:** `reclaim_unmapped_4k_page` (map_4k/unmap_4k_reclaim_one.rs:10, window lock :89, unlock :91) → `reclaim_last_4k_mapping` (unmap_4k_reclaim_last.rs:102: stutter :221-:222, deletable) → `reclaim_last_lock_4k_cache_with_room` (unmap_4k_reclaim_last_cache.rs:7: drain :70, exec-forced pool-unlock boundary :73-:74). It is called from:
  - **thread_exit** `thread_exit_reclaim_unmap_leaves` (syscall_thread_exit_reclaim_release.rs:534; process `!zombie` :300, so visible) → needs `ThreadExitPagetableWindowsChanged` on the drain path, and `ThreadExitRefund` (:553) absorbs the unlock. (Step, label and refund step user-approved.)
  - **kill** `kill_reclaim_unmap_leaves` (syscall_kill_process_reclaim_release.rs:638; target being_killed, visible) → `KillProcessPagetableWindowsChanged` again; refund at :660.
  - These loops run once per page. A drain step in iteration k can carry "window k−1 unlocked + window k locked", hence the ≤2-change shape in §D.4.
- **Zombie retire u_eq sites** (syscall_kill_process_retire_pages.rs:479, syscall_kill_process_retire_pages_scoped.rs:131): the table is hidden, so swap to `kernel_lock_states_unchanged_except_tables_of_implies_u_eq(.., Some(target))`. No step.
- `clear_4k_mapping_present` (unmap_4k_present.rs:68 lock … :89 unlock): no boundary in between, so net-zero folds into the caller's recorded leaf step (thread_exit_reclaim_leaf.rs:95, kill reclaim_release.rs:161). No step.

**Boundaries kept, per syscall** (each one exists because of an exec event; a window delta folds into it):

| syscall | recorded boundaries that carry a window delta | why they cannot be removed |
|---|---|---|
| mmap_4k | enter (Read :286 / Fill moved below :148), directory/leaf steps (unchanged windows), exit (map_range.rs:368) | enter/exit are big-lock acquire/release points; directory steps are page-allocation steps |
| map_4k share | `Share4kDirectory` (adds keys exactly), `Share4kLeaf` | per-page allocation and per-leaf boundaries already exist in exec |
| unmap_4k | enter (syscall_unmap_4k_pagetable.rs:175 lock; next recorded boundary), exit (:316-:323) | big-lock rlock/runlock |
| iommu_map_4k | enter (check.rs:372), exit / failure (:409, exit.rs:121) | same |
| ipc | `lock_tables` (pages_lock.rs:125-:135, recorded at :1305), failure stutter :749-:750 (B3d confirms the windows are unlocked again at :231/:342 before it; otherwise it moves or is deleted per the rule), `unlock_tables` | rendezvous lock retry loop |
| new_process / new_container | enter: new_process lock_helpers.rs:585 (held on precheck success; the :589 unlock on failure is net-zero inside the failure stretch), new_container lock_owners.rs:337; finish: finish_release.rs:156/:158, share_helpers.rs:466/:468, release_source.rs:77 (unlocks fold into the finish/release step) | big-lock and owner-lock acquire/release |
| kill_process | `KillProcessPagetableWindowsChanged` (drain path only), `KillProcessRefund` (absorbs unlock); zombie retire invisible | drain per-page lock/unlock (drain_4k_cache_batch.rs:150-:163) |
| thread_exit | `ThreadExitPagetableWindowsChanged` (drain path only), `ThreadExitRefund` | same drain loop |

Rule for every implementing agent: list every boundary call between each window lock and its unlock. Delete or move stutters. Fold the delta into the next recorded step. If a recorded or exec-forced boundary appears that this table does not list, stop and report before adding a step.

### D.5 Traces and wrappers
- Each `*_trace.rs` `_from_u` lemma for the steps above gets the new clause in its partial trace `[X]`.
- The `_pre_from_k`/`_from_u` bridging lemmas take the window delta from the KernelK wrapper ensures (`lock_pagetable_*` ensures `pagetable_window_locks@ == pagetable_window_locks_after_locking_range(..)`), so they stay verbatim-K-ensures → U-spec lemmas `[X]`.
- The kill and thread_exit traces accept the optional `*PagetableWindowsChanged` step wherever a drain boundary can occur inside a held window (§D.4b), and their refund trace lemmas (`kill_trace_from_refund`, `kill_trace_from_scoped_credit`, `thread_exit_trace_from_refund`) take the optional unlock.

### D.6 NI
- `KillProcessPagetableWindowsChanged` and `ThreadExitPagetableWindowsChanged` get `_lr`/`_iso`. The changed table belongs to the caller's domain (kill: the target is in the killer's subtree; thread_exit: own process).
- `Share4kDirectory` `_lr`/`_iso` (ni_share_4k.rs:8/:19) are re-proved over the new `directory` field and the target-table window clause.
- `pagetable_window_locks` is a field of `ProcessU.pagetable` and is copied through `domain_view`. Steps change it only on the caller's own table (ipc: source + target). The ipc peer-table argument is identical to the big-lock mode argument (`isolated`/`endpoint_iso` exclude peer ∈ b).
- `refund` `_lr`/`_iso` (ni_kill_process.rs :789/:810; ni_thread_exit.rs :393/:403) are patched for the optional unlock.

---

## E. Invariants and lemmas

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

### E.2 Lemmas
- `[X]`: all `*_wf_at` restatements in pagetable_concurrent_lemma.rs (:147 :157 :178 :189 :220 :231); `lock_window_eof*` / `unlock_window_eof*` / `create_entry_l3_eof*` closures; trace `_from_u`; kill and thread_exit refund trace lemmas with the optional unlock; EOL summaries for the four range-window loops.
- New approved specs: the three `pagetable_window_locks_after_*` helpers (D7), `kill_process_pagetable_windows_changed_step`, `kill_process_refund_step`, `thread_exit_pagetable_windows_changed_step` and `thread_exit_refund_step`, plus the labels `KillProcessPagetableWindowsChanged` / `ThreadExitPagetableWindowsChanged`.
- Existing lemmas restated in place, with no new statement shape: `pagetable_l2_windows_unlocked_when_wlocker_holds_no_windows` (subsystem_mutation_pagetable_map.rs:948).
- Rename to `<premise>_implies_<conclusion>`: that lemma becomes `wlocker_holds_no_windows_implies_l2_windows_unlocked`. This is an in-scope rename.

### E.3 U-equality lemmas (9; premise inlined, no new lemma)
In each per-table lock-mode forall, add:
`pagetable_c(post.pt_mp, post.pt_lower.view(), p).lower.pagetable_window_locks == pagetable_c(pre.pt_mp, pre.pt_lower.view(), p).lower.pagetable_window_locks`
For the `match table` / `Some(p)` variants, add the same for `p`.
- projection.rs: `kernel_thread_write_held_section_implies_u_eq` :8 (`..*pre` shape, nothing to add); `kernel_nonlock_fields_and_lock_states_unchanged_implies_u_eq` :29 (~:52); `kernel_lock_states_unchanged_except_tables_of_implies_u_eq` :98 (~:142, zombie excluded); `..._u_process_map` :224; `kernel_restored_locks_implies_u_eq` :617 (~:661).
- bindings.rs: `kernel_snapshot_nonlock_fields_and_lock_states_unchanged_implies_u_eq` :32.
- release.rs: `kernel_page_then_pcid_allocator_unlocks_implies_u_eq` :6 (post == `KernelK{pg_arr, pcid_allc_mp, ..*pre}`, nothing to add).
- kernel_step_wrappers.rs: `end_kernel_step_restored_locks` :158, `_with_iommu_table` :265, `end_kernel_step_unchanged` :387.

Callers that drop and re-take window locks inside one step (kill reclaim_scoped :262 shared branch; unmap reclaim_one :89/:91) must supply equal `pagetable_window_locks`. The lock/unlock pair inside one stretch restores the map; this needs a `insert(w, W).insert(w, U) == insert(w, U)` + `old[w]==U` fact, discharged by `=~=`.

---

## F. Risk, cost, TCB

### F.1 TCB assumption (soundness argument for multiple `&mut KernelK`)
1. **Semantic layer (primary; user's argument, 2026-10-29: "虽然我们现在容许多个线程有 KernelK 的 mut ref，KernelK 顶层的所有字段都是在锁保护下的。这是这个方法论和 rust 冲突但是不产生问题的论据").**
   - Every top-level `KernelK` field, and every `L2EntryLock` field (`word`, `l1`, `entry`, `owner`), is read or written only by the holder of its protecting lock.
   - For an `L2EntryLock`, that is the holder of the window (小锁), or the pagetable big-lock (大锁) write holder under the `pagetable_window_holders_hold_pagetable` discipline. `word` is additionally touched by the CAS of a contending `lock`, which is an atomic.
   - Verus enforces this: every access path to these fields requires the matching `LockPerm`/`PointsTo` (`borrow_mut` requires `wlocked_by` + perm; `set_published_locked`/`borrow_l1_mut`/`unlock` require the entry `LockPerm` or owner == caller).
   - Hence no two threads access the same non-atomic location concurrently, and there is no data race despite multiple live `&mut KernelK`.
2. **Compiler layer (recorded assumption).** rustc/LLVM do not reorder, cache or dead-store-eliminate ordinary accesses to lock-protected memory across the acquire/release atomics of the lock primitives, because LLVM treats such atomics as clobbers of all non-local memory. This is current toolchain behavior, not a Rust language guarantee: two live `&mut` to one location is UB under the language rules. Cross-ref: §11.3 of the earlier design note.

The `&mut L2EntryLock` path (A.3) adds no new aliasing class beyond item 1. It is the same `&mut` convention that `RwLock::borrow_mut` (rwlock.rs:527) already uses; it reverses the 2026-10-13 `&self` pilot.

### F.2 TCB size
- **Before:** 6 `external_body` in l2_page_map.rs: `load_word_acquire` :116, `store_word_release` :130, `lock` :148, `unlock` :178, `page_perm_to_l2_page_map` :246 (mints `lo..hi` `LockPerm`s and inserts into lctx window maps), `l2_page_map_to_page_perm` :301. `get` and `set_published_locked` are verified.
- **After:** 6 `external_body`, all with entry-local or page-local contracts. Entry TCB (4): `lock`, `unlock` (shape of `RwLock::wlock` rwlock.rs:620), `load_acquire`, `store_release` (one-line contracts, B.1). Page TCB (2): `page_perm_to_l2_page_map`, `l2_page_map_to_page_perm`. `get` and `set_published_locked` stay verified. Optional: +1 `entry_mut` if array `index_mut` fails.
- Weaker: page minting no longer touches lctx or `LockPerm`.
- Smaller: the ghost side maps (`l2_ghost`/`l2_lock`) are gone.
- Same count (6 → 6). Each word primitive's contract now mentions only its own entry (today they take the `L2PageGhost`/`L2LockGhost` tokens and an index).

### F.3 Proof-cost risks
- Range-window loops (range_windows.rs :232 :442 :693 :919): `Map::new` per iteration. Mitigation: invariant `pagetable_window_locks@ == pagetable_window_locks_after_locking_range(old, prefix)` plus an `=~=` step, with an EOL summary if over 5 s.
- Heavy functions (current rlimit): `share_mapping_4k_build_and_share` 20.8M, `ipc_pages_lock_tables_attempt` 14.1M, `ipc_pages_check_tables` 11.5M, `install_one_mmap_4k_directory_page` 10.7M. Mitigation: state window deltas only in wrapper ensures and never inline in the exec equation.
- Deep trigger: `l1_perm(p,i)` sits three levels deep (`l2_perms@[p].value().ar@[i].l1@`). The inline accessor rule plus flat `(p,i)` triggers apply. Watch for monolith order flips (memory: deep-trigger flip, nested-forall pattern).
- `page_closure` term change (`l1_tables.dom` → `l1_rev_map.dom`) ripples into allocator contracts. The value is equal under wf; the risk is trigger mismatch in allocator EOFs.
- `boot` builder (init.rs): a new nested loop moves L1 perms into entries; KVM boot test is required.
- Expected rlimit: −(l2_ghost/l2_lock/l1_tables framing) + (pagetable_window_locks range maps). Net unknown, estimated ±3%.

---

## G. Batches

Verus `--verify-only-module` still needs its whole crate to typecheck. Every kernel_core type change therefore lands in one compile pass (B0) before anyone verifies, and each syscall crate is fixed by one owner. Briefs: `b0_api_freeze.md` … `b4_ni.md` in this scratchpad directory.

| batch | owner files | focused target |
|---|---|---|
| **B0** API + kernel_core compile pass | l2_page_map.rs (final); `PageTableLower` + accessors; `PageTableU.pagetable_window_locks` + 3 helpers + 6 literals; `Share4k.directory`; mechanical signature/field edits in every kernel_core file, with no proof repair | `-- --no-verify` typecheck of `veriflat_kernel_core`, then `pagetable_concurrent::l2_page_map` |
| **B1** pagetable_concurrent (~20) | `src/pagetable_concurrent/*` except l2_page_map.rs; pagetable_seq/pagetable_window_stale_eof.rs, pagetable_seq/pagetable_util_t.rs | `veriflat_kernel_core` `pagetable_concurrent::*`, `pagetable_seq::{pagetable_window_stale_eof,pagetable_util_t}` |
| **B2** kernel_core rest (~20) | memory_management/{pagetable_map_spec,subsystem_mutation_pagetable_map,subsystem_mutation_eof}.rs; locker_unlocker/{pagetable,pagetable_eof,pagetable_window,pagetable_range_windows}.rs; kernel_u_define_spec.rs; kernel_step_spec/kernel_u_steps.rs; kernel_step_wrappers.rs + kernel_step_wrappers/*; init.rs | `veriflat_kernel_core` per module |
| **B3b** map_4k crate (~16) | every touched file in `src/kernel/implementation/map_4k/` | `veriflat_map_4k` |
| **B3a** mmap_4k (~6) | `syscall_mmap_4k/*` | `veriflat_syscall_mmap_4k` |
| **B3c** unmap + iommu_map (~9) | `syscall_unmap_4k/*`, `syscall_iommu_map_4k/*` | 2 crates |
| **B3d** ipc (~8) | `syscall_ipc/*` | `veriflat_syscall_ipc` |
| **B3e** new_process + new_container (~25) | `syscall_new_process/**`, `syscall_new_container/*` | 2 crates |
| **B3f** kill + thread_exit (~14) | `syscall_kill_process/*`, `syscall_kill_container/*`, `syscall_thread_exit/*` | `veriflat_syscall_kill_process`, `veriflat_syscall_thread_exit` |
| **B4** NI (~10) | `noninterference/src/*` | `noninterference/verify-ni.sh` |

Order: B0 → (B1 ∥ B2) → B3b (map_4k is a dependency of the other syscall crates) → (B3a ∥ B3c ∥ B3d ∥ B3e ∥ B3f) → B4 → integration.

Integration (one agent, heavy, at most two jobs at once):
1. `./verify-workspace.sh` (whole).
2. `noninterference/verify-ni.sh`.
3. Monolith `./verify.sh --num-threads 32 --time`, compared with the base rlimit.
4. Boot build + KVM boot run (init.rs and the TCB atomics changed).

Total: 10 batches, about 155 files (the Share4k field and window plumbing widen B3e/B3f beyond the first estimate).

---

## Decision status
- **D1** (user-approved) ghost `pagetable_window_locks: Map<WindowVa, LockStateU>`, copied verbatim to U, plus the two `wf_window_locks` clauses.
- **D2** (self) entry `lock` has no `lock_id_acyclic`; verified `lock_window` keeps it. Alt: acyclic inside the TCB (blocks `create_entry_l3`).
- **D3** (self) L1 domain = `l1_rev_map.dom()`; `page_closure` switches to it. Alt: a ghost `l1_set` field.
- **D4** withdrawn: `set_published_locked` keeps `lctx` and its internal `enter_kernel_view_release` exactly as today.
- **D5** (self) `Tracked<&LockPerm>` threaded through 7 lower primitives + 9 wrappers + 12 sites. Alt: owner == current thread.
- **D6** (user) the mmap Fill enter boundary moves below the existing-window lock; delete the u_eq/rebase at fill_enter.rs:149. No exec change (§D.4b).
- **D7** (user-approved) helper names `pagetable_window_locks_after_locking_range` / `pagetable_window_locks_after_unlocking_range` / `pagetable_window_locks_after_new_l2_page`.
- **D7b** (user) the field is `pagetable_window_locks` in both `PageTableU` and `PageTableLower` (names show they operate on the page table).
- **D8** (user) `Share4k` progress gains `directory: Mmap4kDirectory`; `share_4k_directory_step` is exact (§D.4a).
- **D9** (user) kill-local `kill_process_refund_step` absorbs the optional unlock; the same for thread_exit (`thread_exit_refund_step`) plus the `ThreadExitPagetableWindowsChanged` step/label (§D.4b), both user-approved.
- **D10** (self) `set_published_locked` does not maintain `l1`; verified `borrow_l1_mut` restores `l1_inv`.
- **D11** (self, per span principle; label names user-chosen) `KillProcessWindowLocked` becomes `KillProcessPagetableWindowsChanged`. It is recorded only on the drain path, with the ≤2-change shape, because a per-page loop can unlock window k−1 and lock window k inside one stretch. Alt: always record a lock step (finer than needed).
- **D12** (user) entry `lock` mirrors `wlock_requires`/`wlock_ensures` (rwlock.rs:977-:1000): requires the caller does not hold the entry and is in the Acquire phase; `old.owner() is None` is an ensures; it uses the real `lock_ensures(old, new, lock_id, obj_id)` (local_context.rs:591) and `unlock_ensures(old, new, obj_id, lock_id)` (:613).
