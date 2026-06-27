# VeriFlat — spec/proof history (NOT auto-loaded)

Read-on-demand record of *why* the spec looks the way it does — bugs found and
fixed, design decisions reversed. This file lives outside `.kiro/steering/` on
purpose so it is **not** loaded into every session; consult it when you need the
rationale behind a clause ("why is the cpu binding there?"), not for day-to-day
rules. Rules and current state live in `.kiro/steering/`.

## container_allocator_free_{4k,2m,1g}_page_wf — three spec bugs (2026-06)

These three bidirectional predicates (in `container_allocator_pages_spec.rs`)
tie a page's `Free{4k,2m,1g}` state to its location: `GlobalList` ⟺ in the
allocator's `global_poll`, `PreCpuCache{cpu_id}` ⟺ in `cpu_caches[cpu_id]`.
They were **defined but never wired into `memory_management_inv()`** until this
work — without them, popping a page from a cache couldn't establish the page's
prior `Free4k` state, blocking the `Owned4k` transition in
`allocate_free_4k_page`. Now conjuncts of `memory_management_inv()`. Wiring them
in surfaced three real spec bugs (all found *after* the crate verified green —
a wrong/weak invariant conjunct still verifies, it's just weaker than intended).

**Bug 1 — vacuous antecedent.** The cache-reverse clause read
`global_poll.contains(page_ptr) && cpu_caches[cpu_i].contains(page_ptr) ==> …`.
A page is in exactly one place (pool XOR a cache, never both), so the `&&` made
the clause **vacuous**. Fixed to cache-membership-only, with the
`allocator_map.dom().contains(alloc_ptr) && cpu_id_valid(cpu_i)` well-formedness
guards before `==>` (mirroring the global-poll-reverse sibling). All 3 granules.
Each predicate also got `recommends container_page_owner_wf + page_array_wf`
(can't name `container_allocator_wf` — needs the other two allocator maps).

**Bug 2 — key/value swap.** The `map()` lookup in all six membership clauses
(4k/2m/1g × pool/cache) read
`global_poll.view().map().spec_index(page_index2page_ptr(page_index)) ==
free_list_node_storage.addr()` — indexing the node-address-keyed `map()` by a
*page pointer* and comparing to a *node address*. Both sides swapped.
`LinkedList.map()` is keyed by **node address → PagePtr value** (`wf_map`;
`pop_head` gives `ret.1@.value()@ == map()[ret.0]`, `ret.0` = node addr).
Corrected to `.map().spec_index(free_list_node_storage.addr()) ==
page_index2page_ptr(page_index)`. Consequence: `pop_head` returns
`(node_addr, node_perm)`; the **page pointer is `node_perm@.value()@`**, read in
exec via `PPtr::<Node<PagePtr>>::from_usize(node_addr).borrow(..).value` — NOT
`ret.0`. (The original fast-path stub `let (page_ptr,_) = pop_head()` returned
the node address.)

**Bug 3 — unconstrained cpu binder.** The cache-reverse clause's
`matches PreCpuCache { cpu_id }` left `cpu_id` a fresh binder, never tied to the
cache index `cpu_i` — so a page in `cache[5]` could record `PreCpuCache{3}` and,
via the forward clause, sit in two caches at once. The intended invariant is a
bijection (page in `cache[C]` ⟺ state `PreCpuCache{C}`). Fixed by adding a
separate conjunct `state->Free4k_state->PreCpuCache_cpu_id == cpu_i` (the
`matches` binder is now `_cpu_id`). NOTE: a `matches` pattern only *binds* a
fresh var — `matches PreCpuCache { cpu_id: cpu_i }` does NOT test equality
against the outer `cpu_i` (it shadows it), and a `matches` binding doesn't even
scope across `&&`; the field ACCESSOR is the right tool. (The reusable form of
this gotcha is in `veriflat-project-notes.md` § Page state with ghost payload.)

## LockOwnerId order redesign + more allocate spec fixes (2026-06)

While proving `allocate_free_4k_page`'s page-state transition, several more
issues surfaced:

**Bug 4 — `None` should be the MAX owner-id.** `LockId.spec_gt` compares
`container` (a `LockOwnerId`) first. A Free page has `container = None`; a held
process has `container = Some(depth)` (via `ProcessRO`). The original order had
`Some > None`, so a `None`-owner page could NOT be lock-ordered after a process
— blocking the page lock. Fixed `LockOwnerId::spec_gt`/`spec_lt` so `None` is
the maximum. Reasoning (user): once a `None`-owner object (Free page, pagetable)
is locked, nothing with a concrete owner is acquired afterward, so `None` sorts
above every `Some`.

**Bug 5 — `High` should be the MIN owner-id.** Symmetric: an `Owned` page is
intended to carry `container = High` so it can never be locked while any
`Some`-owner is held (the protocol always locks CPU/process first) — i.e. owned
pages are effectively private. Final order, high→low: `None > Some(big) >
Some(small) > High`; `NotApp` is a wildcard. `High` was unused, so both
comparator changes had zero blast radius on existing proofs.

**`matches`-binds-not-tests gotcha (during bug 3's fix).** `matches PreCpuCache
{ cpu_id: cpu_i }` does NOT test equality against the outer `cpu_i` — it binds a
fresh `cpu_i`, shadowing it, and the binding doesn't even scope across `&&`. The
real cpu-binding constraint is a separate conjunct using the field accessor
`state->Free4k_state->PreCpuCache_cpu_id == cpu_i`. (Now in
`veriflat-project-notes.md` § Page state with ghost payload.)

**Bug 6 — missing `map.dom().contains(storage.addr())` conjunct.** The six
forward clauses asserted `cache.map()[storage.addr()] == page_ptr` without
guaranteeing the key is live (Map index is junk off-domain). Added the dom
conjunct to all six; needed so `lemma_value_addr_unique` (map injectivity) has
both addresses in-domain.

**Bug 7 — `LockedArray::wunlock` contradictory ensures.** It asserted BOTH
`kernel_view_locking_state() == old` AND `unlock_ensures` (which forces
Acquire→Release) — jointly `false` in an Acquire section. Deleted the `== old`
line (matches `LockedMap::wunlock`). `unlock_ensures` is the source of truth:
within a kernel section you Acquire (lock phase) then transition to Release at
the first unlock and never re-lock; `kernel_step_boundary` flips back to Acquire
for the next step.

**Bug 8 — temp-alloc caches not finite.** `Process.temp_alloc_cache_{4k,2m,1g}`
had no `finite()` invariant, but `.len()` feeds `process_effective_quota_*` and
the conservation law, and `Set::insert` grows length by 1 only for finite sets.
Added `.finite()` for all three to `process_tree_fields_wf` (beside the existing
`subtree_set.finite()`). Zero blast radius on existing producers.

New reusable LinkedList lemmas (in `spec_impl.rs`): `lemma_value_addr_unique`
(map injectivity via `no_duplicates` on values), `lemma_map_dom` (expose
`map().dom() == perms.dom()` past closed `wf`). `pop_head` ensures strengthened
with `old.dom().contains(ret.0)` + `ret.0 == addr_list[0]`.
