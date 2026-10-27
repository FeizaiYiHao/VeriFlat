# Kernel objects and their lock ids

`LockId { container, process, major, minor }` (`src/define/lock_id.rs`).
Equality is structural. Order is lexicographic over the four fields: owner
components first, then the major, then the minor (lexicographic, a strict
prefix first). `LockOwnerId` is `High | Some(depth) | None`, ordered
`High < Some(small) < … < Some(big) < None`; there is no wildcard.

- `High`: a killer-marked object (`(High, High, KILLED_LOCK_MAJOR = 0, minor)`),
  or the owner a killer requests when marking a deeper container.
- `Some(depth)`: a concrete container or process depth.
- `None`: the object intentionally has no owner component and sorts after
  every owned object of the same prefix. It is not a fallback.

Each component comes from an `OwnerSource` of the lock's read-only data:
`Payload` (the payload's own owner, the default for `ROT = ()`), `Fixed(owner)`
(read-only data's fixed owner), or `Dynamic` (the concrete owner recorded by
the current dynamic write acquisition, `None` otherwise). `Dynamic` is an
acquisition policy, never an owner value. A marked object reports `High` for
both components regardless of source.

## Dynamic container lock
Only the container's process component is `Dynamic`. A write acquisition
requests a concrete owner `r`; under the lock guard: a kill record wins
(`Killed`); a live holder with recorded owner `h < r` returns `DepthConflict`
at once; a holder with `h >= r` is waited for and rechecked; a free lock is
acquired and records `LockControl::DynamicProcess(r)`; unlock clears it.
Ordinary container-locking syscalls request the caller's current process
depth and stutter with `ErrorContainerLockOrderConflict` (ABI index 49) on a
conflict. Marking a deeper container requests `High`. A newly created child
container is published write-held with `Some(0)`. `ContainerU` projects the
recorded owner as `lock_process_owner`.

## Owners by object
| Object | Container | Process | Major | Minor |
|---|---|---|---|---|
| Container | `Some(self.depth)` | dynamic owner, else `None` | 101 | addr |
| CPU offline request cell | `Some(container depth)` | `None` | 104 | family minor |
| Process | `Some(container depth)` | `Some(self.depth)` | 105 | addr |
| PCID allocator | `Some(container depth)` | `None` | 107 | family minor |
| Thread, RUNNING | `Some(container depth)` | `Some(process depth)` | by state | addr |
| Thread, unmarked KILLED | `Some(container depth)` | `None` | by state | addr |
| Thread, other states | `None` | `None` | by state | addr |
| CPU, Running/Idle | `Some(container depth)` | `Some(process depth)` if it has a current process, else `None` | 1 / 2 | cpu id |
| CPU, Off | `None` | `None` | 30002 | cpu id |
| Page table, page-table window, IOMMU table, IOMMU root table | `None` | `None` | 10004 / 10007 / 10006 / 10005 | addr; window: (root, L4, L3, L2 index); root table: table base |
| Endpoint, physical page, CPU set, scheduler shard, PCID needflush, allocator quota/cache/pool | `None` | `None` | family major | family minor |

Any of these objects that a killer has marked reports
`(High, High, KILLED_LOCK_MAJOR, minor)` instead.

The IOMMU table write lock is also the IOTLB dirty marker: while it is held,
attached domains may cache hidden leaves; the holder flushes the IOTLB before
unlocking.
