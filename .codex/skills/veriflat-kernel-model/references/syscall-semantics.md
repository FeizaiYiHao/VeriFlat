# Current syscall semantics

- `mmap_4k` keeps the `quota == range * 4` precheck, uses hierarchical
  range-clean predicates, builds page-table levels, then installs executable 4K
  leaves. Do not restore the deleted legacy mmap path.
- Ordinary IPC supports Empty and Pages for send/receive. Pages shares existing
  4K data mappings and allocates only missing receiver page-table directories.
  Call/reply and other non-empty payloads remain out of scope.
- SEND queues contain only SENDING/CALLING; RECEIVE queues contain only
  RECEIVING/RECEIVING_CALL. Same-direction or empty queues block with the exact
  payload. Opposite-direction handling locks the peer first.
- Pages rendezvous validates type, equal length, distinct processes, source and
  target ranges, quota, and ownership before mutation. Errors preserve queue,
  mapping, and quota state. Queue length and refcount remain one `usize` each.
