# Current syscall semantics

- `mmap_4k` keeps the `quota == range * 4` precheck, uses hierarchical
  range-clean predicates, builds page-table levels, then installs executable 4K
  leaves. Do not restore the deleted legacy mmap path.
- Ordinary IPC supports Empty, Pages, Endpoint, and Cpu for send/receive.
  Pages shares existing 4K data mappings and allocates only missing receiver
  page-table directories. Endpoint transfers an endpoint descriptor reference.
  Call/reply and other non-empty payloads remain out of scope.
- SEND queues contain only SENDING/CALLING; RECEIVE queues contain only
  RECEIVING/RECEIVING_CALL. Same-direction or empty queues block with the exact
  payload. Opposite-direction handling locks the peer first.
- Pages rendezvous validates type, equal length, distinct processes, source and
  target ranges, quota, and ownership before mapping mutation. An alive peer
  is dequeued and scheduled on rendezvous errors, receiving the same error;
  mappings and quota remain unchanged. A killed peer stays queued. Queue
  length and refcount remain one `usize` each.
- Cpu send carries only `Cpu { cpu_id }`; receive accepts any CPU and blocks
  with the unit `ReceiveCpu` marker. Bounds are syscall safety preconditions.
  Ownership and Off state are checked at rendezvous, without reserving the CPU
  when the sender blocks. Same-container transfer is an error.
- Discover both CPU sets and the peer scheduler through container RO data;
  acquire the CPU sets in pointer order, then the peer scheduler, then the
  terminal Off CPU lock. Do not acquire container locks. Move membership and
  the closed slot together, and update the CPU's owning container and depth.
  It stays Off. Off CPUs have no non-default PCID dirty records, and existing
  TLB invariants imply no non-default translations remain.
- Successful Cpu transfer records one kernel step. The sender receives
  `Success`; the receiver receives `SuccessUsize { value: cpu_id }`, through
  the queued thread's `error_code` when it was already blocked. Rendezvous
  errors leave CPU ownership unchanged and record no kernel step.
