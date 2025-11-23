# System call lock requiring order. 

## Mmap

CPU -> Rlock Container -> Rlock Process -> Rlock Thread -> Wlock Page table -> Wlock allocator -> Physical pages (Free state)

## Munmap

CPU -> Rlock Container -> Rlock Process -> Rlock Thread -> Wlock Page table -> Physical pages (Mapped state) -> Wlock allocator

## Pass pages through endpoint

CPU -> Rlock Container -> Rlock Process -> Wlock Thread (State Running) -> Wlock Endpoint ->  Wlock Thread (State Blocked) -> Wlock Page table1 -> Wlock Page table2 -> Physical pages (Mapped state)

CPU -> Rlock Container -> Rlock Process -> Wlock Thread (State Running) -> Wlock Endpoint ->  Wlock Thread (State Blocked) -> Lock scheduler

## Pass endpoint through endpoint

CPU -> Rlock Container -> Rlock Process -> Wlock Thread (State Running) -> Wlock Endpoint -> Wlock Endpoint to be passed ->  Wlock Thread (State Blocked)

CPU -> Rlock Container -> Rlock Process -> Wlock Thread (State Running) -> Wlock Endpoint ->  Wlock Thread (State Blocked) -> Lock scheduler

## Schedule 
CPU -> Rlock Container -> Rlock Process -> Wlock Thread (State Running) -> Lock scheduler -> Wlock Thread (State Scheduled)

## Kill Process
CPU -> Rlock Container -> Rlock Process -> ... ->  Wlock target Process -> Wlock Threads -> Change states to Killing.
CPU -> Rlock Container -> Rlock Process -> ... ->  Wlock parent Process ->  Wlock target Process -> Wlock Threads (state killing) -> Wlock Endpoint/ lock scheduler