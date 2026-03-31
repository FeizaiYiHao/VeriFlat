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
CPU -> Rlock Container -> Rlock Process -> ... ->  Wlock target Process -> Change Process state to Killing.
CPU -> Rlock Container -> Rlock Process -> ... ->  Wlock target Process -> Wlock Threads -> Change threads states to Killing.

CPU -> Rlock Container -> Rlock Process -> ... ->  Wlock parent Process ->  Wlock target Process -> Wlock blocked/scheduled Threads (state killing) -> Wlock Endpoint/ lock scheduler
CPU -> Rlock Container -> Rlock Process -> ... ->  Wlock parent Process ->  Wlock target Process -> Wlock Running Threads (state killing) -> Wlock CPU


# Supported system calls
## Single step system calls
Create thread
Create process
Create endpoint
Create container
Map
Unmap
Send
Receive
Kill thread

## Multiple step system calls
### Kill single process
Lock the process
sort threads
lock threads
change states to killing (first step)
sort cpu id

lock cpus
unlock cpus (second step)

sort endpoint id
lock endpoints
sort allocator ids
lock allocators

unlock allocators
unlock endpoints 


lock them,
For each level of the threads
### Kill process (plus child processes and all threads)
Lock the top killing process
For each process tree depth level:
    sort process pointer
    lock processes
    gather all threads at the level
    sort threads
    lock threads

lock cpus
lock endpoints

unlock cpu
unlock endpoints (second step)


Kill container (plus child containers and all processes and threads)
Lock all the containers, processes, threads and change thread states to killing. 
Move threads up to the top process of the top container
Kill all the containers
Kill all processes
Kill all threads