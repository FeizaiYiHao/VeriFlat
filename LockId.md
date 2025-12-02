# Kernel objects and their lock ids

## Pagetable 
Container Depth: None
Process Depth: None
Major Id: Page table major id
Minor Id: addr

## Physical pages 
Container Depth: None
Process Depth: None
Major Id: Based on the state of the page (Free, merged, allocated, mapped)
Minor Id: Index

## Endpoint 
Container Depth: None
Process Depth: None
Major Id: Endpoint major id
Minor Id: Index

## Container
Container Depth: self.depth or killing container's depth
Process Depth: NA 
Major Id: Container major id
Minor Id: addr

## Process
Container Depth: owning_container.depth or killing container's depth
Process Depth: self.depth or killing process's depth
Major Id: Process major id
Minor Id: addr

## Thread
Container Depth: None or killing container's depth
Process Depth: None or killing process's depth
Major Id: self.state (Running, Blocked, scheduled)
Minor Id: addr

## CPU
Container Depth: Running or killing thread's container depth or None if idle
Process Depth: Running or killing thread's process depth or None if idle
Major Id: self.state (Running, idle, off)
Minor Id: CPU id