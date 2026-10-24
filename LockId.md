# Kernel objects and their lock ids

## Pagetable 
Container Depth: None
Process Depth: None
Major Id: Page table major id
Minor Id: addr

## IOMMU root table
Container Depth: NotApp
Process Depth: NotApp
Major Id: IOMMU root table major id (10005)
Minor Id: table base

## IOMMU table
Container Depth: None
Process Depth: None
Major Id: IOMMU table major id (10006)
Minor Id: addr
Its write lock is also the IOTLB dirty marker: while it is held, attached domains may cache hidden leaves; the holder flushes the IOTLB before unlocking.

## Page-table 2M window
Container Depth: None
Process Depth: None
Major Id: Page-table window major id (10007)
Minor Id: (root, L4 index, L3 index, L2 index)

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
Container Depth: owning_container.depth or killing container's depth
Process Depth: owning_process.depth or killing process's depth
Major Id: self.state (Running, Blocked, scheduled)
Minor Id: addr

## CPU
Container Depth: Running or killing thread's container depth or None if idle
Process Depth: Running or killing thread's process depth or None if idle
Major Id: self.state (Running, idle, off)
Minor Id: CPU id