# Kernel objects and their lock ids

## Pagetable 
Container Depth: None
Process Depth: None
Major Id: Page table major id
Minor Id: addr

## Physical pages 
Container Depth: None
Process Depth: None
Major Id: Based on the state of the page
Minor Id: Index

## Endpoint 
Container Depth: None
Process Depth: None
Major Id: Endpoint major id
Minor Id: Index

## Container
Container Depth: self.depth or killing container's depth
Process Depth: High 
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
Major Id: self.state
Minor Id: addr

## CPU
Container Depth: High or killing thread's container depth
Process Depth: High or killing thread's process depth
Major Id: CPU major ID
Minor Id: CPU id