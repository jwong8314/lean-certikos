# Mapping the kernel

This file tracks the port of the CertiKOS kernel itself, module by module. The
lock layers it stands on are covered in [SCOPING.md](SCOPING.md) and
[COMPARISON.md](COMPARISON.md).

The layer names are those of the released mCertiKOS sources (`mcertikos/mm`,
`mcertikos/proc`, `mcertikos/trap`).

## How a kernel module is ported

Each kernel object is a **region** protected by a lock (`LockRegion.lean`):
a block of cells that only the lock's holder reads and writes. A kernel
operation is a critical section on it. One generic theorem does the lock work
for every module:

- `KernPAlloc.cs_guarantee`: for any critical section `C` with a verified run
  on its region, `acquire(lk); C; release(lk)` finishes on a valid log, and the
  region it releases is related by `C`'s specification to the region the
  previous holder released.

So porting a module means three things:

1. an abstract specification of each operation, as a function on the region;
2. the C code of the critical section, in ClightL with `rd`/`wr`;
3. a proof that the code computes the specification (a `*_run` lemma).

`cs_guarantee` then gives the refinement to the atomic operation, under any
environment that keeps the log valid.

## Status

| Module (mCertiKOS layers) | What it is | Status |
|---|---|---|
| **Memory management** | | |
| `MBoot`, `PreInit` | boot, physical memory map | not started |
| `MALInit`, `MALOp`, `MALT` | allocation table, `palloc`/`pfree` | **done**: `KernPAlloc.lean` |
| `MContainer` | per-process memory quotas | not started |
| `MPTIntro`, `MPTOp`, `MPTCommon` | page-table entries, two-level page tables | not started |
| `MPTKern`, `MPTInit`, `MPTNew` | kernel page table, address-space creation | not started |
| `MShareIntro`, `MShareOp`, `MShare` | shared memory between processes | not started |
| **Process management** | | |
| `PKContext`, `PKContextNew` | kernel contexts, context switch | not started |
| `PThreadIntro`, `PThreadInit` | thread control blocks | not started |
| `PQueueIntro`, `PQueueInit`, `PAbQueue` | thread queues | not started |
| `PCurID`, `PThreadSched`, `PThread` | current thread, scheduler, `yield`/`sleep`/`wakeup` | minimal: `ThreadLayer.lean` (threads as virtual CPUs, safety only) |
| `PIPCIntro`, `PIPC` | synchronous IPC | not started |
| `PUCtxtIntro`, `PProc` | user contexts, process creation | not started |
| **Trap handling** | | |
| `TTrapArg`, `TTrap`, `TDispatch`, `TSysCall` | system-call arguments, handlers, dispatch | not started |
| **Other** | | |
| virtualization (`VMX`, `VMCS`, `EPT`) | guest VMs | not started |
| device drivers, interrupts | | not started |
| security (noninterference) | process isolation | not started |

## What `KernPAlloc.lean` proves

- `pallocSpec np b`: the abstract allocator on a table of `np` pages. It marks
  the first free page and returns it, or returns `np` when none is free.
- `palloc_fresh`: the returned page was free, is now allocated, and no other
  entry changed.
- `scan_run`: the C scan loop
  `while (i != np) { x = AT[i]; if (x == 0) { AT[i] = 1; r = i; i = np; } else i++; }`
  computes `pallocSpec`.
- `palloc_guarantee`: `palloc()` (acquire, scan, release) refines
  `pallocSpec`: the page it returns and the table it releases are
  `pallocSpec` of the table the previous holder released.
- `pfree_guarantee`: `pfree(j)` clears entry `j` and nothing else.

## What stands in the way of the rest

- **No pointers or structs in ClightL.** Kernel objects are regions of
  32-bit cells indexed by number. That fits tables (allocation table,
  page-table entries, thread control blocks as fixed-size records) but not
  linked structures as CertiKOS writes them.
- **One region per lock.** Operations that touch two objects (for example a
  page-table update that also allocates a page) need two locks held in a fixed
  order. The protocol allows it, but no theorem covers it yet.
- **No machine model.** Context switch, traps and virtualization are about
  registers, privilege levels and assembly. None of that exists here, so those
  modules need a machine model first.
- **Per-CPU only.** `cs_guarantee` is a per-CPU guarantee. The multicore
  results for regions (`RegionLive.lean`, `RegionNoLost.lean`) are for one
  client shape, not for arbitrary kernel operations.

## Suggested order

1. `MContainer` (quotas): another table, same pattern as `palloc`.
2. Page tables (`MPTIntro` to `MPTNew`): a two-level table as a region, with
   map/unmap as critical sections. This needs the two-lock theorem, since
   mapping allocates.
3. Thread control blocks and queues (`PThreadIntro` to `PAbQueue`): tables
   again, with queues as index-linked lists inside a region.
4. Scheduler and IPC: these need the thread layer extended with queues and
   liveness.
5. Traps, context switch, virtualization: need a machine model.
