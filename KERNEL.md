# Mapping the kernel

This file tracks the port of the CertiKOS kernel itself, module by module. The
lock layers it stands on are covered in [SCOPING.md](SCOPING.md) and
[COMPARISON.md](COMPARISON.md).

The layer names are those of the released mCertiKOS sources (`mcertikos/mm`,
`mcertikos/proc`, `mcertikos/trap`).

## How a kernel module is ported

Each kernel object is a **region** protected by a lock (`LockRegion.lean`):
a block of cells that only the lock's holder reads and writes. A kernel
operation is a critical section on it. Two generic theorems do the lock work
for every module:

- `KernPAlloc.cs_guarantee`: for any critical section `C` with a verified run
  on its region, `acquire(lk); C; release(lk)` finishes on a valid log, and the
  region it releases is related by `C`'s specification to the region the
  previous holder released.
- `KernFrame.cs_guarantee2`: the same when `C` takes and releases a second
  lock inside, as `pt_insert` does when it calls `palloc`. It rests on the
  frame `ext_frame`: code working on one lock leaves our phase on every other
  lock alone, and the region of any other lock we hold.

So porting a module means three things:

1. an abstract specification of each operation, as a function on the region;
2. the C code of the critical section, in ClightL with `rd`/`wr`;
3. a proof that the code computes the specification (a `*_run` lemma).

`KernFrame.lean` makes step 3 short. Inside a critical section the state is
`CSt c i j l b` (we hold lock `i`, are idle on `j`, and region `i` is `b`).
`cst_rd` and `cst_wr` are the rules for a read and a write, and the `Runs`
combinators (`Runs.seq`, `Runs.ite_true`, `Runs.while_true`, …) compose them
along the structure of the code.

The generic theorem then gives the refinement to the atomic operation, under
any environment that keeps the log valid.

## Status

| Module (mCertiKOS layers) | What it is | Status |
|---|---|---|
| **Memory management** | | |
| `MBoot`, `PreInit` | boot, physical memory map | not started |
| `MALInit`, `MALOp`, `MALT` | allocation table, `palloc`/`pfree` | **done**: `KernPAlloc.lean`, with owners in `KernOwner.lean` |
| `MContainer` | per-process memory quotas | **done**: `KernContainer.lean` (alloc, free, split; no getters), page ownership in `KernOwner.lean` |
| `MPTIntro`, `MPTOp`, `MPTCommon` | page-table entries, two-level page tables | **done**: `KernPT.lean` (insert, remove, lookup; no permission bits, tables are never freed) |
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

## What `KernPT.lean` proves

The page table of one address space is a region. Its first `nd` cells are the
page directory. Entry `d` is 0 when no second-level table is present, and
otherwise the address of the table's page. Page `p` has address
`nd + p * ne`, and entry `e` of the table at address `x` is cell `x + e`.

- `ptInsertSpec`: the abstract `pt_insert(d, e, w)`. If the table for `d` is
  present, write the entry. Otherwise take a page from the allocator, zero
  it, install it in the directory, and write the entry. If no page is free,
  change nothing.
- `ptInsertCS`: the C code.
  `pd = PT[d]; if (pd == 0) { r = palloc(); if (r != np) { pd = nd + r * ne; for k < ne: PT[pd + k] = 0; PT[d] = pd; } } if (pd != 0) PT[pd + e] = w;`
- `palloc_nested`: `palloc` called while holding the page table's lock. It
  takes and releases the allocation table's lock. Afterwards we still hold
  the page table's lock and its region is unchanged.
- `ptInsert_guarantee`: `pt_insert` refines `ptInsertSpec`. It finishes idle
  on both locks. The page table it releases is `ptInsertSpec` of the one the
  previous holder released, with the page that `palloc` returned.
- `ptRmv_guarantee`, `ptRead_guarantee`: unmapping clears the entry, and
  lookup returns it and releases the table unchanged.
- `PTInv`: the invariant between a page table and the allocation table. Each
  present directory entry is the address of an allocated page, and no two
  entries share a page.
- `insert_lookup_same`, `insert_lookup_other`, `insert_inv`, `rmv_lookup`:
  under `PTInv` the region behaves as a map. An inserted entry reads back,
  every other entry reads as before, and the invariant holds again with the
  allocation table that `palloc` left.

Not covered: permission bits in entries, freeing a second-level table, and
the kernel's own page table (`MPTKern`). `ptInsert_guarantee` does not say
where in the final log the nested `palloc` happened, only that the page is
`pallocSpec` of some allocation table it found.

## What `KernContainer.lean` proves

The container table is a region. Container `id` is five cells from `id * 5`:
quota, usage, parent, number of children, in use.

- `ctAlloc_guarantee`: `container_alloc(id)` refines `ctAllocSpec`. If the
  container is under quota it calls `palloc` on the allocation table's lock,
  and charges one page if a page came back.
- `ctFree_guarantee`: `container_free(id, j)` refines `ctFreeSpec`. It gives
  one page back and calls `pfree(j)`.
- `ctSplit_guarantee`: `container_split(id, amt)` refines `ctSplitSpec`. If
  the parent has `amt` pages left it sets up the child slot
  `id * mc + 1 + nchildren` with quota `amt` and charges the parent.
- `alloc_inv`, `free_inv`, `split_inv`: `usage ≤ quota` is kept. After a
  split the child has quota `amt`, usage 0, the right parent, and is marked
  in use; the parent's quota is unchanged and its usage grew by `amt`.
- `nest_run`: the general form of the nested call. Any code that works only
  on the lock in `lk`, run on another lock inside a critical section, leaves
  our lock held and our region unchanged.

Not covered: the getters. Page ownership is in `KernOwner.lean`, below.

## What `KernOwner.lean` proves

The allocation table now says who owns each page. A cell is a tag: 0 for a
free page, 1 for a kernel page (the pages of page tables), `id + 2` for a
page of container `id`.

- `pallocO_guarantee`: `palloc(o)` refines `pallocOSpec`. It tags the first
  free page with `o`. `KernPAlloc`'s `palloc` is the case `o = 1`
  (`pallocO_one`).
- `pfreeO_guarantee`: `pfree(o, j)` refines `pfreeOSpec`. It frees page `j`
  only if its tag is `o`, and returns whether it did (`pfreeO_ok`).
- `ctAllocO_guarantee`: `container_alloc(id)` as before, with the page tagged
  `id + 2`.
- `ctFreeO_guarantee`: `container_free(id, j)` calls `pfree(id + 2, j)` and
  lowers the usage only if the page was freed. A container cannot free a
  page it does not own, and its usage does not move if it tries.
- `ostep_other`: a `palloc` or `pfree` by the owner tagged `o'` leaves the set
  of pages tagged `o` exactly as it was, for every other nonzero `o`.
- `PTOwn`, `pt_ostep`, `pt_osteps`: if every page of a page table is tagged 1,
  then `PTInv` and `PTOwn` hold again after any sequence of allocations and
  frees by owners other than the kernel. This is the rely that `PTInv`
  needed.
- `insert_own`: `pt_insert` keeps `PTOwn`.

Not covered: `ostep_other` and `pt_osteps` are about the abstract steps. They
are not yet joined to the shared log, where one would show that every event
on the allocation table's lock is such a step. Usage is not shown equal to
the number of pages a container owns. `pt_insert` still allocates with the
kernel's tag, not the tag of the process whose address space it is.

## What stands in the way of the rest

- **No pointers or structs in ClightL.** Kernel objects are regions of
  32-bit cells indexed by number. That fits tables (allocation table,
  page-table entries, thread control blocks as fixed-size records) but not
  linked structures as CertiKOS writes them.
- **`PTInv` across CPUs.** `KernOwner.pt_osteps` shows the invariant survives
  any allocations and frees by containers, on the abstract allocation table.
  What is left is to show that the events other CPUs put on the allocation
  table's lock are exactly such steps: a kernel-wide invariant on the log.
- **No machine model.** Context switch, traps and virtualization are about
  registers, privilege levels and assembly. None of that exists here, so those
  modules need a machine model first.
- **Per-CPU only.** `cs_guarantee` and `cs_guarantee2` are per-CPU
  guarantees. The multicore results for regions (`RegionLive.lean`,
  `RegionNoLost.lean`) are for one client shape, not for arbitrary kernel
  operations.

## Suggested order

1. Tie ownership to the log: every release of the allocation table's lock
   is an `OStep` of the releasing CPU's current owner, and usage equals the
   number of pages owned.
2. Address spaces (`MPTKern`, `MPTInit`, `MPTNew`) and shared memory
   (`MShare*`): built from `pt_insert` and `pt_rmv`.
3. Thread control blocks and queues (`PThreadIntro` to `PAbQueue`): tables
   again, with queues as index-linked lists inside a region.
4. Scheduler and IPC: these need the thread layer extended with queues and
   liveness.
5. Traps, context switch, virtualization: need a machine model.
