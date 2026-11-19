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

Two kinds of files exist, and they should not be confused.

- **Ported**: follows the mCertiKOS sources (public mirror `npe9/certikos`,
  the sequential PLDI'16 kernel). The abstract state, the specifications and
  the C code are transcribed, and the C code is proved to refine the
  specifications. The sources were read, not run.
- **Prototype**: written before the sources were checked. Verified, but its
  state and specifications are this project's own and differ from
  mCertiKOS's. To be replaced by ports.

The concurrent kernel (mC2) is not public. Where a lock protects an object
here, that part follows the papers, not sources.

Layers are listed bottom-up, as in `mcertikos/mm`, `proc`, `trap`.

| Layer | What it adds | Status |
|---|---|---|
| **Memory management** (`mm`) | | |
| `PreInit` | boot loader, memory map (`get_size`, `get_mms`, `get_mml`, `is_usable`) | missing |
| `MBoot` | allocation-table accessors over memory | **ported** in `MALOp.lean`: `is_norm`, `at_get`, `at_set`, `at_set_c`, `get_nps`. Missing: `set_norm`, `set_nps`, `at_get_c` |
| `MALInit` | `mem_init` | missing |
| `MALOp` | `palloc`, `pfree` | **ported**: `MALOp.lean` (`palloc_refines`, `pfree_refines`) |
| `MALT` | container code: `container_init`, getters, `container_can_consume`, `container_split`, `container_alloc` | **ported** in `MContainer.lean`: the four getters (`getter_guarantee` with `get_*_ref`), `container_split` (`container_split_refines`), `container_alloc` (`container_alloc_refines`). Missing: `container_init`, `container_can_consume` |
| `MContainer` | page-table pool accessors (`set_pt`, `get_PDE`, `set_PDE`, `rmv_PDE`, `set_PDEU`, `get_PTE`, `set_PTE`, `rmv_PTE`, `set_IDPTE`) | **in progress**: `MPTIntro.lean` has the state, the eight specs (`getPDE_spec` … `setIDPTE_spec`) and the relation to memory (`MatchPT`). The C code and its proofs are next. `setPT'_spec` not yet |
| `MPTIntro` | `pt_read`, `pt_read_pde`, `pt_rmv_aux`, `pt_rmv_pde`, `pt_insert_aux`, `pt_insert_pde`, `idpde_init` | prototype only |
| `MPTOp` | `pt_alloc_pde`, `pt_free_pde`, kernel mappings | missing |
| `MPTCommon` | `pt_insert`, `pt_rmv` with reference counts | prototype only |
| `MPTKern`, `MPTInit` | kernel page table, `pt_init`, paging on | missing |
| `MPTNew` | `pt_new`, `pt_resv`, `pmap_init` | missing |
| `MShareIntro`, `MShareOp`, `MShare` | shared memory | missing |
| abstract ownership | `pperm`, the logical table `LAT` with its owner lists, `consistent_ppage` | `pperm` and `consistent_ppage` are in `MALOp.lean` and proved preserved. `LAT` missing. `KernOwner.lean` is a prototype with a different design |
| **Process management** (`proc`) | | |
| `PKContext`, `PKContextNew` | kernel contexts, `kctxt_switch`, `kctxt_new` | missing (needs assembly and a machine model) |
| `PThreadIntro`, `PThreadInit` | thread control blocks | missing |
| `PQueueIntro`, `PQueueInit`, `PAbQueue` | thread queues, then abstract queues | missing |
| `PCurID`, `PThreadSched`, `PThread` | current thread, `thread_spawn`, `thread_yield`, `thread_sleep`, `thread_wakeup` | missing (`ThreadLayer.lean` is a prototype of a different thing) |
| `PIPCIntro`, `PIPC` | synchronous IPC | missing |
| `PUCtxtIntro`, `PProc` | user contexts, `proc_create` | missing |
| **Trap handling** (`trap`) | | |
| `TTrapArg`, `TTrap`, `TDispatch`, `TSysCall` | system-call arguments, handlers, dispatch | missing |
| **Other** | | |
| `objects/ObjVMX`, `ObjVMCS`, `ObjEPT` | virtualization | missing |
| `security` | noninterference (`Integrity`, `Confidentiality`, `Security`) | missing |
| `layerlib`: `LAsm`, `CompCertiKOS` | layered assembly, the compiler | missing: no machine model, no verified compiler |
| layer calculus | linking layers vertically with `high_level_invariant` | partial: each port states refinement to the spec; invariant preservation and layer linking are not done per layer |

### What a port still leaves out

Even for the ported layers:

- `ikern` and `ihost` are dropped from the specifications (no machine model).
- Indices are `Nat` rather than `Z`.
- The objects live in lock regions, not in CompCert memory.
- `high_level_invariant`: the parts about the allocation table and the
  containers are proved preserved by the specifications
  (`MContainerInv.lean`). They are not yet carried along the shared log.
- Boot (`mem_init`, `container_init`) is not ported, so nothing establishes
  the invariant initially.

## How the ports are organised

- **Agreed order** (2026-11-19): 0 calling convention for layers, 1 page
  tables, 2 boot and init, 3 shared memory, 4 invariants along the shared
  log, 5 thread data, 6 machine model and scheduler, 7 IPC, 8 processes and
  traps, 9 security and virtualization. Stage 0 is done. Stage 1 has started.
- **`Layer.lean`: a primitive's interface is a triple.**
  `Triple εR c i M F P s Q` says: in a critical section, on a region matching
  abstract data `d` with precondition `P`, the code `s` runs to completion,
  writes only cells in the footprint `F`, and leaves a region matching a `d'`
  with `Q`. A layer's code is verified against the triples of the layer
  below, never against its code. `container_alloc` calls `palloc` this way
  (`palloc_triple`).
- **`Triple.lift`** is the frame rule. When a layer adds state, the triples
  below keep working, provided what was added survives writes inside their
  footprints.
- **`Triple.locked`** turns a triple into a statement about
  `acquire; s; release`: acquiring always succeeds, and if the region found
  matches `d` with `P`, the call finishes and releases a region matching
  `d'` with `Q`.
- **One memory-management region, one lock.** The allocation table, the
  container table, and next the page-table pool, the identity map and flat
  memory, are all in one region (`MatchMM`, `MatchPT`). A primitive is one
  critical section and the sequential specifications apply as they are.
  mC2 uses finer locks. Its sources are not public, so that is not ported.
  It is the subject of stage 4.

## What the ported files prove

Each port has the same shape, which is mCertiKOS's own two steps.

1. The C code computes a function on the region, for any region
   (`pallocC`, `pfreeC`, `ctAllocC`, `ctSplitC`).
2. That function refines the abstract specification whenever the region
   matches abstract data (`palloc_ref`, `pfree_ref`, `alloc_ref`,
   `split_ref`).

### `MALOp.lean`

- State: `ATInfo` (`ATValid allocated type count`), `PPgInfo`, `PData`.
- Relation: `MatchD`, mCertiKOS's `match_AT`. Entry `i` is the three words
  at `3 * i`: type, allocated, count.
- `palloc_refines`: `palloc()` refines `palloc'_spec`. It scans from page 1
  for the first unallocated normal page, sets its allocated bit and clears
  its count, and returns it, or returns 0. The proof uses `ATInv` (every
  entry below `nps` is defined, `nps ≤ maxpage`).
- `pfree_refines`: `pfree(j)` refines `pfree'_spec`. The code is
  `at_set(j, 0)`. That the page was allocated, normal, unmapped and had
  permission `PGAlloc` is a precondition of the specification.

### `MContainer.lean`

- State: `Container` (quota, usage, parent, children, used), `RData`.
- Relation: `MatchC`, mCertiKOS's `match_container`. An unused container
  matches any words whose "used" word is 0.
- `getter_guarantee`, `get_quota_ref`, `get_usage_ref`, `get_parent_ref`,
  `get_nchildren_ref`: the four getters.
- `container_alloc_triple`, `container_alloc_refines`: `container_alloc(id)`
  refines `container_alloc_spec`, in one critical section, calling `palloc`
  through its specification. The code tests `usage == quota` where the
  specification tests `usage < quota`, so the proof needs `usage ≤ quota`
  (`cvalid_usage`).
- `container_split_refines`: `container_split(id, q)` refines
  `container_split_spec`. The code makes no checks. The specification's
  conditions are what make the writes land on the right cells.

### `MContainerInv.lean` and the end of `MALOp.lean`: the invariants

mCertiKOS shows that every primitive of a layer preserves
`high_level_invariant`. The parts about these two layers are ported and
proved, on the specifications.

| Invariant (mCertiKOS name) | Preserved by |
|---|---|
| `valid_nps`, `AT_kern`, `AT_usr`, `consistent_ppage` (here `ATInv`) | `palloc'_spec` (`palloc_inv`), `pfree'_spec` (`pfree_inv`), `container_alloc_spec` (`alloc_at_inv`) |
| `Container_valid`, all thirteen fields | `container_alloc_spec` (`alloc_valid`), `container_split_spec` (`split_valid`) |
| `quota_bounded_AT` | `container_alloc_spec` (`alloc_quota_bounded`), `container_split_spec` (`split_quota_bounded`) |

- `alloc_defined`: under `Container_valid` and `quota_bounded_AT`,
  `container_alloc_spec` is defined. A container below its quota always finds
  a free page (mCertiKOS's `quota_bounded_AT_first_free`). So the case where
  the specification is undefined cannot happen.
- `split_valid` derives that the child slot is free from the invariant: a
  used container at that index would have to be in its parent's child list,
  and the list's index range excludes it.

Not done in the ports:

- The invariants are preserved by the specifications. They are not yet
  carried along the shared log. The `*_refines` theorems still take them as
  hypotheses.
- `palloc'_spec` and `pfree'_spec` alone do not preserve `quota_bounded_AT`.
  In mCertiKOS they are not exported above the container layer.
- Boot is not ported, so nothing establishes the invariants initially.
- The getters and the setters of `MBoot` (`set_at_u_spec` and the like) have
  no invariant lemmas. The setters do not preserve the invariant one at a
  time.

# Prototype files

The sections below describe the files written before the sources were
checked. They are verified, but they are not mCertiKOS's specifications.

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

**This file is not a port of an mCertiKOS layer.** It is this prototype's own
design. Checked against the public sources (`npe9/certikos`:
`objects/ObjPMM.v`, `objects/ObjContainer.v`, `layerlib/AuxStateDataType.v`,
`mm/MALOpCSource.v`):

| | mCertiKOS | here |
|---|---|---|
| allocation-table entry | `ATValid allocated type refcount`, no owner | an owner tag |
| `pfree(i)` | `at_set(i, 0)`, no check; the spec has a precondition (allocated, `PGAlloc`) | checks the tag at run time |
| who uses a page | abstract state only: `pperm` (`PGUndef`, `PGAlloc`, `PGHide owner`) and the logical table's list of page-table entries mapping it (`LATOwner`) | the tag, in the table itself |
| `container_free` | none (its spec is commented out, and only lowered the usage) | frees and lowers usage if the tag matches |
| `palloc` failure | returns 0; pages scanned from 1, only `ATNorm` ones | returns `np`; scans from 0, no page types |
| `container_alloc` with no free page | undefined (`None`): the quota invariant rules it out | returns `np`, usage unchanged |
| `container_split` | conditions are preconditions of the spec | quota checked at run time |

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
