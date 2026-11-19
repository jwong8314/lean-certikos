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
- **Prototype**: written before the sources were checked. The memory-management
  prototypes have been replaced by ports and removed (see "Retired
  prototypes").

The concurrent kernel (mC2) is not public. Where a lock protects an object
here, that part follows the papers, not sources.

Layers are listed bottom-up, as in `mcertikos/mm`, `proc`, `trap`.

| Layer | What it adds | Status |
|---|---|---|
| **Memory management** (`mm`) | | |
| `PreInit` | boot loader, memory map (`get_size`, `get_mms`, `get_mml`, `is_usable`) | **accessors ported** in `MALInitC.lean` as reads of the memory map in the region (`MatchMMap`). `boot_loader` itself is not code here (it is not verified in mCertiKOS either): its effect is the precondition `MatchMMap` |
| `MBoot` | allocation-table accessors over memory | **ported** in `MALOp.lean`: `is_norm`, `at_get`, `at_set`, `at_set_c`, `get_nps`. `set_norm`, `set_nps` in `MALInitC.lean`. Missing: `at_get_c` |
| `MALInit` | `mem_init` | **specification ported**: `MALInit.lean` (`mem_init_spec`, `real_nps`, `real_AT`). `mem_init_inv`: it establishes the allocation-table invariant. **C code ported**: `MALInitC.lean`, `mem_init_triple` (the three loops refine `mem_init_spec`) |
| `MALOp` | `palloc`, `pfree` | **ported**: `MALOp.lean` (`palloc_refines`, `pfree_refines`) |
| `MALT` | container code: `container_init`, getters, `container_can_consume`, `container_split`, `container_alloc` | **ported** in `MContainer.lean`: the four getters (`getter_guarantee` with `get_*_ref`), `container_split` (`container_split_refines`), `container_alloc` (`container_alloc_refines`). `container_init_spec` ported in `MContainerInit.lean`, with `container_init_inv`: it establishes all three invariants. **C code of `container_init` ported**: `MContainerInitC.lean`, `container_init_triple`. Missing: `container_can_consume` |
| `MContainer` | page-table pool accessors (`set_pt`, `get_PDE`, `set_PDE`, `rmv_PDE`, `set_PDEU`, `get_PTE`, `set_PTE`, `rmv_PTE`, `set_IDPTE`) | **ported**: `MPTIntro.lean`. All eight memory accessors refine their specs (`getPDE_triple`, `setPDE_triple`, `rmvPDE_triple`, `setPDEU_triple`, `getPTE_triple`, `setPTE_triple`, `rmvPTE_triple`, `setIDPTE_triple`). Missing: `set_pt` (loads `CR3`; needs the machine model) |
| `MPTIntro` | `pt_read`, `pt_read_pde`, `pt_rmv_aux`, `pt_rmv_pde`, `pt_insert_aux`, `pt_insert_pde`, `idpde_init` | **ported**: `MPTOp.lean`. The six operations refine `ptRead_spec` … `ptInsertPDE_spec`, each verified against the accessor's triple. `idpde_init` is in `MPTInit.lean` (`idpde_init_triple`) |
| `MPTOp` | `pt_alloc_pde`, `pt_free_pde`, `pt_init_comm` | **ported**: `MPTCommon.lean`. `pt_alloc_pde` refines `ptAllocPDE_spec` (through the specs of `container_alloc`, `pt_insert_pde`, and 1024 calls of `rmv_PTE`); `pt_free_pde` refines `ptFreePDE_spec` (through `pt_read_pde`, `pt_rmv_pde`, `pfree`). `pt_init_comm` is in `MPTInit.lean` (`pt_init_comm_triple`) |
| `MPTCommon` | `pt_insert`, `pt_rmv` with reference counts, `pt_init_kern` | **ported**: `MPTKern.lean`. `pt_insert` refines `ptInsert_spec` (`ptInsert_triple`) and `pt_rmv` refines `ptRmv_spec` (`ptRmv_triple`), both keeping the page's count in the allocation table. `pt_init_kern` is in `MPTInit.lean` (`pt_init_kern_triple`) |
| `MPTKern`, `MPTInit` | kernel page table, `pt_init`, paging on (`set_pg`, `set_cr3`) | missing: these are boot, and loading `CR3` needs the machine model |
| `MPTNew` | `pt_new`, `pt_resv`, `pt_resv2`, `pmap_init` | **ported**: `MPTNew.lean`. `pt_new` refines `pt_new_spec`; `pt_resv` refines `ptResv_spec` (stated over `container_alloc_spec` and `ptInsert_spec`); `ptResv_locked` is `pt_resv` under the lock. `pt_resv2` is in `MPTResv2.lean` (`ptResv2_triple`). Missing: `pmap_init` (machine model) |
| `MShareIntro` | the shared-memory table and its seven accessors | **ported**: `MShareIntro.lean`. Each accessor refines its spec (`getState_triple`, `getSeen_triple`, `getLoc_triple`, `setState_triple`, `setSeen_triple`, `setLoc_triple`, `clear_triple`) |
| `MShareOp` | `shared_mem_to_pending`, `shared_mem_to_dead`, `shared_mem_to_ready`, `get_shared_mem_status_seen`, `shared_mem_init` | **ported**: `MShareOp.lean` (`toPending_triple`, `toDead_triple`, `toReady_triple`, `statusSeen_triple`). `shared_mem_init`: its loop is verified (`smInit_triple` in `MShare.lean`); its call to `pmap_init` waits for the machine model |
| `MShare` | `shared_mem_status`, `offer_shared_mem` | **ported**: `MShare.lean` (`status_triple`, `offer_triple`) |
| abstract ownership (`PTInitGen`) | the logical table `LAT` with its owner lists, `consistent_pmap`, `consistent_pmap_domain`; `alloc_spec`, `ptInsert0_spec`, `ptRmv0_spec`, `ptResv_spec` over owner lists | **ported**: `PTInitGen.lean`. The count-based specs refine the owner-list ones: `alloc_exist`, `ptInsertPTE_exist`, `ptAllocPDE_exist`, `ptInsert_exist`, `ptRmv_exist`, `ptResv_exist`. Missing: `ptFreePDE0_spec`, and that the owner-list specs preserve the upper invariant |
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
- Boot: `mem_init`, `container_init`, `idpde_init`, `pt_init_comm` and
  `pt_init_kern` are ported with their C code. `pt_init` and `pmap_init` are
  not: they need the machine model.

## How the ports are organised

- **Agreed order** (2026-11-19): 0 calling convention for layers, 1 page
  tables, 2 boot and init, 3 shared memory, 4 invariants along the shared
  log, 5 thread data, 6 machine model and scheduler, 7 IPC, 8 processes and
  traps, 9 security and virtualization. Stages 0 to 3 are done, except for what needs `CR3` (`pt_init`, `pmap_init`, and so the first line of `shared_mem_init`).
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

### `MPTIntro.lean`

- State: `PTPerm`, `PTEInfo`, `PDE`, `PTData` (the page-table pool, the
  identity map, the current page table, the paging flags, visible flat
  memory).
- Relation: `MatchPT` (`match_PDE`, `match_IDPDE`, `relate_PMapPool`). A
  present directory entry holds `pi * 4096 + 7` and the permission table says
  page `pi` is hidden and owned by that entry. Its second-level table is the
  1024 words of page `pi` in flat memory.
- `Layout`: where the five tables sit in the one region.
- `pool_update`, `pte_update`, `idp_update`: replacing a directory entry, a
  second-level entry or an identity-map entry keeps the relation. Two present
  directory entries never share a page (`pde_unique`), because the permission
  table names the one owner.
- The eight triples, one per accessor. Each is the interface the next layer
  is verified against.

### `MPTOp.lean` and `MPTCommon.lean`

- `MPTOp.lean`: the six operations by virtual address. Each is one accessor
  after computing `PDX` and `PTX`, so each proof is the accessor's triple and
  `Triple.assign_pre`.
- `MPTCommon.lean`: the first primitives that span the whole memory manager.
  - `pfree_lift`, `container_alloc_lift`: `pfree` and `container_alloc` were
    verified on the allocation table and containers alone. `Triple.lift`
    carries them to the state with page tables. What has to be shown is that
    they leave hidden pages' permissions alone (`pfree_pperm`, `alloc_pperm`;
    the second uses `consistent_ppage`).
  - `ptFreePDE_triple`: `pt_free_pde` refines `ptFreePDE_spec`.
  - `ptAllocPDE_triple`: `pt_alloc_pde` refines `ptAllocPDE_spec`. The loop
    that clears the new table is verified against `rmv_PTE`'s specification,
    1024 times (`rmvLoop_run`), and ends with `real_init_PTE`.

### `MPTKern.lean`

- `ptInsert_triple`: `pt_insert(n, vadr, padr, perm)` refines `ptInsert_spec`.
  It covers the three outcomes: the second-level table was there (returns 0);
  it was allocated (returns its page); none could be allocated (returns
  `MagicNumber`, nothing mapped). The proof goes through the specifications
  of `pt_read_pde`, `pt_alloc_pde`, `pt_insert_aux`, `at_get_c` and
  `at_set_c`.
- `ptRmv_triple`: `pt_rmv(n, vadr)` refines `ptRmv_spec`: it clears the entry,
  lowers the page's count, and returns the page, or returns 0 if nothing was
  mapped.
- `atGetC_lift`, `atSetC_lift`: the count accessors carried to the state with
  page tables.

### `PTInitGen.lean`: who owns a page

Below this step the allocation table counts the mappings of each page. Above
it, mCertiKOS's state lists them: `LAT` holds, for each page, the entries
`LATO n pdi pti` that map it. This is mCertiKOS's page ownership. The step
has no C code: it is a simulation between two abstract states.

- `Relate h d`: the states agree, and each count is the length of the owner
  list.
- `ptInsert_exist`, `ptRmv_exist`, `ptResv_exist`, `alloc_exist`: if the
  specification over owner lists is defined on `h`, the one over counts is
  defined on any related `d`, returns the same, and ends in related states.
- `ptRmv_exist` is where the invariant earns its keep:
  `consistent_pmap_domain` says the entry being removed is among the page's
  owners exactly once, so the count goes down by exactly one.
- With `MPTNew.ptResv_triple`, the C code of `pt_resv` is tied to
  mCertiKOS's top specification of it, through three steps: code to
  count-based spec, and count-based spec to owner-list spec.

### `MALInit.lean` and `MContainerInit.lean`: boot, at the level of specifications

- `mem_init_spec`: the page count is the end of the highest region of the
  boot memory map (`real_nps`), and each page's entry is computed from the
  map (`real_AT`): kernel outside `[kern_low, kern_high)`, normal inside if a
  usable region covers the page, reserved otherwise.
- `real_nps_range`, `real_at_kern_valid`, `real_at_usr_valid`: mCertiKOS's
  lemmas, under its assumptions on the memory map (`MM_valid`, `MM_kern`).
- `mem_init_inv`: `mem_init_spec` establishes `ATInv`.
- `container_init_spec`: after `mem_init`, the root container gets every free
  page as its quota (`real_AC`, `real_quota`).
- `container_init_inv`: `container_init_spec` establishes `ATInv`,
  `Container_valid` and `quota_bounded_AT`.

So the invariants that the refinement theorems assume now have a beginning
(`container_init_inv`) and are kept by every specification
(`MContainerInv.lean`, `palloc_inv`, `pfree_inv`).

### `MALInitC.lean` and `MContainerInitC.lean`: the C code of boot

- **The memory map is in the region**, at a base `mmb` above the allocation
  table and the containers: the number of regions, then start, length and
  "usable" of each (`MatchMMap`). `get_size`, `get_mms`, `get_mml` and
  `is_usable` are reads of it. `boot_loader` is not code here; what it leaves
  is the precondition.
- `while_inv`: a loop rule with an invariant and a measure. The earlier ports
  proved each loop by a hand-written induction.
- `mem_init`'s three loops, each with its own theorem: `npsLoop_run` (the
  page count), `scanLoop_run` (is page `i` inside a region), `fillLoop_run`
  (the type of each page).
- **`mem_init_triple`: the C code refines `mem_init_spec`.** It writes only
  the allocation table.
- `MM_correct` (ported from `AuxStateDataType.v`) is what makes the code
  agree with the specification. The code stops at the first region that
  contains the page; the specification asks for any usable region that does.
  They agree because overlapping regions have the same permission.
- **`container_init_triple`: the C code refines `container_init_spec`.** It
  calls `mem_init` through `mem_init_triple`, counts the free pages
  (`cntLoop_run`) and writes container 0.
- As in mCertiKOS (`valid_preinit_container`), `container_init_triple` assumes
  every container is unused before initialisation.

What differs from the sources:

- `i < kern_low || i >= kern_high` is written with `+`, and `&&` with `*`
  (ClightL has no short-circuit operators); `>`, `<=`, `>=` are written with
  the unsigned `<`.
- `kern_high < 2^20` is assumed, so `(i + 1) * PgSize` does not wrap. In
  mCertiKOS it is the constant 983040.
- The two theorems are about the code inside a critical section. Boot runs
  before any other CPU, so no lock is taken in the sources.

### `MPTInit.lean`: the page tables at boot

- `real_idpde` (ported from `CalRealIDPDE.v`) and `idpde_init_spec`.
- The C code of `idpde_init`: `container_init`, then 1024 x 1024 calls of
  `set_IDPTE`.
- **`idpde_init_triple`: the C code refines `idpde_init_spec`.** The proof
  uses `container_init_triple` and `setIDPTE_triple`, not their code.
- The memory map sits between the containers and the page-table pool
  (`cb + 5 * num_id ≤ mmb`, `mmb + 1 + 3 * size ≤ pb`).

- `real_ptp` (ported from `CalRealPTPool.v`) and `pt_init_comm_spec`: every
  process's directory points at the identity table outside `[256, 960)` and
  is empty inside.
- The C code of `pt_init_comm`: `idpde_init`, then for each process 1024
  calls of `set_PDE` or `rmv_PDE`.
- **`pt_init_comm_triple`: the C code refines `pt_init_comm_spec`**, through
  `idpde_init_triple`, `setPDE_triple` and `rmvPDE_triple`.
- As in mCertiKOS (`valid_uninitialized`), it assumes no directory entry
  holds a table before initialisation (`NV`).
- The loop variables are the locals `set_PDE` and `rmv_PDE` take their
  arguments in (`n`, `i`), so there is no separate argument passing.

- `real_pt` (ported from `CalRealPT.v`) and `pt_init_kern_spec`: process 0
  is the kernel, and its directory maps the whole address space with the
  identity table.
- **`pt_init_kern_triple`: the C code refines `pt_init_kern_spec`**, through
  `pt_init_comm_triple` and 704 calls of `set_PDE`.

Still missing for boot: `pt_init` (`pt_init_kern(); set_pt(0); set_pg();`)
and `pmap_init`, which only calls it. They load `CR3` and turn paging on, so
they wait for the machine model (stage 6).

### `MPTResv2.lean`: one page in two address spaces

- `ptResv2_spec` and the C code of `pt_resv2`: allocate a page, map it in the
  first process, and if that worked map it in the second.
- **`ptResv2_triple`: the C code refines `ptResv2_spec`.**
- `ptInsert_keeps`: **`ptInsert_spec` preserves the allocation-table
  invariant**, keeps every container within its quota (`UQ`), and returns at
  most `MagicNumber`. `pt_resv2` needs this between its two calls of
  `pt_insert`. `ptResv2_keeps` is the same for `ptResv2_spec`.
- `ptInsert_flags`, `ptResv2_flags`: they do not change the paging flags.
- **Footprints.** `pt_alloc_pde`, `pt_insert`, `pt_resv` and `pt_resv2` now
  say which cells they leave alone: everything from `cb + 5 * num_id` up to
  `pb`. Before, their theorems allowed any cell to change. The shared-memory
  table sits in that gap and depends on this.
- The C comment in the sources tests `result == MagicNumber` before the
  second `pt_insert`. The Clight code they verify tests `!=`, which matches
  the specification and is what is ported.

### `MShareIntro.lean`, `MShareOp.lean`, `MShare.lean`: shared memory

Two processes share a page by both offering. For each ordered pair of
processes the kernel keeps a state (ready, pending, dead), whether the first
has seen it, and the address the first offered.

- **State**: `SData` is `PTData` with `smspool`. **Region**: the table is at
  `sb`, between the containers and the page-table pool (`SLayout`); entry
  `(p1, p2)` is three cells at `sb + (p1 * num_proc + p2) * 3`: location,
  state, seen (`MatchSMS`, `MatchSP`, `MatchS`).
- `sm_get`, `sm_put`: what the three cells of a valid entry hold, and that
  rewriting them gives the table with that entry replaced. Every proof in
  these files goes through these two.
- **The seven accessors** refine their specifications.
- **`shared_mem_to_pending`, `shared_mem_to_dead`,
  `get_shared_mem_status_seen`** refine theirs.
- **`toReady_triple`: `shared_mem_to_ready` refines its specification.** It
  reads the address the other process offered, calls `pt_resv2`
  (`ptResv2_lift`: the page-table theorem in the state with the table, which
  it leaves alone), and marks both directions ready.
- **`status_triple`, `offer_triple`: `shared_mem_status` and
  `offer_shared_mem` refine their specifications.** `offer_triple` uses the
  theorems of `shared_mem_to_ready`, `shared_mem_to_dead` and
  `shared_mem_to_pending`, not their code.
- **`smInit_triple`**: the two loops of `shared_mem_init` clear the table
  (`real_smspool`).

What differs from the sources:

- All these specifications require paging to be on (`pg = true`). Nothing
  ported turns it on yet, so the theorems are about states that the ported
  boot code does not reach. `sharedmem_init_spec` is stated; only its loop
  is verified.
- `offer_triple` and `toReady_triple` assume the allocation-table invariant
  and that every container is within its quota, as `pt_resv2` does.
- The functions take their arguments in the locals `pid1`, `pid2`, `sva`.
  Accessors take the two processes as expressions, so `get(pid2, pid1)` needs
  no argument passing.
- The Clight of `offer_shared_mem` copies each result into a second
  temporary. That copy is left out.
- `sharedmem_init_spec` sets the allocation table (`real_AT`) where the
  sources set owner lists (`real_LAT`).

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
- Boot: see `MALInit.lean`, `MContainerInit.lean` and their C code in
  `MALInitC.lean`, `MContainerInitC.lean`.
- The getters and the setters of `MBoot` (`set_at_u_spec` and the like) have
  no invariant lemmas. The setters do not preserve the invariant one at a
  time.

# Retired prototypes

Before the mCertiKOS sources were checked, this project had its own
simplified allocator, page tables, containers and page ownership
(`KernPT.lean`, `KernContainer.lean`, `KernOwner.lean`, and the allocator in
`KernPAlloc.lean`). They were verified, but their state and specifications
were not mCertiKOS's. The ports above replace them, and the three files were
removed on 2026-11-19. They remain in the git history, up to the commit
before "Retire the memory-management prototypes".

`KernPAlloc.lean` and `KernFrame.lean` stay. They hold the lock rules
(`cs_guarantee`, `cs_guarantee1`, `cs_guarantee2`), `Runs` and the frame
lemmas that the ports use. The simplified `palloc` in `KernPAlloc.lean` is
unused by the ports.

## What stands in the way of the rest

- **No pointers or structs in ClightL.** Kernel objects are regions of
  32-bit cells indexed by number. That fits tables (allocation table,
  page-table entries, thread control blocks as fixed-size records). Where
  mCertiKOS stores a pointer, the port stores a number (see `MPTIntro.lean`).
- **No function calls in ClightL.** A call is the callee's statement, inlined.
  Arguments are passed in agreed local variables. Triples make this sound to
  reason about, but the code is not literally the C functions.
- **Invariants of the page-table layers.** `ptInsert_spec` and
  `ptResv2_spec` preserve the allocation-table invariant
  (`ptInsert_keeps`, `ptResv2_keeps`). `ptRmv_spec` and the container
  invariants under page-table operations are not done. The simulation in
  `PTInitGen.lean` assumes the upper invariant (`HInvI`). That the owner-list
  specifications preserve it is not proved, except for `alloc_spec`
  (`alloc_inv_I`).
- **Invariants along the shared log** (stage 4). The invariants are proved
  preserved by the specifications. `Triple.locked` assumes them when the lock
  is taken. Nothing yet shows that every release re-establishes them.
- **No machine model.** `set_pt`, `set_pg`, context switch, traps and
  virtualization are about `CR3`, registers, privilege levels and assembly.
  Until then nothing establishes `pg = true`, which the shared-memory
  specifications require.
- **Boot** (stage 2): `mem_init`, `container_init`, `idpde_init`,
  `pt_init_comm` and `pt_init_kern` are ported, code and specification.
  `pt_init` and `pmap_init` wait for the machine model.

## Order

See "How the ports are organised" above. Stages 2 and 3 are done except for
`pt_init` and `pmap_init` (machine model). Next: stage 4, the invariants
along the shared log.
