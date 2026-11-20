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
| `MPTKern`, `MPTInit` | kernel page table, `pt_init`, paging on (`set_pg`, `set_cr3`) | **ported**: `MCPU.lean`. `CR3` and the paging bit are two words of the kernel region; `set_pt` refines `setPT'_spec`, `set_pg` refines `setPG1_spec`, and `pt_init` refines `pt_init_spec` (`pt_init_triple`). `pt_init_factors`: the specification is its three calls, using `real_pt_PMap_valid` and `real_pt_PMap_kern` |
| `MPTNew` | `pt_new`, `pt_resv`, `pt_resv2`, `pmap_init` | **ported**: `MPTNew.lean`. `pt_new` refines `pt_new_spec`; `pt_resv` refines `ptResv_spec` (stated over `container_alloc_spec` and `ptInsert_spec`); `pt_resv` under the lock is `MMInv.ptResv_locked_inv`. `pt_resv2` is in `MPTResv2.lean` (`ptResv2_triple`). `pmap_init` only calls `pt_init` (`MCPU.lean`) |
| `MShareIntro` | the shared-memory table and its seven accessors | **ported**: `MShareIntro.lean`. Each accessor refines its spec (`getState_triple`, `getSeen_triple`, `getLoc_triple`, `setState_triple`, `setSeen_triple`, `setLoc_triple`, `clear_triple`) |
| `MShareOp` | `shared_mem_to_pending`, `shared_mem_to_dead`, `shared_mem_to_ready`, `get_shared_mem_status_seen`, `shared_mem_init` | **ported**: `MShareOp.lean` (`toPending_triple`, `toDead_triple`, `toReady_triple`, `statusSeen_triple`). `shared_mem_init` as a whole function is `sharedmem_init_triple` in `MInit.lean` |
| `MShare` | `shared_mem_status`, `offer_shared_mem` | **ported**: `MShare.lean` (`status_triple`, `offer_triple`) |
| abstract ownership (`PTInitGen`) | the logical table `LAT` with its owner lists, `consistent_pmap`, `consistent_pmap_domain`; `alloc_spec`, `ptInsert0_spec`, `ptRmv0_spec`, `ptResv_spec` over owner lists | **ported**: `PTInitGen.lean`. The count-based specs refine the owner-list ones: `alloc_exist`, `ptInsertPTE_exist`, `ptAllocPDE_exist`, `ptInsert_exist`, `ptRmv_exist`, `ptResv_exist`. Missing: `ptFreePDE0_spec`, and that the owner-list specs preserve the upper invariant |
| **Process management** (`proc`) | | |
| `PKContext`, `PKContextNew` | kernel contexts, `kctxt_switch`, `kctxt_new` | **ported, with a different kind of context**: `KMachine.lean` (a kernel context is a suspended ClightL computation; `cswitch`, `set_SP`, `set_RA` are steps of the kernel machine), `PKContext.lean` (`kctxt_switch_refines`, `kctxt_sp_refines`, `kctxt_ra_refines`), `PThreadSpawn.lean` (`kctxt_new_run`). mCertiKOS's is six saved registers and twenty assembly instructions |
| `PThreadIntro`, `PThreadInit` | thread control blocks | **`PThreadIntro` ported**: `PThreadIntro.lean`. `get_state`, `get_prev`, `get_next`, `set_state`, `set_prev`, `set_next`, `tcb_init` refine their specs; `threadInit_triple` verifies the loop of `thread_init` (`real_tcb`). `thread_init` as a whole function is `thread_init_triple` in `MInit.lean` |
| `PQueueIntro` | thread queues: `get_head`, `get_tail`, `set_head`, `set_tail`, `tdq_init` | **ported**: `PQueueIntro.lean`. Each accessor refines its spec (`getHead_triple`, `getTail_triple`, `setHead_triple`, `setTail_triple`, `tdqInit_triple`); `tdqueueInit_triple` verifies the loop of `tdqueue_init` (`real_tdq`). `tdqueue_init` as a whole function is `tdqueue_init_triple` in `MInit.lean` |
| `PQueueInit` | `enqueue`, `dequeue`, `queue_rmv` on linked control blocks | **ported**: `PQueueInit.lean`. `enqueue_triple`, `dequeue_triple`, `queueRmv_triple`; the specs keep `TCBCorrect_range` and `TDQCorrect_range` (`enqueue_keeps`, `dequeue_keeps`, `queueRmv_keeps`) |
| `PAbQueue` (`AbQueueGen`) | queues as lists; the refinement from lists to linked control blocks | **ported**: `PAbQueue.lean` (data, specs, relation), `PAbQueueGen.lean` (`enqueue_exists`, `dequeue_exists`, `queue_rmv_exists`, `get_state_exists`, `set_state_exists`), `PAbQueueInv.lean` (the five invariants are established and kept; `enqueue0_triple`, `dequeue0_triple`, `queueRmv0_triple`, `getState0_triple`, `setState0_triple`). Missing: the page-table and shared-memory primitives restated over the list view |
| `PCurID` | current thread: `get_curid`, `set_curid` | **ported**: `PCurID.lean` (`getCurid_triple`, `setCurid_triple`, `liftA`) |
| `PThreadSched`, `PThread` | `thread_spawn`, `sched_init`, `thread_wakeup`, `thread_sched`, `thread_yield`, `thread_sleep` | **ported**: `PSchedInit.lean` (`sched_init_triple`, `sched_init_inv`), `PThreadSched.lean` (`thread_wakeup_triple`), `PThreadSwitch.lean` (`thread_sched_run`, `thread_yield_run`, `thread_sleep_run`), `PThreadSpawn.lean` (`thread_spawn_run`). `ThreadLayer.lean` is an earlier prototype of a different thing. Not done: that every parked thread is eventually resumed, and reasoning about one thread alone |
| `PIPCIntro`, `PIPC` | synchronous IPC: the channel pool and its accessors, `get_kernel_pa`, `syncsendto_chan_pre`, `syncsendto_chan_post`, `syncreceive_chan`, `proc_init` | **ported**: `PIPCIntro.lean` (the seven accessors and `get_kernel_pa` refine their specs; `liftCI`), `PIPC.lean` (`syncSendPre_triple`, `syncSendPost_triple`), `FlatMem.lean` (`flatmem_copy` as a loop, `flatmemCopy_triple`), `PIPCRecv.lean` (`syncReceive_triple`), `PProcInit.lean` (`proc_init_triple`, `proc_init_inv`). Not done: the two halves of a send joined with the sleep between them, which mCertiKOS does in the trap layer |
| `PUCtxtIntro`, `PProc` | user contexts, `proc_create`, `proc_start_user`, `proc_exit_user` | **ported**: `PUCtxtIntro.lean` (the top state `UData`; `uctx_get`, `uctx_set`, `uctx_set_eip`, `save_uctx` refine their specs; `liftIU`), `UMachine.lean` (user mode: a trap enters the kernel, a finished kernel computation returns), `PProc.lean` (`proc_create_run`, `procExitUser_triple`, `procStartUser_run`, `start_user_ustar`). `elf_load` and `tss_switch` are left out |
| **Trap handling** (`trap`) | | |
| `TTrapArg`, `TTrap`, `TDispatch`, `TSysCall` | system-call arguments, handlers, dispatch, the kernel's entry points | **ported**: `TTrapArg.lean` (`uctx_arg1` … `uctx_arg6`, `uctx_set_errno`, `uctx_set_retval1` … `5`), `TTrap.lean` (`trap_sendtochan_pre`, `trap_sendtochan_post`, `sys_receive_chan`, `sys_get_quota`, `ptfault_resv`), `TDispatch.lean` (`container_can_consume`, `sys_proc_create`, `syscall_dispatch_c`), `TSysCall.lean` (`syscall_dispatch`, `pgf_handler`, `sys_yield`, from user mode back to user mode). Missing: `SYS_share` and `SYS_print` in the dispatcher, and the virtualization handlers |
| **Other** | | |
| `objects/ObjVMX`, `ObjVMCS`, `ObjEPT` | virtualization | missing |
| `security` | noninterference (`ObsEq`, `Integrity`, `Confidentiality`, `ConfidentialityRestore`, `Security`) | **ported up to the unwinding conditions**: `ObsEq.lean` (the observation function), `Integrity.lean`, `Confidentiality.lean`, `ConfidentialityPF.lean` (the page fault), `Security.lean` (`KPass`: one passage through the kernel; `integ`, `conf`, `conf_restore`). Missing: the theorem for whole executions (`SecurityBigstep.v`, `end_to_end_security`), which needs a model of user programs; integrity and confidentiality of user-mode instructions; preservation of the security invariants |
| `layerlib`: `LAsm`, `CompCertiKOS` | layered assembly, the compiler | missing: no machine model, no verified compiler |
| layer calculus | linking layers vertically with `high_level_invariant` | partial: each port states refinement to the spec; invariant preservation and layer linking are not done per layer |

### What a port still leaves out

Even for the ported layers:

- `ikern` and `ihost` are in the top state (`UData`) and checked by the
  specifications from `PUCtxtIntro` up. The specifications below do not
  mention them.
- Indices are `Nat` rather than `Z`.
- The objects live in lock regions, not in CompCert memory.
- `high_level_invariant`: the parts about the allocation table and the
  containers are proved preserved by the specifications
  (`MContainerInv.lean`). The allocation-table invariant and the quota bound
  are carried along the shared log (`LogInv.lean`, `MMInv.lean`).
- Boot is ported in full, code and specification, from `mem_init` up to
  `proc_init` (`MCPU.lean`, `MInit.lean`, `PSchedInit.lean`,
  `PProcInit.lean`).

## How the ports are organised

- **Agreed order** (2026-11-19): 0 calling convention for layers, 1 page
  tables, 2 boot and init, 3 shared memory, 4 invariants along the shared
  log, 5 thread data, 6 machine model and scheduler, 7 IPC, 8 processes and
  traps, 9 security and virtualization. Stages 0 to 8 are done, except for the linking step for the rely of stage 4 and what the machine model still lacks (the lock at the kernel boundary, interrupts, memory accesses through the page table).
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
- **`Triple.locked_inv`** (`LogInv.lean`) is `Triple.locked` with the
  invariant on the log: the caller assumes the log has it, not that the
  region matches anything.
- **`LayerStep.lean`: steps.** `Step εR c i M F s σ d σ' d'` is a triple for
  one starting point: from locals `σ` and data `d` the code ends with `σ'`
  and `d'`. Steps compose like an interpreter run (`Step.seq`,
  `Step.ite_true`, `Step.while_inv`), so a function that makes several calls
  is run through one step lemma per call, with no intermediate predicates.
  `Step.triple` turns the result into a triple. Used from the thread queues
  on.
- **`Triple.sim`** (`LayerStep.lean`) is data abstraction. When a layer's
  state is a view of the state below (`R a d`), a triple below gives a triple
  above, if abstract preconditions give concrete ones and concrete results
  are views of abstract results. `PAbQueue` gets its triples this way.

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

`pt_init` (`pt_init_kern(); set_pt(0); set_pg();`) and `pmap_init`, which
only calls it, load `CR3` and turn paging on. They are in `MCPU.lean`.

The three triples of this file name their footprint: cells below the end of
the containers and from the page-table pool on. That is what lets the
control registers, which sit between, survive them.

### `MCPU.lean`: `CR3`, the paging bit, `pt_init`

The first part of the machine model (stage 6).

- **The model.** mCertiKOS's bottom layer has two trusted primitives,
  `set_cr3` and `set_pg`, whose specifications are part of its machine
  model. Here the two registers are two words of the kernel region, at
  `cpub` and `cpub + 1`, and the primitives write them. `MatchCPU` ties them
  to the abstract state: `CR3` holds the address of directory `PT`
  (`relate_PT`), and the paging word is nonzero exactly when `pg` holds.
  Before this file no cell constrained `pg` or `PT`.
- `PMap_common`, `PMap_kern`, `PMap_usr`, `PMap_valid` are mCertiKOS's.
  `real_pt_get` gives every entry of the initial page tables;
  `real_pt_PMap_valid` and `real_pt_PMap_kern` follow (the second for
  `kern_low = 262144`, `kern_high = 983040`, mCertiKOS's constants).
- `setPT_triple`, `setPG_triple`: `set_pt` and `set_pg` refine `setPT'_spec`
  and `setPG1_spec`.
- **`pt_init_factors`**: `pt_init_spec` is `pt_init_kern_spec`, then
  `setPT'_spec 0`, then `setPG1_spec`. The side conditions of the last two
  say the kernel's page table is valid and maps the kernel by the identity,
  which is what makes turning paging on safe in mCertiKOS.
- **`pt_init_triple`**: `pt_init` refines `pt_init_spec`. Afterwards `pg` is
  true in the abstract state and in the region.

What the model leaves out:

- One `CR3` and one paging bit, as in single-core mCertiKOS, not one per
  CPU. The registers are written with the kernel lock held.
- No access goes through the page table. Kernel code runs on the identity
  map; user-mode accesses are not modelled yet. So `PMap_kern` is a
  condition the code meets, not one the semantics here depends on.
- `ikern`, `ihost`, the trap state and kernel contexts are not in it yet.

### `MInit.lean`, `PSchedInit.lean`: initialisation as whole functions

- **`KLayout`: one layout for the whole kernel region.** In order: the
  allocation table, the containers, the boot loader's memory map, `CR3` and
  the paging bit, the shared-memory table, the control blocks, the queues,
  the current thread, the page-table pool, the identity map, flat memory.
  Earlier the memory map and the tables above it were constrained by
  separate hypotheses.
- **`sharedmem_init_triple`, `thread_init_triple`, `tdqueue_init_triple`**:
  each `*_init` is the one below followed by its own loop, and refines its
  specification from the state the boot loader leaves (`init = false`,
  paging off, no container in use, no page table). Each proof calls the
  triple of the function below, not its code.
- **`tdqueue_init0_triple`**: the same code refines the specification over
  lists. The relation `RelA` holds before boot as well: its pointer-view
  invariants are conditional on `pg`, as in mCertiKOS.
- **`sched_init_triple`**: `tdqueue_init(mbi_adr); set_curid(0);
  set_state(0, TSTATE_RUN);` refines `sched_init_spec`.
  **`sched_init_inv`**: the state it reaches satisfies the list view's
  invariants.

So boot now reaches the states the operations are about: `pg = true`, every
table initialised, thread 0 running.

### `PSchedBoot.lean`: boot under the lock

- `sched_init_mmi`: `sched_init_spec` establishes the memory-management
  invariant, `pg = true` and `cid = 0`.
- **`sched_locked_inv`**: `acquire; sched_init; release`, on a log whose
  kernel region is as the boot loader leaves it, finishes idle and releases
  a region matching a state with paging on, the memory-management invariant
  (`MMI`) and the list view's invariants (`AInv`). This is
  `MMInv.boot_locked_inv` for the whole of boot. The rely on the other CPUs
  is assumed, as everywhere in stage 4.

### `KMachine.lean`: kernel contexts (machine model, second part)

mCertiKOS's kernel context is six saved registers, and `cswitch` is twenty
assembly instructions that store them and load six others. What that means
is control: execution continues where the other context left off. ClightL
has no registers, stack or code pointers, so this could not be transcribed.
It was decided on 2026-11-19 to model it as follows.

- **A kernel context is a suspended ClightL computation** (`KCtx`): the
  statement to run, the continuation (the stack and return address), and the
  locals (the saved registers).
- **`kstep`**: the kernel machine. Its state is the running computation, the
  pool of kernel contexts, and the shared log. Ordinary steps are ClightL's.
  Three calls are the machine's own: `cswitch(n, n')` parks the running
  computation in slot `n`, about to return `0` from the call, and resumes
  slot `n'`; `set_SP(n)` gives context `n` an empty stack; `set_RA(n, f)`
  makes it start at function `f`, a number looked up in the machine's text.
- **`KStar.of_runs`**: code of the layers below runs on the kernel machine
  as it did, under any continuation, and leaves the pool alone. So every
  triple proved before applies unchanged.

What it leaves out: the pool belongs to one CPU's machine, so threads do not
move between CPUs. The switch is one trusted step, where mCertiKOS verifies
assembly.

### `PKContext.lean`: the context primitives

- `KData` is `CData` with the pool. `kctxt_switch_spec`, `kctxt_sp_spec`,
  `kctxt_ra_spec` keep mCertiKOS's shape; only the type of a context
  changes. The specifications never look inside one.
- `kctxt_switch_refines`, `kctxt_sp_refines`, `kctxt_ra_refines`: the three
  machine calls refine them.

### `PThreadSwitch.lean`: `thread_sched`, `thread_yield`, `thread_sleep`

mCertiKOS writes these three in assembly. They are transcribed call by call:

```
thread_sched:  new = dequeue(num_chan); set_state(new, RUN); old = get_curid();
               set_curid(new); kctxt_switch(old, new)
thread_yield:  cid = get_curid(); set_state(cid, READY); enqueue(num_chan, cid); thread_sched()
thread_sleep:  cid = get_curid(); set_state(cid, SLEEP); enqueue(chan, cid); thread_sched()
```

- `thread_sched_spec`, `thread_yield_spec`, `thread_sleep_spec` are
  mCertiKOS's, and so is `CurIDValid`.
- **`thread_sched_run`, `thread_yield_run`, `thread_sleep_run`**: run on the
  kernel machine, each ends with the head of the ready queue running, the
  caller parked in its own slot as a computation about to return from the
  call, and the region matching the new state. `thread_sched_eq`,
  `thread_yield_eq`, `thread_sleep_eq`: that state is the specification's.
- Each also gives the invariants of the new state (`AInv`, `CurIDValid`,
  the current thread in range).
- The proofs use the triples of the list view and one machine step. The
  invariants are used as in mCertiKOS: the thread taken from the ready queue
  is on it (`InQ`), so it has a container (`NotInQ`) and is not the current
  thread (`CurIDValid`).
- As in mCertiKOS, `thread_yield` and `thread_sleep` are undefined when the
  ready queue is empty.
- Each theorem also says which cells the code writes (`SchedF`: the control
  blocks, the queues and the current-thread word). That is what lets them be
  used in the larger state of the later layers.
- What differs: the lock is held across the switch, so the thread resumed
  finds it held (the CPU holds it, not the thread). `clear_cr2` is left out.
  The context saved has the locals as the scheduler's code left them; the
  theorems say which locals that code writes.

### `PThreadSpawn.lean`: `kctxt_new`, `thread_spawn`, and passthrough

- **`liftPC`**: a triple of the page-table layers holds in the state with
  threads, queues and the current thread, if it writes only cells of those
  layers and keeps `pg`. It crosses the shared-memory table, the control
  blocks, the queues, the list view and the current thread at once. This is
  the passthrough that was missing; `pt_new` is its first use (`ptNewC`).
- **`kctxt_new_run`**: `pt_new`, then `set_SP` and `set_RA`: a child
  container, and a context that starts at `entry` on an empty stack.
- **`thread_spawn_run`**: then the new thread is ready, at the back of the
  ready queue. `split_child_free` (the slot a split gives is unused) with
  `NotInQ` puts the new thread on no queue, which `enqueue` requires.

### `PThreadSched.lean`: `thread_wakeup`

- `thread_wakeup_spec` is mCertiKOS's: the head of a sleep queue goes to the
  ready queue (queue `num_chan`).
- **`thread_wakeup_factors`**: the specification is its three calls,
  `dequeue`, `set_state(READY)`, `enqueue`, each by its specification over
  lists. As in mCertiKOS's code proof the invariants are needed: `InQ` says
  the thread taken off the queue was on it, then `NotInQ` says it has a
  container, which `set_state` and `enqueue` require.
- **`thread_wakeup_triple`**: the C code refines the specification. It is
  the first function verified on the list view alone. The proof calls
  `dequeue0_triple`, `setState0_triple` and `enqueue0_triple` and never
  mentions a control block or a queue pointer.
- `thread_wakeup_keeps`: the specification keeps `AInv`.

### `PIPCIntro.lean`: the IPC channels

- **State**: `IData` is `CData` with `syncchpool`. Each thread has a channel
  `SyncChanValid to paddr count`: who it is sending to, the kernel's address
  of its buffer, and the length. The three fields are machine words, as in
  mCertiKOS. **Region**: three cells per channel at `ipb`, after the
  current-thread word (`ILayout`, `MatchI`).
- The six accessors and `init_sync_chan` refine their specifications
  (`getSyncTo_triple` … `initSync_triple`).
- **`getKernelPa_triple`**: `get_kernel_pa` refines `get_kernel_pa_spec`. It
  gives the kernel's address of a user address, read through the page table.
  It calls `pt_read` by its triple, carried up by `liftPC` and `liftCI`.
- `stepCI`, `liftCI`: steps and triples of the layers below hold in `IData`,
  if they do not write the pool.
- `syncInit_step`: the loop of `proc_init` gives `real_syncchpool`.

### `FlatMem.lean`: `flatmem_copy`

- `flatmem_copy_spec` is mCertiKOS's: copy `count` words (at most 1024)
  between two allocated pages below `adr_low`.
- **`flat_write`**: writing a word of an allocated page keeps the whole
  memory-management region matching. The second-level page tables are in
  hidden pages (`PGHide`), so the write cannot land in one.
- **`flatmemCopy_triple`**: the loop refines the specification.
- What differs: in mCertiKOS `flatmem_copy` is a primitive of the bottom
  layer, without code. Here it is a loop over the cells of flat memory. Flat
  memory is indexed by word here and by byte there.

### `PIPC.lean`, `PIPCRecv.lean`: synchronous send and receive

- A send is two calls around a sleep. `syncsendto_chan_pre` publishes the
  buffer in the sender's channel: the receiver, the kernel's address of the
  buffer, the length. `syncsendto_chan_post` runs after the sender is woken.
  It reads the count the receiver left, or reports that nobody received.
- `syncreceive_chan`: if the sender is sending to the caller, copy its buffer
  (`flatmem_copy`), write the count into the sender's channel, mark the
  channel answered, and wake the sender (`thread_wakeup`).
- **`syncSendPre_triple`, `syncSendPost_triple`, `syncReceive_triple`**: the
  three functions refine their specifications. Every call inside goes through
  the callee's step or triple: `get_curid`, `get_state`, the channel
  accessors, `get_kernel_pa`, `flatmem_copy`, `thread_wakeup`.
- `stepPC` (`PIPCRecv.lean`) is `liftPC` for steps.
- What differs: the code is the Clight that mCertiKOS verifies. The C in its
  comments differs from it in two places (what `syncsendto_chan_pre` returns,
  and the argument order of `flatmem_copy`). The code compares against
  `num_chan` where the specifications say `num_proc`; they are one constant
  in mCertiKOS, and the theorems assume `num_proc ≤ num_chan`.
  `syncReceive_triple` assumes the queue invariants (`AInv`), which
  `thread_wakeup` needs.
- Not done: the two halves of a send joined with the sleep between them and
  a receive by another thread. mCertiKOS does that in the trap layer.

### `PProcInit.lean`: `proc_init`

- `proc_init_spec` is `sched_init_spec` followed by `real_syncchpool`
  (`proc_init_eq`).
- **`proc_init_triple`**: `sched_init`, then `init_sync_chan` for every
  channel, refines it, from the region as the boot loader leaves it.
- `proc_init_inv`: afterwards the queue invariants hold, thread 0 is the
  current thread and is running, and every channel is valid and idle.

### `PUCtxtIntro.lean`: user contexts and the top state

- **State**: `UData` is `IData` with the kernel contexts, the user contexts
  (seventeen registers per process, each a machine word or unknown), and the
  flags `ikern` and `ihost`. It is the state every later file works on.
  **Region**: seventeen cells per process at `ucb`, after the channels
  (`ULayout`, `MatchU`).
- `uctxGet_triple`, `uctxSet_triple`, `uctxSetEip_triple`: the accessors
  refine their specifications.
- **`saveUctx_triple`**: `save_uctx(u0, …, u16)` refines `save_uctx_spec`.
  Its seventeen arguments are locals.
- `stepIU`, `liftIU`: steps and triples of the layers below hold in `UData`.

### `UMachine.lean`: user mode (machine model, third part)

mCertiKOS's processor is in kernel mode or in user mode. It was decided here
to model that as follows, continuing the model of kernel contexts.

- `UState`: the machine is either running a kernel computation, or in user
  mode with seventeen registers.
- **A trap** takes it from user mode to the handler of the trap, on an empty
  kernel stack, with the user's registers in the locals `u0` … `u16`. The
  user program may have left anything in them, so they are arbitrary.
- **A kernel computation that finishes on an empty stack returns to user
  mode** with the registers in `u0` … `u16`. This is `trap_out`.
- So `ikern` is the kind of state the machine is in. What a user program
  does between two traps is not modelled, as in mCertiKOS.
- Not in the model: the lock at the boundary (the kernel is entered and left
  inside a critical section), and interrupts.

### `PProc.lean`: processes

- **`proc_create_run`**: `proc_create` on the kernel machine does what
  `proc_create_spec` says. It is `thread_spawn` with `proc_start_user` as the
  entry, then seven writes to the child's user context
  (`proc_create_factors`). So a new process, the first time it is scheduled,
  goes to user mode at its entry point.
- **`procExitUser_triple`**: `proc_exit_user` saves the registers of the
  trap and loads the kernel's page table.
- **`procStartUser_run`**, **`start_user_ustar`**: `proc_start_user` loads
  the process's page table and its registers, and the machine then leaves the
  kernel with them.
- `toK`, `putK`, `matchU_putC`: the scheduler's theorems, stated on `KData`,
  are used on the top state through the footprints they now state.
- What differs: `trap_in`, `pt_in`, `pt_out` only change flags that no cell
  holds, so they have no code. `elf_load` (no effect on the state in
  mCertiKOS either) and `tss_switch` are left out.

### `TTrapArg.lean`, `TTrap.lean`, `TDispatch.lean`: system calls

- Arguments, error code and return values are registers of the caller's user
  context (`uctxArg_triple`, `uctxSetReg_triple`).
- **Handlers** (`TTrap.lean`): `trapSendPre_triple`, `trapSendPost_triple`,
  `trapReceive_triple`, `trapGetQuota_triple`, `ptfaultResv_triple`. Each
  reads its arguments, calls the kernel function through its triple, and
  writes the result back.
- **`ctCanConsumeU`**: `container_can_consume` refines its specification.
- **`sysProcCreate_run`**: `sys_proc_create` checks the quota, the room for
  ids and the number of children, then calls `proc_create` with the entry
  point read from the table `ELF_ENTRY_LOC` (`MatchELF`).
- **`sysDispatch_run`**: `syscall_dispatch_c` does what
  `sys_dispatch_c_spec` says.
- What differs: the dispatcher handles `SYS_spawn` and `SYS_get_quota`;
  `SYS_share` and `SYS_print` are not ported. mCertiKOS's specification of
  `sys_proc_create` is defined for image 0 only, because an entry point is a
  pointer there; here it is a number and any image is allowed. ClightL has no
  `||`, `&&` or `<=`, so the tests are nested conditionals with `<`.

### `TSysCall.lean`: the kernel's entry points

mCertiKOS's top layer exports three primitives. Each is a whole passage
through the kernel.

- **`syscall_dispatch_ustar`**: a system call. If `proc_exit_user_spec`,
  `sys_dispatch_c_spec` and `proc_start_user_spec` are defined in turn, the
  machine goes from user mode back to user mode with the registers the last
  one returns, and the region matches the final state.
- **`pgf_handler_ustar`**: a page fault, likewise with `ptfault_resv_spec`.
- **`sys_yield_run`**: a yield. The caller's kernel computation is parked,
  about to run `proc_start_user`, and the head of the ready queue runs.
- **`sys_yield_ustar`**: from user mode in one process to user mode in
  another. The process resumed was parked by an earlier yield, and it leaves
  the kernel with the user context saved for it.
- What differs: the fault address is a local at the trap, not the field `ti`.
  The theorems assume the invariants mCertiKOS carries along (valid current
  thread, queue and container invariants). The synchronous IPC handlers are
  proved but not wired to an entry point; in the mCertiKOS sources read here
  those entry points are commented out too.

### `ObsEq.lean`, `Integrity.lean`, `Confidentiality.lean`, `ConfidentialityPF.lean`, `Security.lean`: security

mCertiKOS's security proof (Costanzo, Shao and Gu, PLDI'16) is stated over the
top layer's specifications, and so is the port.

- **`observe i d`** (`ObsEq.lean`): what process `i` can see of the state.
  Its address space as its page table maps it (the physical pages are
  hidden), what is left of its quota, how many children it has, whether it
  is running, its kernel and user contexts, and, when it is running, the mode
  flags. `ObsEq i d1 d2` says `i` observes the same in both
  (`obsEq_convert`).
- **Integrity** (`Integrity.lean`): while `i` is not running, a passage of
  the running process through the kernel does not change what `i` observes.
  `integrity_syscall`, `integrity_pgf`, `integrity_yield` (for an observer
  that is neither process). `ptResv_frame` is the fact behind the page-fault
  case: `pt_resv` changes only the caller's page table and container, and
  pages that were free.
- **Confidentiality** (`Confidentiality.lean`, `ConfidentialityPF.lean`):
  what the running process observes after a passage through the kernel
  depends only on what it observed before, and so do the registers it gets
  back. `confidentiality_syscall`, `confidentiality_pgf`,
  `confidentiality_yield`.
- The confidentiality proofs go through a stronger statement than
  mCertiKOS's: the observation after is a function of the observation before
  (`obs_syscall`, with `obsDispatch`, `obsExit`, `obsStart`; `resv_obs` for
  the page fault). These functions are the kernel as a process sees it.
- **The page fault** is the interesting case. Which physical page the
  process gets depends on what the others have allocated. The observation
  hides physical pages, and a fresh page holds no data, so the process sees
  the same thing whichever page it got. `resvKind_obs`: whether a page is
  mapped, and whether a table had to be allocated too, is determined by what
  the process observed (its quota and the permissions of its address space).
- **Resumption** (`confidentiality_restore`): two states a parked process
  could not tell apart; when a yield resumes it in both, it still cannot,
  and it resumes the same kernel computation.
- **`Security.lean`** puts these on one transition relation. `KPass t d d'
  rs'` is one passage through the kernel for the trap `t` (a system call, a
  page fault, or a yield, with the registers at the trap). `integ`, `conf`
  and `conf_restore` are the three unwinding conditions, mCertiKOS's lemmas
  of the same names.
- What is assumed (`SecInv`), as in mCertiKOS's `secure_inv`: the container
  invariant, that the observer's and the caller's containers are in use, that
  the pages a process maps are not free (`MappedUsed`; in mCertiKOS it
  follows from the owner lists), and that a free page holds no data
  (`FreeNone`, mCertiKOS's `dirty_ppage`).
- Not done: that a passage preserves `SecInv`; integrity and confidentiality
  of user-mode instructions (user code is not modelled); and the unwinding
  theorem that turns the three conditions into noninterference for whole
  executions.

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

### `LogInv.lean` and `MMInv.lean`: the invariants along the log

Before this, every theorem about `acquire; s; release` assumed that the
region found under the lock matched abstract data with the operation's
precondition. Now that is a property of the log.

- `LInv i J l`: the log is valid and the region last released on lock `i`
  satisfies `J`. For a kernel lock `J b` is `∃ d, M d b ∧ I d`.
- `RelyJ εR c i J`: the rely. Whatever the environment appends, the last
  released region still satisfies `J`.
- `rstep_hmem`: an event changes the last released region only if it is a
  release by a holder that has written. So taking the lock, waiting, and
  other locks' events do not disturb the invariant.
- `acquire_runs_inv`: under the rely, acquiring finds a region with `J`.
- **`Triple.locked_inv`**: if the log has `∃ d, M d b ∧ I d` on entry, the
  region found matches such a `d`; for any such `d` with `P` the call
  finishes, and the log on exit has `∃ d', M d' b ∧ I' d'`. `I'` is what the
  operation establishes from `I`, so boot can go from one invariant to
  another.
- `MMI`: the allocation-table invariant and every container within its quota.
- **`boot_locked_inv`**: from a log whose region is as the boot loader left
  it (`PreInit`), `pt_init_kern` under the lock ends on a log with `MMI`,
  initialised.
- **`ptResv_locked_inv`, `offer_locked_inv`**: `pt_resv` and
  `offer_shared_mem` under the lock keep `MMI` on the log. The caller needs
  only that the specification is defined on the state found.

So the exit of one theorem is the entry of the next: nothing about the region
is assumed between calls.

What this does not give:

- **The rely is assumed.** See "What a port still leaves out".
- **Boot does not yet connect to the operations.** After `boot_locked_inv`
  paging is off, and `ptResv_spec` and `offer_shared_mem_spec` are defined
  only with paging on. Turning it on is `pt_init`, which needs the machine
  model.
- `PreInit` (every container unused, no directory entry holding a table, no
  page permission) is assumed of the region the boot loader leaves. In
  mCertiKOS these are invariants of the initial state.
- **A calling-convention bug found and fixed.** The earlier `ptResv_locked`
  put the process argument in the local `n` before `acquire`, and `acquire`
  uses `n` for the lock's counter. Its hypotheses were about `n` after
  `acquire`, so no caller could meet them. `ptResv_locked_inv` takes the
  argument in `pn` and copies it once the lock is held. `ptResv_locked` is
  removed.

### `PThreadIntro.lean`: thread control blocks

- **State**: `TData` is `SData` with `tcb`, one `TCBValid state prev next`
  per process. **Region**: three cells per process at `tb`, after the
  shared-memory table (`TLayout`, `MatchTCB`, `MatchTP`, `MatchT`).
- `tcb_get`, `tcb_put`: what the three cells of a valid block hold, and that
  rewriting them gives the pool with that block replaced.
- **The seven accessors** refine their specifications (`getTState_triple`,
  `getPrev_triple`, `getNext_triple`, `setTState_triple`, `setPrev_triple`,
  `setNext_triple`, `tcbInit_triple`).
- **`threadInit_triple`**: the loop of `thread_init` makes every block a dead
  thread on no queue (`real_tcb`).
- As with shared memory, the specifications require paging to be on, and
  `thread_init_spec` is stated with only its loop verified.
- `PKContext` and `PKContextNew`, which sit below this layer in mCertiKOS,
  are about saved registers and come with the machine model (stage 6).
- `matchS_frame`, `matchT_frame`: the layers up to this one depend only on
  the cells up to the end of the control blocks and from the page-table pool
  on. The cells between are free for the layers above.

### `PQueueIntro.lean`: thread queues

- **State**: `QData` is `TData` with `tdq`, one `TDQValid head tail` per
  queue, queues `0 … num_chan`. `num_proc` stands for "none". **Region**: two
  cells per queue at `qb`, after the control blocks (`QLayout`, `MatchTDQ`,
  `MatchQP`, `MatchQ`).
- **The five accessors** refine their specifications (`getHead_triple`,
  `getTail_triple`, `setHead_triple`, `setTail_triple`, `tdqInit_triple`).
  `set_head` and `set_tail` take the value as a machine word (`sv < 2^32`),
  which mCertiKOS gets from the C calling convention.
- **`tdqueueInit_triple`**: the loop of `tdqueue_init` empties every queue
  (`real_tdq`). It needs no precondition.
- **Steps for the queue operations**: `getPrevQ`, `getNextQ`, `setPrevQ`,
  `setNextQ`, `getHeadQ`, `getTailQ`, `setHeadQ`, `setTailQ`, each saying
  what one accessor does to `QData`.
- **`liftT`**: a primitive of the layers below keeps its triple in `QData`
  if its footprint stays out of the queue pool.

### `PQueueInit.lean`: `enqueue`, `dequeue`, `queue_rmv`

- The three specifications are mCertiKOS's (`enqueue_spec` and
  `dequeue_spec` from `proc/PQueueIntro.v`, `queue_rmv_spec` from
  `objects/ObjQueue.v`), on the doubly linked control blocks.
- **`enqueue_triple`, `dequeue_triple`, `queueRmv_triple`**: the C code
  refines them. The proofs follow the specification's case split and run the
  code through the accessor steps. `queue_rmv` has five paths; the one where
  `prev = next` is why its C code tests `prev != next`.
- `dequeue` and `queue_rmv` assume `TCBCorrect_range`, as mCertiKOS's code
  proofs do: it puts the `next` and `prev` they follow inside the pool.
- **`enqueue_keeps`, `dequeue_keeps`, `queueRmv_keeps`**: the specifications
  keep `TCBCorrect_range` and `TDQCorrect_range`. `real_tcb_correct`,
  `real_tdq_correct`: initialisation establishes them.
- `dequeue` leaves its result in the local `proc_index`.

### `PAbQueue.lean`, `PAbQueueGen.lean`, `PAbQueueInv.lean`: queues as lists

- **State**: `AData` is `SData` with `abtcb` (`AbTCBValid state inQ`, `inQ`
  the queue the thread is on, `-1` for none) and `abq` (`AbQValid l`, the
  queue's threads, tail first). The pointers are gone.
- **Specifications**: `get_state0_spec`, `set_state0_spec`, `enqueue0_spec`
  (cons), `dequeue0_spec` (the last leaves), `queue_rmv0_spec` (remove),
  `tdqueue_init0_spec`.
- **The relation** is mCertiKOS's `AbQ_RealQ`, with
  `abqueue_match_next_prev_rec` transcribed. `rec_iff` restates it: the head
  is the list's last element, the tail its first, and each `(x, prev, next)`
  of `links l` is the control block of `x`. `links_append` says appending
  lists appends their links, with the two ends at the join pointing at each
  other. The proofs are built on that and are new: mCertiKOS's
  `AbQueueGen.v` is about 4,700 lines, most of it this refinement.
- **`enqueue_exists`, `dequeue_exists`, `queue_rmv_exists`,
  `get_state_exists`, `set_state_exists`**: when the list operation
  succeeds, the pointer operation succeeds from every related state with the
  same result, and the results are related. They use `AbQCorrect_range`,
  `QCount` and `InQ`: a queue's list has no repeats (`q_nodup`) and queues
  are disjoint (`q_disjoint`), so a control block that changes is seen by one
  list only.
- **The invariants** (`AInv`: `AbTCBCorrect_range`, `AbQCorrect_range`,
  `NotInQ`, `QCount`, `InQ`) are established by initialisation
  (`tdqueue_init0_inv`) and kept by every operation (`set_state0_keeps`,
  `enqueue0_keeps`, `dequeue0_keeps`, `queue_rmv0_keeps`).
- **The code refines the list specifications**: `getState0_triple`,
  `setState0_triple`, `enqueue0_triple`, `dequeue0_triple`,
  `queueRmv0_triple`, over `MatchA` (the region matches some pointer state
  related to the lists). Each is the triple of `PQueueInit` carried across
  the relation by `Triple.sim`.
- `RelA` also carries the pointer view's invariants (`TCBCorrect_range`,
  `TDQCorrect_range`), which mCertiKOS keeps as the lower layer's own.
- `set_state0_spec` bounds the thread by `num_id` and `set_state_spec` by
  `num_proc`. They are one constant in mCertiKOS; here the theorem assumes
  `num_id ≤ num_proc`.
- Not done: the page-table and shared-memory primitives are not restated
  over `AData`. `liftT` brings them to `QData`; crossing to the list view
  needs one more use of `Triple.sim`.

### `PCurID.lean`: the current thread

- **State**: `CData` is `AData` with `cid`. **Region**: one cell at `cidb`,
  after the queue pool (`CLayout`, `MatchC`).
- `getCurid_triple`, `setCurid_triple`: `get_curid` and `set_curid` refine
  their specifications.
- `liftA`: the primitives of the list view keep their triples in `CData`.
- `thread_spawn`, `sched_init` and `thread_wakeup`, which mCertiKOS builds
  on this layer, are the scheduler (stage 6).

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

- The `*_refines` theorems of the allocation table and the containers still
  take the invariants as hypotheses on the region found. `pt_resv`,
  `offer_shared_mem` and boot have the version with the invariant on the log
  (`MMInv.lean`).
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
- **Invariants along the shared log** (stage 4): done for one CPU against a
  rely (`RelyJ`). The rely is what the other CPUs' own theorems guarantee,
  but that step (linking, as `Link.lean` does for the single ticket lock) is
  not redone for regions. `RelyJ` is shown to hold only with no environment
  and for an environment that does not release the lock. Only the
  allocation-table invariant and the quota bound are carried, not
  `Container_valid` or `quota_bounded_AT`.
- **The machine model is partial.** `CR3` and the paging bit are in
  (`MCPU.lean`), one copy, as words of the kernel region. Kernel contexts
  are in (`KMachine.lean`), as suspended computations in a pool that belongs
  to one CPU. User mode is in (`UMachine.lean`): a trap enters the kernel and
  a finished kernel computation returns. Not modelled: what user code does,
  interrupts, guest mode (virtualization), and memory accesses through the
  page table.
- **The lock at the kernel boundary.** Every theorem about kernel code is
  inside a critical section. The kernel entry points are proved from "lock
  held at the trap" to "lock held at the return"; acquiring at the trap and
  releasing before the return, as `Triple.locked` does for plain code, is not
  done on the machine with user mode.
- **Threads.** The scheduler functions are verified against their
  specifications, which say what one call does to the state and which
  context runs next. `sys_yield_ustar` follows one switch through: the
  process at the head of the ready queue is resumed and returns to user
  mode. Not done: that every parked thread is eventually resumed (it needs
  the others to yield), reasoning about one thread with the others as its
  environment (CertiKOS's thread-local layer), and liveness.
- **Thread data** (stage 5): control blocks, queues, the list view and the
  current thread are ported. The invariants of the list view are proved on
  the specifications. Boot establishes them on the log
  (`sched_locked_inv`); the operations under the lock that keep them there
  (as `ptResv_locked_inv` does for memory management) are not stated yet.
- **Boot**: ported in full, from `mem_init` to `proc_init`. What it
  assumes of the boot loader's state is stated as preconditions (`PreInit`
  in `MMInv.lean`, `MatchMMap`, paging off). `sched_locked_inv`
  (`PSchedBoot.lean`) runs `sched_init` under the lock and leaves the
  invariants on the log; `proc_init` has its triple but not yet that
  version.
- **The primitives over the upper states.** `liftPC` and `stepPC` carry
  any triple or step of the page-table layers to the state with the current
  thread, and `liftCI`, `stepCI` from there to the state with the channels.
  The shared-memory triples (stated over `SData`) do not have their version
  yet, and `MatchCPU` has to be carried separately (it survives any triple
  that keeps `pg`, `PT` and the two register cells).
- **Invariants at the top.** The entry-point theorems take the invariants
  as hypotheses on the state at the trap. That each passage through the
  kernel re-establishes them, so that they hold at the next trap, is proved
  only in part: the queue invariants are stated after a yield and after
  `proc_create`, but not after the dispatcher as a whole, and the container
  invariants are not stated after `proc_create`.

## Order

See "How the ports are organised" above. Stages 0 to 8 are done, with these
left open inside them:

- stage 4: the rely on the other CPUs is assumed, not derived by linking;
- stage 6: the scheduler theorems are per call, with no thread-local
  reasoning;
- stage 8: the dispatcher lacks `SYS_share` and `SYS_print`; the lock is not
  acquired and released at the kernel boundary; the invariants are assumed at
  each trap rather than carried from one to the next.

Stage 6 in files: `MCPU.lean` (`CR3`, paging, `pt_init`), `MInit.lean`,
`PSchedInit.lean`, `PSchedBoot.lean` (boot), `KMachine.lean`,
`PKContext.lean` (kernel contexts), `PThreadSched.lean`,
`PThreadSwitch.lean`, `PThreadSpawn.lean` (the scheduler).

Stage 7 in files: `PIPCIntro.lean` (the channels, `get_kernel_pa`),
`FlatMem.lean` (`flatmem_copy`), `PIPC.lean`, `PIPCRecv.lean` (send and
receive), `PProcInit.lean` (`proc_init`). These are the four primitives that
mCertiKOS's `PIPC` layer adds. Its asynchronous `sendto_chan` and
`receive_chan` are commented out in the sources and are not ported.

Stage 8 in files: `PUCtxtIntro.lean` (the top state, user contexts),
`UMachine.lean` (user mode), `PProc.lean` (`proc_create`, entering and leaving
the kernel), `TTrapArg.lean`, `TTrap.lean`, `TDispatch.lean` (system calls),
`TSysCall.lean` (the three entry points).

Stage 9, security: `ObsEq.lean`, `Integrity.lean`, `Confidentiality.lean`,
`ConfidentialityPF.lean`, `Security.lean`. The three unwinding conditions
hold for a passage through the kernel. Left in security: that the security
invariants are preserved, and the theorem for whole executions, which needs
a model of user programs. Then virtualization (`ObjVMX`, `ObjVMCS`, `ObjEPT`
and the handlers that use them), which is not started.
