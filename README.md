# lean-certikos

A prototype of CertiKOS-style verification in Lean 4: certified concurrent
layers (CCAL) for spinlocks, with safety **and liveness**, over a small
Clight-like language (ClightL). One AST is emitted to both C and Python, and
the Python translation is proved equivalent to the C.

57 Lean files, about 26,000 lines. No `sorry`. The main theorems depend only on
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Status (2026-11-18)

**Done**

- **ClightL**: a small-step C-like semantics, built for layered refinement and
  liveness: primitives query an environment context ε and append events to a
  shared log.
- **Ticket lock**:
  - protocol invariant, mutual exclusion, and 32-bit wraparound exactness;
  - per-CPU C code, guarantee, and liveness with an explicit bound;
  - refinement to an atomic lock layer (R₁);
  - contextual refinement for every client;
  - a concrete fair scheduler.
- **Multicore linking** (ticket lock): parallel composition and transfer, and
  per-CPU liveness on multicore runs. Environment fairness is derived from
  scheduler fairness.
- **Lock arrays with `pull`/`push`**:
  - per-CPU code, the atomic layer, and a fair scheduler;
  - client refinement and multicore linking;
  - no lost updates, and fair termination on the multicore machine.
- **MCS lock**:
  - protocol with ghost queue positions, mutual exclusion, and R₁ onto the same
    atomic layer as the ticket lock;
  - per-CPU code, liveness, and refinement;
  - a fair scheduler;
  - multicore linking and multicore liveness, with and without a critical
    section.
- **MCS bound numbers** (after Kim et al., APLAS 2017):
  - `swap(bound)` records the client's promised bound in the log;
  - the bounded atomic layer `H_CalLock`, with R₁ onto it;
  - critical sections respect their bound;
  - the waiting measure built from the bounds of the CPUs ahead in the queue;
  - `acquire(bound)` in the C code;
  - the bounded per-CPU guarantee;
  - the bounded multicore machine: mutual exclusion, fair termination, and every
    reachable global log is a valid `H_CalLock` log.
- **Python**: the ClightL → PyL translation, proved equivalent to the C, with
  liveness transferred to the Python side.
- **Lock arrays protecting regions**: each lock protects a block of cells.
  - `LockRegion.lean`: the protocol, per-lock mutual exclusion, R₁, and the
    data invariant (an acquirer sees exactly the region the last holder
    released).
  - `LockRegionCPU.lean`: the C code per CPU. The client
    `acquire; cell[j]++ for j < k; release` finishes on a valid log, and the
    region it releases is the previous holder's with those cells incremented
    (no lost updates). A fair region scheduler shows this is not vacuous.
  - `RegionLive.lean`: on the multicore machine, every reachable global log
    is valid, two CPUs touching the region of the same lock are the same CPU,
    and fair runs end within `K * (T * (27 + 6 * nc) + 1)` steps.
  - `RegionNoLost.lean`: no lost updates across CPUs. When every CPU has
    finished, each cell holds exactly the number of CPUs that used its lock.
- **C-to-C calls and modules**:
  - `ClightCall.lean`: functions with call frames, modules, and linking.
  - `CallStack.lean`: a real call stack, so functions call functions to any
    depth. `inc(lk)`, which calls `acquire` and `release`, refines the two
    atomic steps.
  - `ClientCall.lean`: every ticket-lock client linked with the lock module by
    real function calls refines the atomic layer.
- **Verified printers** (`PrintC.lean`, `PrintPy.lean`): parsing the printed
  tokens gives back the program (for Python, up to the nesting of sequences,
  which is all Python text can express). Both emitters use them.
- **Generic environment fairness** (`EnvFairGen.lean`): any client pool whose
  lock owner takes at most `B` steps before releasing gets `EnvFair` from a
  `K`-fair scheduler. The ticket client is one instance.
- **A minimal thread layer** (`ThreadLayer.lean`): threads sharing one CPU,
  switching only at yield points, are a special case of the multicore machine,
  so the multicore safety theorems apply to them.

- **Kernel, memory management** ([KERNEL.md](KERNEL.md) tracks the port module
  by module):
  - **Page allocator** (`KernPAlloc.lean`): `palloc` (acquire, scan the
    allocation table, release) refines an abstract allocator, and `pfree`
    clears an entry. `cs_guarantee` is the generic step for a critical
    section on one region.
  - **Two locks** (`KernFrame.lean`): `cs_guarantee2` covers a critical
    section that takes a second lock inside. `ext_frame` is the frame: code
    working on one lock leaves every other lock we hold, and its region,
    alone.
  - **Page tables** (`KernPT.lean`): two-level page tables as a region.
    `pt_insert` reads the directory, calls `palloc` under the page table's
    lock if the second-level table is missing, zeroes and installs the new
    table, and writes the entry. It refines `ptInsertSpec`
    (`ptInsert_guarantee`), with `ptRmv_guarantee` and `ptRead_guarantee`
    for unmapping and lookup. Under the invariant `PTInv`, the region is a
    map: an inserted entry reads back, every other entry is unchanged, and
    the invariant is kept (`insert_lookup_same`, `insert_lookup_other`,
    `insert_inv`).
  - **Containers** (`KernContainer.lean`): per-process memory quotas.
    `container_alloc` charges a page and calls `palloc`, `container_free`
    gives one back and calls `pfree`, and `container_split` carves a child's
    quota out of its parent's. Each refines its abstract operation
    (`ctAlloc_guarantee`, `ctFree_guarantee`, `ctSplit_guarantee`), and each
    keeps `usage ≤ quota` (`alloc_inv`, `free_inv`, `split_inv`).
  - **Ported from the mCertiKOS sources** (`MALOp.lean`, `MContainer.lean`):
    the allocation table and the containers with mCertiKOS's own abstract
    state, specifications and C code. `palloc`, `pfree`, `container_alloc`,
    `container_split` and the container getters are proved to refine
    `palloc'_spec`, `pfree'_spec`, `container_alloc_spec`,
    `container_split_spec` and the getter specs. mCertiKOS's invariants on
    these two layers (`Container_valid`, `quota_bounded_AT`, the allocation-table
    invariant) are ported and proved preserved by the specifications
    (`MContainerInv.lean`). The files above and below
    this one in the list are earlier prototypes with their own
    specifications; [KERNEL.md](KERNEL.md) says which is which.
  - **Page ownership** (`KernOwner.lean`): the allocation table records who
    owns each page. `palloc` tags the page, `pfree` frees it only for its
    owner, and `container_free` lowers the usage only if the page was the
    container's. No owner changes another owner's pages (`ostep_other`), so a
    page table keeps its invariant whatever containers allocate and free
    (`pt_osteps`).

**Not done yet**

- **Regions, rest**: the multicore region proofs are for one client shape
  (increment `nc` cells). There is no client refinement for every region
  client, and no linking framework (per-CPU guarantees composed) for regions.
- **Client refinement through calls, for the other locks**: proved for the
  ticket lock. Lock-array and MCS clients still link by inlining.
- **Owner bounds for other clients**: the generic fairness theorem has one
  instance, the ticket client.
- **Thread layer, rest**: no scheduler data structures (ready and sleep
  queues, context switch), and no thread liveness.
- **Thread-safe CompCertX**: not attempted. It needs a verified compiler.
- **Printers, rest**: turning tokens into text is still trusted.
- **The rest of the kernel**: the page allocator, page tables and containers
  are ported. Address-space creation, shared memory, threads and queues, the
  scheduler, IPC, traps and virtualization are not started. The kernel
  guarantees are per CPU, and `PTInv` is not yet shown to hold across other
  CPUs' operations on the allocation table.
  See [KERNEL.md](KERNEL.md).

MCS note: Kim et al. also fold the node writes into `SWAP_TAIL` (their Fig. 1,
lines 5–7), and their `H_CalLock` counter also counts only memory events, so
both match the paper.

## Where to read more

- [KERNEL.md](KERNEL.md): the kernel port, module by module.
- [SCOPING.md](SCOPING.md): the plan, and a table of every file with what it
  proves.
- [COMPARISON.md](COMPARISON.md): a row-by-row comparison with CertiKOS, and
  benchmark results.
- [Bench/RESULTS.md](Bench/RESULTS.md): lock benchmarks (C and Python).

## Build

Lean 4.35.0 (see `lean-toolchain`):

```bash
lake build
```

On the Apple Silicon development machine, the elan toolchains are x86_64
builds, so an arm64 Lean is unpacked into `.tools/` (git-ignored):

```bash
PATH="$PWD/.tools/lean-4.35.0-darwin_aarch64/bin:$PATH" lake build
```

## License

Non-commercial use only (education, research, evaluation). See
[LICENSE](LICENSE). The terms are adapted from the Yale University
Non-Commercial License Agreement that CertiKOS is distributed under.
This repository contains no CertiKOS source code.
