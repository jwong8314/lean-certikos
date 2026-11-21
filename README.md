# lean-certikos

A prototype of CertiKOS-style verification in Lean 4: certified concurrent
layers (CCAL) for spinlocks, with safety **and liveness**, over a small
Clight-like language (ClightL). One AST is emitted to both C and Python, and
the Python translation is proved equivalent to the C.

136 Lean files, about 55,600 lines, and a Coq development of the
virtualization layers in `coq/` (about 3,700 lines). No `sorry`, no `Admitted`. The main theorems depend only on
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Current direction (2026-11-20): mC2, the concurrent CertiKOS kernel**, is
being re-implemented from its papers (OSDI'16, PLDI'18), since no source was
released. The design, what the papers specify, what already exists here, and
the stage order are in [MC2.md](MC2.md). The mCertiKOS port below supplies
the layers mC2 reuses; the kernel-lock files (`TLock`, `THLock`, `THLock2`,
`THRunVM`) are the papers' big-kernel-lock variant `mC2-bl`.

## Status (2026-11-19)

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

- **Kernel, memory management and thread data, ported from the mCertiKOS sources**
  ([KERNEL.md](KERNEL.md) tracks the port layer by layer). The abstract
  state, the specifications and the C code are transcribed from the public
  mCertiKOS sources, and the C code is proved to refine the specifications.
  - **Layers** (`Layer.lean`): a primitive's interface is a triple with a
    write footprint. Each layer is verified against the triples of the layer
    below, never its code. `Triple.lift` is the frame rule and
    `Triple.locked` connects a triple to `acquire; s; release`.
  - **Invariants along the log** (`LogInv.lean`, `MMInv.lean`): the
    invariant is a property of the shared log. Boot establishes it and
    `pt_resv` and `offer_shared_mem` keep it, against a rely on the other
    CPUs that is assumed, not yet derived.
  - **Allocation table** (`MALOp.lean`): `palloc`, `pfree`, and the table
    accessors.
  - **Containers** (`MContainer.lean`, `MContainerInv.lean`):
    `container_alloc`, `container_split`, the getters, and the invariants
    `Container_valid` and `quota_bounded_AT`, proved preserved.
  - **Page tables** (`MPTIntro.lean`, `MPTOp.lean`, `MPTCommon.lean`,
    `MPTKern.lean`, `MPTNew.lean`): the eight accessors of the page-table
    pool, the operations by virtual address, `pt_alloc_pde`, `pt_free_pde`,
    `pt_insert` and `pt_rmv` with reference counts, `pt_new` and `pt_resv`.
  - **Boot** (`MALInit.lean`, `MContainerInit.lean`, and the C code in
    `MALInitC.lean`, `MContainerInitC.lean`): `mem_init` and `container_init`
    refine their specifications, which establish the invariants that the
    other theorems assume. `idpde_init`, `pt_init_comm` and `pt_init_kern`
    (`MPTInit.lean`) fill the identity page table, the kernel part of every
    page table, and the kernel's own page table.
  - **Shared memory** (`MPTResv2.lean`, `MShareIntro.lean`, `MShareOp.lean`,
    `MShare.lean`): `pt_resv2` maps one page in two address spaces, and
    `offer_shared_mem` and `shared_mem_status` refine their specifications.
  - **Thread data** (`PThreadIntro.lean`, `PQueueIntro.lean`,
    `PQueueInit.lean`, `PCurID.lean`): thread control blocks, thread queues
    and the current thread. `enqueue`, `dequeue` and `queue_rmv` on the
    doubly linked control blocks refine their specifications.
  - **Queues as lists** (`PAbQueue.lean`, `PAbQueueGen.lean`,
    `PAbQueueInv.lean`): the layer where a queue is a list of thread ids.
    Each list operation is matched by the pointer operation, the C code
    refines the list specifications, and the list view's five invariants are
    established by initialisation and kept by every operation.
  - **Machine model, first part, and boot** (`MCPU.lean`, `MInit.lean`,
    `PSchedInit.lean`): `CR3` and the paging bit as two words of the kernel
    region, with mCertiKOS's `set_cr3` and `set_pg`. `pt_init` turns paging
    on, and the whole chain `sharedmem_init`, `thread_init`, `tdqueue_init`,
    `sched_init` refines its specifications, under one layout of the kernel
    region. Boot ends with paging on, every table initialised, thread 0
    running, and (`PSchedBoot.lean`) run under the lock it leaves the
    memory-management and queue invariants on the shared log.
  - **Kernel contexts and the scheduler** (`KMachine.lean`,
    `PKContext.lean`, `PThreadSched.lean`, `PThreadSwitch.lean`,
    `PThreadSpawn.lean`): a kernel context is a suspended ClightL
    computation, and the kernel machine has a step that parks the running
    one and resumes another (mCertiKOS's `cswitch`, which is assembly).
    `thread_spawn`, `thread_wakeup`, `thread_sched`, `thread_yield` and
    `thread_sleep` do what mCertiKOS's specifications say, and keep the
    queue invariants.
  - **Synchronous IPC** (`PIPCIntro.lean`, `FlatMem.lean`, `PIPC.lean`,
    `PIPCRecv.lean`, `PProcInit.lean`): each thread has a channel. A sender
    publishes its buffer there and sleeps; the receiver copies the buffer
    between the two address spaces, leaves the count, and wakes the sender.
    `syncsendto_chan_pre`, `syncsendto_chan_post` and `syncreceive_chan`
    refine mCertiKOS's specifications, and so does `proc_init`, which ends
    boot.
  - **Processes, user mode and system calls** (`PUCtxtIntro.lean`,
    `UMachine.lean`, `PProc.lean`, `TTrapArg.lean`, `TTrap.lean`,
    `TDispatch.lean`, `TSysCall.lean`): each process has a user context. The
    machine has a user mode: a trap enters the kernel with the user's
    registers, and a kernel computation that finishes returns to user mode.
    `proc_create`, the system-call handlers and the dispatcher refine
    mCertiKOS's specifications. Its three top-level primitives are proved as
    whole passages through the kernel: a system call, a page fault, and a
    yield that ends in user mode in another process.
  - **Security** (`ObsEq.lean`, `Integrity.lean`, `Confidentiality.lean`,
    `ConfidentialityPF.lean`, `Security.lean`): mCertiKOS's observation
    function (what one process can see of the kernel's state), and the three
    unwinding conditions of its noninterference proof, for one passage
    through the kernel. Integrity: a process that is not running observes
    nothing of another's system call, page fault or yield. Confidentiality:
    after its own passage, what a process observes, and the registers it
    gets back, depend only on what it observed before; this includes the
    page fault, where the physical page it gets is hidden. And a parked
    process that is resumed observes the same whatever happened meanwhile.
    From these, noninterference (`SecurityBigstep.lean`): two executions of
    one program, from states it cannot tell apart, stay in step for ever,
    whatever the other processes do. A program is modelled as a function from
    what the process can see to its next trap.
  - **Virtualization** (`coq/EPT.v`, `coq/VMCS.v`, `coq/VMX.v`, then
    `VEPT.lean`, `VVMCS.lean`, `VVMX.lean`, `GMachine.lean`): mCertiKOS's
    specifications of the extended page table, the VMCS and the `vmx`
    structure, with code written for them (the public sources do not have
    it) and refinement proofs. The VMCS is a block of the kernel region,
    read and written by `vmread` and `vmwrite`. Entering the guest loads its
    registers and saves the host's; leaving it saves the guest's and puts the
    host's back (`vm_roundtrip`). ClightL gained `&`, `|` and `<<` for this,
    and the Python translation stays equivalent. The hypercalls (`coq/Trap.v`,
    then `THyp.lean`, `THyp2.lean`) run on a top state that adds the consoles
    and the virtual machine to the process layers (`TTop.lean`), and the
    dispatcher (`TDispatchH.lean`) handles them with `SYS_spawn`,
    `SYS_get_quota`, `SYS_share` (`TShare.lean`) and `SYS_print`; every call
    but `SYS_share` keeps the other processes' observations (`TSecH.lean`).
  - **Steps and data abstraction** (`LayerStep.lean`): running a function's
    code call by call on the abstract state, and carrying a layer's triples
    to a layer whose state is a view of it.
  - **Page ownership** (`PTInitGen.lean`): mCertiKOS's owner lists. The
    count-based specifications refine the ones that say which page-table
    entries own each page.
  - **Lock rules** (`KernPAlloc.lean`, `KernFrame.lean`): `cs_guarantee`,
    `Runs`, and the frame lemmas for regions.

**Not done yet**

- **Regions, rest**: the multicore region proofs are for one client shape
  (increment `nc` cells). There is no client refinement for every region
  client, and no linking framework (per-CPU guarantees composed) for regions.
- **Client refinement through calls, for the other locks**: proved for the
  ticket lock. Lock-array and MCS clients still link by inlining.
- **Owner bounds for other clients**: the generic fairness theorem has one
  instance, the ticket client.
- **Thread layer, rest**: the scheduler is ported from mCertiKOS, with
  kernel contexts as suspended computations. Its theorems are per call.
  There is no reasoning about one thread with the others as its
  environment, no proof that a parked thread runs again, and no thread
  liveness.
- **Thread-safe CompCertX**: not attempted. It needs a verified compiler.
- **Printers, rest**: turning tokens into text is still trusted.
- **The rest of the kernel**: the page allocator, page tables, containers,
  boot (up to the kernel's page table), shared memory, thread control
  blocks, thread queues (linked, then as lists) and the current thread are
  ported, boot is complete, and so are the scheduler, synchronous IPC,
  processes and the system-call path up to mCertiKOS's top layer. The
  machine model has `CR3`, the paging bit, kernel contexts and user mode, one
  copy rather than one per CPU. The entry points take the kernel lock at the
  boundary (`acquire; entry; release`, `TLock.lean`), and the invariants they
  assume are carried from one trap to the next on the shared log (`KInv`,
  `TInv.lean`; `Good`, `TLock.lean`). The full dispatcher (hypercalls,
  `SYS_share`, `SYS_print`, `SYS_recv`, `SYS_hvm_mmap`) is an entry point too,
  with the lock and the invariant (`THEntry.lean`, `THInv.lean`,
  `THLock.lean`), and so are the page fault and the yield on the full state
  (`THLock2.lean`) and `SYS_hvm_run_vm` with its VM exit (`THRunVM.lean`: the
  guest runs with the lock held, since the processor's mode is per-CPU state
  of which the machine has one copy). Security is
  proved at the top layer's specifications, with user programs as functions
  of what they can see; user-mode instructions are not modelled, and the result
  is not carried down to the machine. The security invariants are shown
  preserved by every passage through the kernel, so noninterference assumes
  them only of the first states (`TSecInv.lean`). Virtualization: mCertiKOS publishes only the
  specifications of its VMX, VMCS and EPT objects, so the code that
  implements them is written here from those specifications and the C
  comments, first in Coq (`coq/`), then in Lean (`VEPT.lean`, `VVMCS.lean`,
  `VVMX.lean`), and proved to refine them; the machine has a guest mode
  (`GMachine.lean`); the hypercalls and the dispatcher are verified on a top
  state with the consoles and the virtual machine, and so are `vmx_init`
  (`coq/Init.v`, `VInit.lean`), the EPT's upper tables in memory
  (`coq/EPT4.v`, `VEPT4.lean`), `SYS_hvm_mmap` (`THyp3.lean`), and
  `SYS_hvm_run_vm` with the VM exit (`TRunVM.lean`); a visit to the guest
  keeps the other processes' observations (`TSecVM.lean`). Not done: what the
  guest itself does is not modelled, and there is one virtual machine shared
  by all processes (as in mCertiKOS). The top state's relation includes the
  EPT's upper tables, and its dispatcher covers every number of mCertiKOS's
  C dispatcher (including `SYS_recv`) plus `SYS_share` and `SYS_print`. The kernel
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
