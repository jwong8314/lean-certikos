# mC2 in Lean: the concurrent kernel, from the papers

mC2 is the concurrent CertiKOS kernel: multicore, fine-grained locks, and
threads that yield, sleep and wake up. The authors released no source for it.
The artifact page that offered `ccal.tar.gz` is gone, and the CertiKOS
organisation on GitHub has no mC2 repository. So this is a **re-implementation
from the papers**, not a port:

* [OSDI16] Gu et al., *CertiKOS: An Extensible Architecture for Building
  Certified Concurrent OS Kernels*, OSDI 2016: the kernel's architecture
  (Fig. 3), the machine refinement chain (§3), and the kernel objects (§4).
* [PLDI18] Gu et al., *Certified Concurrent Abstraction Layers*, PLDI 2018:
  the layer calculus, `push`/`pull`, the shared queues (§4.2), the
  scheduling layers and thread-local layers (§5), and the queuing lock (§5.4).

Where the papers give code, we write that code: the ticket lock (OSDI16
Fig. 7), `palloc` (Fig. 8), the `FIFOBBQ` `remove` (Fig. 10) and the queuing
lock (PLDI18 Fig. 11). Elsewhere the papers give only the design, and the code
is ours, labelled as such. mC2 was built from the sequential mCertiKOS
([OSDI16] §5: layers without synchronisation carry over unchanged), so the
mCertiKOS port in this repository is the source for those layers.

## What the papers say mC2 is

**Machine** ([OSDI16] §3). The bottom machine `x86mc` lets the hardware pick
any CPU at each instruction. A chain of refinements leads to a CPU-local
machine:

* `hs`: the hardware scheduler `ε_hs` decides the interleaving, recorded as
  switch events in the log.
* `lcm`: each CPU keeps a local copy of each shared block, which it gets with
  `pull` and returns with `push`. Touching a block that is not valid locally
  goes wrong, so programs that are safe here are free of data races.
* `pt(A)`: the CPUs outside the active set `A` become an environment
  context, a function from the log to the events the others add. Partial
  machines with disjoint `A`, `B` compose.
* `loc(i)`: switch points only before atomic and `push`/`pull` operations.

**Atomic objects.** An atomic object is a set of primitives, an initial state,
and a log of events, one per call. Its state at any point is the replay of the
log. Each shared object is protected by its own lock, and the module that
implements it is proved to refine an interface in which the whole
`acquire; body; release` is one event (`c.palloc`, `c.enQ i e`, …). Locks of a
lower layer are not available above it, so locks are always taken in layer
order and there are no deadlocks.

**Shared and per-CPU** ([OSDI16] Fig. 3 and §4, [PLDI18] Fig. 1 and §5.1).

| Object | Kind | Protection |
|---|---|---|
| spinlocks (ticket, MCS) | shared | atomic instructions |
| page allocation table `AT`, containers `cn` (quotas) | shared | `lock_AT` |
| page maps, shared-memory owner sets | shared | locks |
| sleeping queues `SleepQs` | shared | one lock per queue |
| pending queue `PendQ`, one per CPU | shared | one lock per queue |
| ready queue `ReadyQ`, one per CPU | **per-CPU** | none |
| current thread (`CurID`), `PCPU` data | per-CPU | none |
| scheduler, thread management, process management, VM monitor | per-CPU | |
| thread control block, kernel context, kernel stack | per-thread | |

**Scheduling** ([PLDI18] §5.1, [OSDI16] Fig. 9). Every thread belongs to a CPU.

* `yield`: move the first thread of this CPU's `PendQ` to its `ReadyQ`, then
  switch to the next ready thread.
* `sleep(i, lk)`: put the running thread on sleeping queue `i`, release
  `lk`, and switch to the next ready thread.
* `wakeup(i)`: take a thread from sleeping queue `i`. If it belongs to this
  CPU, put it on the `ReadyQ`; otherwise put it on its CPU's `PendQ`.
* `cswitch`, in assembly, saves `ra, ebp, ebx, esi, edi, esp` and loads
  another thread's.
* Events `c.yield`, `c.sleep(i, lk)`, `c.wakeup(i)`; the replay function
  `R_sched` gives the running thread.

**Thread layers** ([PLDI18] §5.2–5.3). A software scheduler `ε_ss` joins the
environment. It answers yield and sleep events with the next thread, and
reschedules a sleeping thread only after a wakeup.

* `L[c][T_a]` focuses on a set of threads of CPU `c`, and the other threads
  join the environment. Such layers compose for disjoint sets.
* Multithreaded linking (Thm 5.1) is `L_btd[c] ≤ L_htd[c][T_c]`.
* In the thread-local layer `L[c][t]`, `yield` and `sleep` always come back
  to `t`, so they act as no-ops on the kernel context and update only the
  log. This needs the software scheduler to be fair.

**Synchronisation and services.**

* Queuing lock ([PLDI18] Fig. 11).
* Starvation-free condition variables: FIFO condition queues, after
  Anderson–Dahlin.
* `FIFOBBQ` with the authors' fix ([OSDI16] Fig. 10).
* Synchronous IPC over channels.
* Shared-memory IPC (`Lib Mem`).
* Hardware virtualization, one guest per CPU.
* A few drivers: interrupt controllers, serial, keyboard.
* The trap handler, which is the top layer and the kernel's specification,
  instantiated with one thread on one CPU.

**Theorems.**

* `∀P, [[K & P]]_x86mc ⊑ [[P]]_mC2`: contextual refinement of the whole
  kernel.
* Starvation freedom of the ticket and MCS locks, under a fair hardware
  scheduler and locks held for bounded times (Invariant 1, Lemma 6).
* Every system call returns.
* No data races.

**`mC2-bl`.** [OSDI16] §5 compares mC2 with a big-kernel-lock version: one
lock acquired and released at the top layer, with the fine-grained locks
emptied. The files `TLock`, `THLock`, `THLock2` and `THRunVM` are this
variant, built on the mCertiKOS port.

## What this repository already has

| mC2 piece | Here |
|---|---|
| machine with logs and environment contexts, `push`/`pull` | `ClightL`, `LockArray`, `LockRegion`, `LockRegionCPU` (CPU-local, `loc`-like) |
| partial machines compose (Lemma 3–4) | `Link`, `LinkA`, `LinkM`, `LiveLink`, `ArrayLinkClient` |
| ticket lock, Invariant 1, Lemma 6 | `TicketProtocol`, `TicketLock`, `AtomicLayer`, `TicketLive` |
| MCS lock | `MCSProtocol`, `MCSLock`, `MCSLive`, `MCSBound*` |
| lock-protected objects: acquire, body, release | `LockArrayAtomic`, `KernPAlloc` (`palloc` under a lock), `Layer` (`Triple.locked`) |
| thread layer (first step) | `ThreadLayer` |
| sequential layers mC2 reuses | the mCertiKOS port: `MALOp`, `MContainer`, `MPT*`, `MShare*`, `PAbQueue`, `PThread*`, `PIPC*`, `PProc`, `TTrap*`, `TSysCall`, `VVMX`, … |

The pieces the machine does not yet have:

* per-CPU private memory for the code (ready queue, current thread, `CR3`,
  mode flags); `MC2Sched` keeps them abstract;
* the thread layers with a software scheduler;
* the synchronisation libraries.

## Stages

Bottom to top, as the papers build it:

1. **Atomic objects.** A generic construction: an object with a state, an
   initial state and operations; its high-level log of `c.op(args)` events
   and replay; and the refinement from `acquire(lk); body; release(lk)` to
   one event, given a body that implements the operation on the region. The
   first instance is mC2's `palloc(tid)` (Fig. 8), with the container quota
   check, over `AT` and `cn` under `lock_AT`.
2. **Shared queues** ([PLDI18] §4.2): `enQ`, `deQ` on doubly linked lists
   under one lock each. The body is `deQ_t` on the local copy, reusing
   `PAbQueue`; the events are `c.enQ i e` and `c.deQ i`.
3. **Per-CPU state and the scheduling layer `L_btd[c]`**: per-CPU `ReadyQ`
   and current thread, a `PendQ` per CPU, `SleepQs`; `yield`, `sleep(i, lk)`,
   `wakeup(i)`, `cswitch`; the events and `R_sched`.
4. **Thread layers**: the software scheduler `ε_ss` and its fairness,
   `L[c][T_a]`, multithreaded linking, the thread-local layer `L[c][t]`.
5. **Synchronisation**: the queuing lock (Fig. 11) and its starvation
   freedom, condition variables, `FIFOBBQ` (Fig. 10).
6. **Memory**: page maps and shared memory as atomic objects (the mCertiKOS
   bodies under locks).
7. **Threads, processes, IPC, virtualization**: TCBs, spawning, kernel
   stacks; process management; synchronous IPC on the synchronisation layer;
   one VMX state per CPU.
8. **The trap handler and the whole kernel**: the system calls on the
   thread-local layer; linking threads, then CPUs; liveness (every system
   call returns).

## Progress

| Stage | Status | Files |
|---|---|---|
| 1. Atomic objects | **done**: `atomic_call` (any `acquire; body; release` that implements an operation is one event of the object, with the region the replay of the history); the page allocator `palloc(tid)` of Fig. 8, with the quota check, as an atomic object (`palloc_atomic`) | `MC2Atomic.lean`, `MC2PAlloc.lean` |
| 2. Shared queues | **done**: each queue one atomic object on its own lock's region (head, tail, and the links of the threads on it); mCertiKOS's `enqueue`/`dequeue` implement `enQ t`/`deQ` (`enQ_impl`, `deQ_impl`), so each locked call is one event (`enQ_atomic`, `deQ_atomic`). Enqueuing a thread already on the queue leaves the object undefined; stage 3 must rule it out | `MC2Queue.lean` |
| 3. Scheduling layer | **partly done**: the layer as a machine over the shared queues of stage 2. Each CPU's `yield`, `sleep(i)`, `wakeup(i)` is a few steps, each one queue event or private, interleaved freely across CPUs; a queue's state is the replay of its events and a dequeue's result is the object's `result`, as `deQ_atomic` guarantees. Invariant: every thread is in exactly one place (running on its CPU, on its CPU's ready or pending queue, on a sleeping queue, or between the halves of a `wakeup`), for every interleaving (`wf_replay`). So no queue is enqueued a thread already on it (`queues_defined`, stage 2's obligation), and `R_sched` gives a thread that runs on its own CPU only (`rsched_owner`). **Not yet**: the code of the ready queue on per-CPU memory and of `cswitch`. It needs a lemma the lock framework lacks: two locked calls on different locks in sequence (`wakeup` takes a sleeping queue's lock, then a pending queue's), with the second lock's state, fairness and invariant carried across the first call | `MC2Sched.lean` |
| 4. Thread layers | **partly done**: each CPU's registers and each thread's saved context, with `cswitch` saving at `yield`/`sleep` and loading at `pick`. Every scheduler step on any CPU leaves every thread's context unchanged (`sched_noop`), so after any interleaving a thread's context is its own steps applied to its initial context (`ctx_local`): the thread-local layer, where `yield` and `sleep` are no-ops on the context. The software scheduler is FIFO and fair: a ready thread keeps its place, moves up at each `pick` of its CPU, and has run by the `(k+1)`-th `pick`, `k` the threads ahead of it (`ready_runs'`). **Not yet**: `L[c][T_a]` for sets of threads and multithreaded linking as a refinement between layers; that each CPU keeps picking needs every running thread to yield or sleep eventually, an assumption on the threads | `MC2Thread.lean` |
| 5–8 | not started | |

## Unknowns we decide ourselves

* The C code of every module whose code the papers do not show.
* The exact system-call interface of mC2.
* How a thread is assigned to a CPU (we fix it at creation).
* The steps of `yield`, `sleep` and `wakeup`, and what an idle CPU does (no
  running thread; it calls `yield`): `MC2Sched.lean`.
* Where a thread's queue links live: in the region of the queue it is on
  (`MC2Queue.lean`), so each cell has exactly one lock.
* Where `palloc` reads the quota: inside `lock_AT`, not before it as in
  Fig. 8 (`MC2PAlloc.lean` explains why).
* The code of the condition variable: [OSDI16] cites Anderson–Dahlin
  Fig. 5.14, which we do not have. We write FIFO condition queues ourselves.
* The IPC protocol beyond "synchronous, over channels, single copy".

Each of these is recorded in the file that decides it.
