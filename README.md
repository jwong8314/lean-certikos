# lean-certikos

A prototype of CertiKOS-style verification in Lean 4: certified concurrent
layers (CCAL) for spinlocks, with safety **and liveness**, over a small
Clight-like language (ClightL). One AST is emitted to both C and Python, and
the Python translation is proved equivalent to the C.

47 Lean files, about 20,000 lines. No `sorry`. The main theorems depend only on
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

**Not done yet**

- **Regions on the multicore machine**: the region proofs are per CPU. Multicore
  linking, and no lost updates across CPUs, exist only for single-value lock
  arrays.
- **Client refinement through calls, for the other locks**: proved for the
  ticket lock. Lock-array and MCS clients still link by inlining.
- **Owner bounds for other clients**: the generic fairness theorem has one
  instance, the ticket client.
- **Thread layer, rest**: no scheduler data structures (ready and sleep
  queues, context switch), and no thread liveness.
- **Thread-safe CompCertX**: not attempted. It needs a verified compiler.
- **Printers, rest**: turning tokens into text is still trusted.
- **The rest of mC2**: virtualization and the larger OS modules (scheduler,
  memory management, IPC, VMX). Each is a project of its own.

MCS note: Kim et al. also fold the node writes into `SWAP_TAIL` (their Fig. 1,
lines 5–7), and their `H_CalLock` counter also counts only memory events, so
both match the paper.

## Where to read more

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
