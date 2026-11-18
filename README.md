# lean-certikos

A prototype of CertiKOS-style verification in Lean 4: certified concurrent
layers (CCAL) for spinlocks, with safety **and liveness**, over a small
Clight-like language (ClightL). One AST is emitted to both C and Python, and
the Python translation is proved equivalent to the C.

41 Lean files, about 17,000 lines. No `sorry`. The main theorems depend only on
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
- **Lock arrays protecting regions** (`LockRegion.lean`): each lock protects a
  block of cells. Per-lock mutual exclusion, R₁, and the data invariant: an
  acquirer sees exactly the region the last holder released.
- **C-to-C calls and modules** (`ClightCall.lean`): functions with call frames,
  modules, and linking. A callee runs in a fresh frame. `acquire(lk)` and
  `release(lk, v)` called as real functions refine the atomic `acq`/`rel`.
- **A verified C printer** (`PrintC.lean`): parsing the printed tokens gives
  back the AST. `Bench/EmitC.lean` uses it.

**Not done yet**

- **Calls, rest**: callees are leaf functions (they call primitives, not other
  functions). Whole-client contextual refinement (`ClientRefine.lean`) still
  links by inlining. The per-call refinement through real frames
  (`ClightCall.lean`) is its building block.
- **Regions, rest**: the region lock array has the protocol, atomic layer and C
  primitives. The per-CPU C refinement, multicore linking and no-lost-updates
  proofs exist only for single-value lock arrays.
- **Multicore linking, rest**: environment fairness is derived for the ticket
  client only. There is no CPU-local → thread-local layer and no thread-safe
  CompCertX. These are research-scale.
- **Printers, rest**: joining tokens into C text is trusted, and the Python
  printer (`Bench/EmitPy.lean`) is still unverified.
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
