# Ticket lock: CertiKOS vs. this Lean prototype, piece by piece

**What we compared against.** The concurrent CertiKOS sources (the mC2 kernel and the CCAL `ticketlog` example) are distributed on request only. The public `npe9/certikos` mirror is the sequential PLDI'16 security artifact and has no locks. The artifact page's coqdoc for `mcertikos.ticketlog.*` was not captured by the Internet Archive. So the reference below is what the papers state:

- **[OSDI16]** Gu et al., *CertiKOS: An Extensible Architecture for Building Certified Concurrent OS Kernels*: Fig. 7, Invariant 1, Lemma 6, §6.
- **[PLDI18]** Gu et al., *Certified Concurrent Abstraction Layers*: Fig. 3, Fig. 5, §2, §3.
- **[CACM19]** Gu et al., *Building Certified Concurrent OS Kernels*.

Each row says where the item is in CertiKOS, where it is here, and whether they match. "Match" means the same structure and the same proof obligation, at prototype scale.

| # | CertiKOS | Here | Status |
|---|---|---|---|
| 1 | **Memory model.** The multiprocessor machine `Mx86` treats shared primitives as sequentially consistent ([PLDI18] §1: "assume strong sequential consistency for shared primitives"). | A global event log; every primitive is one atomic event (`TicketLock.lean`, `prims`). | **Match.** Same assumption. Natively on arm64 this needs acquire/release atomics; see benchmark 1. |
| 2 | **Lock data.** `typedef struct { volatile uint ticket; volatile uint now; } ticket_lock; ticket_lock L[NUM_LOCK];` ([OSDI16] Fig. 7). | Single lock: `TicketLock.lean`. **Lock array**: `LockArray.lean`. Events carry the lock index; each lock runs the single-lock protocol on its projection (`projL`, `areplay_proj`), with per-lock mutual exclusion (`amutex`). | **Match.** |
| 3 | **L0 primitives.** `FAI_t`, `get_n`, `inc_n`, plus the no-op `hold` ([PLDI18] Fig. 3); mC2 uses `pull(i)`/`push(i)` for the protected memory ([OSDI16] Fig. 7). | `Prim.faiTicket`, `getNow`, `incNow`, `hold`; indexed versions plus `pull(i)`/`push(i, v)` in `LockArrayCPU.lean` (`aprims`). Ownership: only lock `i`'s holder may pull/push block `i` (`astep`). | **Match.** Blocks are single 32-bit values, not memory regions. |
| 4 | **Events and global log.** Each shared-primitive call is an event `i.FAI_t`, … consed onto the log ([PLDI18] §2). | `Event ⟨cpu, kind⟩` (one lock); `AEvent ⟨cpu, lock, kind⟩` with `pull`/`push v` (lock array). One global log, newest first. | **Match.** MCS events can carry bound numbers (`MCSBound.lean`, row 18). |
| 5 | **Environment context.** Strategies `φ_j` of the other participants plus the scheduler `φ_hs`, each a deterministic partial function of the log. The machine queries `E` before each move ([PLDI18] §2). | `EnvCtx.query : CPU → Log → List Event`, with `noSelf`. `pull` queries before each primitive. | **Match** in substance. CCAL models the scheduler as its own strategy; here it is folded into `query`. |
| 6 | **Switch points.** "exactly one switch point before each atomic operation" ([OSDI16] §3.5). | Every primitive pulls first. The executable model (`Bench/Sim.lean`) switches CPUs exactly there. | **Match.** |
| 7 | **`acq` code.** `uint my_t = FAI_t(); while (get_n() != my_t) {}; hold();` ([PLDI18] Fig. 3). | `acquireCode`: `t = FAI_t(); n = get_n(); while (n != t) n = get_n(); hold();` | **Match.** Clight has no calls inside expressions, so the call is hoisted into `n`, as CompCert's SimplExpr does. Same event trace. |
| 8 | **`rel` code.** `inc_n();` (mC2: `push(i); L[i].now++;`). | `releaseCode`: `inc_n();` | **Match** (`push` missing, see row 3). |
| 9 | **32-bit wraparound.** CertiKOS's first version spun on `now < t`, which breaks when `ticket` overflows. Verification found it; the fix is `!=` ([OSDI16] §6, [CACM19]). | `!=` loop. Exactness is *proved*: `Inv.count` bounds outstanding tickets by `NCPU` (`Inv.outstanding_le`, `loopInv_gap`, `ofNat_eq_of_close`). | **Match**, with the reason made explicit. |
| 10 | **Low-level spec `φ'_acq[i]`** and termination-sensitive simulation `[[acq]]_{L0[i]} ≤_id φ'_acq[i]` ([PLDI18] §2). | `acquireSpec` (fuel-based, as in the MCS-lock paper) and forward simulation `acquire_sim`. Determinism gives no divergence (`acquire_terminates`). | **Match.** |
| 11 | **Rely.** `R_hs`: fair scheduler. `R_j`: other CPUs follow `φ'_acq`/`φ'_rel` and release held locks ([PLDI18] §2). Invariant 1: a holder never re-acquires before releasing, and releases within k steps; at most m events between two moves of one thread ([OSDI16]). | `RelyP`: others keep the log replayable through the protocol state machine. `FairP`: a `CalBound`-style measure that must drop whenever `now` does not move, over reachable states only. | **Match in shape.** Fairness is a measure, not explicit m and k. A concrete scheduler satisfies both (`fairEnv_rely`, `fairEnv_fair`). |
| 12 | **Liveness.** Lemma 6: acquire succeeds within n×m×k iterations ([OSDI16]). | `acquire_live_proto`; explicit bound `acquire_live_bounded`, (NCPU+1)(K+1) for a measure bounded by K; under `fairEnv`, 18 iterations (`acquire_bounded_fair`). | **Match.** |
| 13 | **Mutual exclusion.** "only the thread whose ticket equals `now` can hold the lock; tickets are unique" ([OSDI16]). | `mutex` from the replay invariant `Inv` (`holdNow`, `uniq`). L1 tracks a single holder by construction. | **Match.** |
| 14 | **Relation R₁.** Maps `i.hold ↦ i.acq` and `i.inc_n ↦ i.rel`; other lock events map to nothing ([PLDI18] §2). | `pstep`: `hold` emits `acq`, `incNow` emits `rel`, and `FAI_t`/`get_n` emit nothing; `RelLog`. | **Match.** |
| 15 | **Atomic interface L1.** `φ_acq[i]` queries `E` and emits `i.acq`, then stays in a *critical state* with no queries; `φ_rel[i]` emits `i.rel` ([PLDI18] §2). | `hprims`: `acq` pulls from ε_H and requires the lock to be free; `rel` does not query. `held_no_env` proves no other CPU could have added a lock event anyway. | **Match.** |
| 16 | **`L1'[i] ≤_{R1} L1[i]`, composed into `L0[i] ⊢_{R1} M1 : L1[i]`**, for every client P (contextual refinement) ([PLDI18] (2.2)). | Per call: `acquire_refines_atomic`, `release_refines_atomic`, `critical_section_refines`. **For every client** (`ClientRefine.lean`): any `P : Stmt HPrim` (loops, branches, any number of critical sections) linked with the verified code (`M P` inlines `acquireCode`/`releaseCode`). `client_sim`: every L0 step is matched by P's atomic L1 execution under one table-built ε_H with `HRely`; inside a C block, the block's end is always reachable (no added divergence); `client_final`, non-vacuous under `fairEnv` (`client_final_fair`). | **Match**, with linking by inlining: ClightL has no C-to-C calls, so there are no call frames and clients may not use the lock code's locals `t`/`n`/`_`. |
| 17 | **Parallel layer composition** (rely/guarantee compatibility), multicore linking, thread-safe CompCertX ([PLDI18] §3, Fig. 5). | `Link.lean`: `compose` (per-CPU guarantees under every rely-respecting ε ⇒ every multicore run is explained by the per-CPU layers, with each CPU's ε built from the run and satisfying `RelyP`), `transfer`, and for the ticket lock `client_guar`, `ticket_linked`, `multicore_cs_exclusive`. | **Partial.** Safety links. Liveness links too (`LiveLink.lean`): the per-CPU `acquire_live_bounded` applies to every multicore run, under `EnvFair D` (CCAL's environment assumption), giving at most `(NCPU+1)(D+2)+1` polls per acquire. `SchedFair.lean` derives `EnvFair (17K)` from a `K`-fair scheduler for the ticket-lock client, so `multicore_acquire_fair` assumes only scheduler fairness. No thread-local layer, no CompCertX. |
| 18 | **MCS lock** with the same interface ([OSDI16], [Kim et al. 2017]). | `MCSProtocol.lean`, `MCSLock.lean`: MCS events on the shared log, the queue as ghost positions, `mutexM`, R₁ onto the same atomic `acq`/`rel` (`mreplay_hreplay`), per-CPU C code with guarantees, liveness under `FairB`/`FairN`, and `acquireM_refines_atomic`/`releaseM_refines_atomic`. | **Partial.** The two node writes before `SWAP` are folded into the `swap` event; bound numbers in events at the log level (`MCSBound.lean`: `swap b`, the `H_CalLock` layer with R₁, `crit_bound`, and the waiting measure `M_i` with `wait_bound`), and at the C level (`MCSBoundC.lean`: `acquire(bound)` passes the bound to `swap`; runs erase step for step to the unbounded MCS machine, so termination carries over; the finished log records the C argument); no proof yet that the client's own events keep the bounded log valid; a concrete fair scheduler (`MCSFair.lean`) shows the liveness and refinement theorems are not vacuous; multicore linking for safety (`LinkM.lean`, `MCSLink.lean`); multicore liveness under any `K`-fair scheduler, fewer than `K * (41T + 1)` steps (`MCSLive.lean`). |
| 19 | **Benchmark.** One lock, empty critical section, 10,000 consecutive acquire/release pairs; ticket lock 34 cycles on one core (i7-2600S, 2.8 GHz, turbo off, so about 12 ns), efficiency falling with cores ([OSDI16] §6, Fig. 11). | `bench/`, same method in user space on arm64 (Apple M2 Pro). Results in `bench/RESULTS.md`. | Comparable method; different hardware, and user space rather than bare metal. |

## Changes made to match CertiKOS (this round)

- **`hold` added as the linearization point** (rows 3, 7, 14). Before, the successful `get_n` emitted `acq`. Now `get_n` is a pure read, and `hold` emits `acq`, which is CCAL's R₁.
- **L1 `rel` runs in the critical state** (row 15). It no longer queries ε_H. `held_no_env` justifies this: with the lock held, the only valid high-level move is our own `rel`.
- **Explicit liveness bound** (row 12): `loop_live_bounded`, `acquire_live_bounded`, `acquire_bounded_fair`.

## Still different, in order of importance

1. **Contextual refinement links by inlining** (row 16): ClightL still has no C-to-C calls or modules, so `M P` inlines the lock code.
2. **Multicore linking is partial** (row 17): deriving `EnvFair` is specific to the ticket-lock client; no thread-local layer.
3. **Lock-array blocks are single values** (rows 2 and 3), not memory regions; the lock array has a concrete fair scheduler (`LockArrayFair.lean`) contextual refinement for every client (`ArrayClientRefine.lean`), and multicore linking for safety (`LinkA.lean`, `ArrayLinkClient.lean`); lost-update freedom (`NoLostUpdate.lean`) and fair termination (`ArrayLive.lean`) on the multicore machine.
4. **MCS bounds** (row 18): in the events (`MCSBound.lean`) and as a C argument (`MCSBoundC.lean`). Still missing: a per-CPU bounded guarantee (the client keeps `bcal` defined) and a bounded multicore machine.

## Performance (full numbers in `bench/RESULTS.md`; rerun with `python3 bench/run_all.py`)

The test machine is an Apple M2 Pro (arm64), running in user space. CertiKOS measured inside the kernel on an Intel i7-2600S, so compare shapes, not absolute numbers.

**1. Native lock latency.** ns per acquire+release, empty critical section, one lock:

| threads | CertiKOS C (OSDI'16 Fig. 7) | ours: C printed from the verified AST, SC atomics | ours, acquire/release atomics | Python threads |
|---|---|---|---|---|
| 1 | 3.96 | 8.03 | 4.51 | 148 |
| 2 | 47.5 | 53.5 | 48.1 | ~23,000 |
| 4 | 139 | 145 | 140 | ~39,000 |
| 8 | 202 | 206 | 201 | ~25,000 |

- **Uncontended:** with SC primitives, our code is about 2× slower than CertiKOS's. The algorithm is the same. The gap comes almost entirely from `inc_n`, which compiles to a second atomic read-modify-write (`ldaddal` on `now`) per transaction. CertiKOS uses a plain volatile `now++`, which is sound on x86-TSO. Ablation (1 thread, ns; same harness):

  | variant | `FAI_t` | `get_n` | `inc_n` | ns |
  |---|---|---|---|---|
  | ours-c (all SC) | `ldaddal` | `ldar` | `ldaddal` | 7.7 |
  | `inc_n` = load + SC store | `ldaddal` | `ldar` | `ldr`+`stlr` | 4.7 |
  | acquire/release | `ldadd` | `ldapr` | `ldr`+`stlr` | 4.3 |
  | CertiKOS ordering | `ldaddal` | `ldr` | `ldr`+`str` | 3.7 |
  | certikos-c | | | | 3.7 |

  - Dropping the second atomic RMW saves about 3 ns. A plain load plus an SC store gives the same atomic `inc_n` event because only the holder writes `now` (`mutex`). That relies on the protocol, though, not on the L0 assumption alone.
  - The last ~1 ns is the release store (`stlr` vs `str`). That ordering is exactly what CertiKOS's plain store lacks on arm64; on x86 every store is a release, so it would cost nothing there.
  - `ldar` vs a plain load in the spin read costs almost nothing.
  - With acquire/release primitives our code runs at 4.5 ns, within 15% of CertiKOS. That variant is justified informally by `mutex` (only the holder writes `now`), not by the SC proof.
- **Contended:** all three C versions are within a few percent of each other. Cache-line transfer of the lock dominates, and the falling efficiency matches the ticket-lock curve in [OSDI16] Fig. 11.
- **Correctness:** every native run passed the counter check, including the CertiKOS volatile version on arm64. Passing a test does not show it is correct on a weakly ordered CPU.
- **Python:** about 35× slower uncontended. Under contention it costs 20–40 µs per hand-off, because a spinning waiter holds the GIL until the interpreter forces a switch. The algorithm is correct (counter exact) but a ticket lock is the wrong tool in CPython.

**2. Executable models** (same semantics, same scheduler):

- The Lean model (the verified ASTs run by `ClightL.step`, compiled) is 1.5–1.8× faster than the Python model.
- **The two produce identical logs in every configuration** (length and FNV-1a hash), and every log replays through the verified protocol (`replay`). This is the differential test proposed in SCOPING.md §7 option D, run for real.
- Cost per event grows linearly with log length in both models, because `ticket`/`now` are replay functions that rescan the log, exactly as in the spec. The CertiKOS Coq model could not be run (sources not public).
