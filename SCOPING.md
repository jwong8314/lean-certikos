# Scoping: the full CertiKOS (mC2) result in Lean 4, without Clift

Status: scoping draft, revised 2026-11-06. A prototype now exists in `CertiKOS/`; §0a lists what it proves.

Revision note: earlier drafts built on **Clift** (github.com/eisbaw/Clift). This version **drops Clift as the foundation** (§3) and replaces it with a purpose-built Clight-style semantics designed around CertiKOS's liveness method (§4). The CertiKOS method described in §2 is now checked against the MCS-lock paper (Kim, Sjöberg, Gu, Shao, "Safety and Liveness of MCS Lock—Layer by Layer"), not just recalled.

---

## 0. TL;DR

| Question | Answer |
|---|---|
| Keep Clift? | **No.** Clift's C-level core *could* host the CertiKOS method if its code were deterministic. But the parts that make Clift worth using are the wrong shape for termination-sensitive refinement: its monadic lift, its `corres`, and its relational `spec` primitives (§3). It also offers no path to assembly linking or a compiler proof, and the full CertiKOS result needs both. |
| What replaces it? | **"ClightL"**: a small-step, **deterministic-given-ε** Clight-like semantics in Lean with a CompCert-style block memory. Paired with an **LAsm-like assembly semantics**, a **layer framework** that uses CompCert's "forward simulation + determinism ⇒ backward simulation" trick, and a **liveness kit** that copies CertiKOS's bound numbers, fuel-based loop specs, ghost layers and fairness bound (§4). |
| Does this make liveness easy? | Yes, in the same sense it is easy in CertiKOS. Because all nondeterminism lives in ε, per-function proofs are sequential, refinement is termination-sensitive by construction, and starvation freedom reduces to a decreasing measure over log events (§2). |
| What's still hard? | The **multicore → CPU-local → thread-local** machine refinements, the **compiler bridge** (Lean has no CompCertX), and the scale of mC2 (about 6,100 lines of C and 400 lines of asm in ~10 modules, including a hypervisor). |
| Python equivalence? | Unchanged in substance. Compare a deterministic, sequential Python model against the **whole-kernel trap-handler spec**, with ε as an explicit input (§7). |
| Target | **Faithful mC2 (decided 2026-11-06):** 32-bit x86 (IA-32), multicore, including the Intel VT-x hypervisor module. The Coq specs are ported, not reinvented (§1a). |
| Rough size | Full mC2 parity: **roughly 6–12 person-years** for an expert team, dominated by the kernel modules and the compiler bridge. Framework + locks + toy kernel milestone: about 1–1.5 person-years. These are my estimates, not data. |

---

## 0a. Prototype status (updated 2026-11-07)

A first P0 spike is in `CertiKOS/` and builds with Lean 4.35.0. It has no `sorry`, and the only axioms are Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

| File | What it shows |
|---|---|
| `ClightL.lean` | A Clight-style language with 32-bit values and CompCert-style continuations. `step : Config → Option Config` is a function, so the semantics is deterministic by construction. Shared state is reachable only through a primitive table of the layer underneath. |
| `Determinism.lean` | Reaching a final state ⇒ no divergence (`not_diverges_of_star_final`); final states are unique (`final_unique`). This is the "downward simulation suffices" core. |
| `TicketLock.lean` | Event log + ε (with the no-self-events property). One event per atomic primitive. Ticket-lock `acquire` in ClightL. A fuel-based spec. **Forward simulation** (`acquire_sim`) ⇒ **termination of the C code** (`acquire_terminates`). **Liveness under a bounded-fairness rely** (`acquire_live`, `acquire_live_terminates`): no-overtake + a `CalBound`-style counter, with fairness as a *hypothesis*, not an axiom. **Non-vacuity**: a concrete ε satisfies the rely (`demoEnv_rely`, `demo_acquire_terminates`). **Vacuity check**: a forever-spinning `acquire` passes a Clift-style partial refinement (`spin_partial`) and fails the termination-sensitive one (`spin_not_total`). |
| `TicketLock.lean` (cont.) | `release` (`inc_now`) with its simulation (`release_sim`). |
| `TicketProtocol.lean` | **Protocol replay** of the shared log into per-CPU phases (idle/waiting/holding) and a **high-level log** of `acq`/`rel` events. A **global invariant** holds for every replayable log, including `ticket = now + #active CPUs` with `NCPU = 8` (CertiKOS `TOTAL_CPU`). That counting fact is what makes the 32-bit `n != t` test wraparound-safe (`ofNat_eq_of_close`). **Mutual exclusion** (`mutex`). **Linearization** (`acquire_guarantee`, `release_guarantee`): under the rely "others follow the protocol" (`RelyP`), `acquire` from idle ends holding, and its *only* high-level contribution is one `acq c` at the very end (`release`: one `rel c`). **Liveness over reachable states** (`acquire_live_proto`): fairness (`FairP`) only constrains replayable logs in which we wait, and no-overtaking is now *derived* from the invariant instead of assumed. **End to end** (`acquire_correct`): the C code reaches a final state, cannot diverge, and its final log satisfies the guarantee. **Non-vacuity**: `protoEnv` (CPU 1 running the protocol) satisfies `RelyP`, and a concrete run is checked by evaluation (`demo_proto_acquire`, `demo_proto_guarantee`). |
| `AtomicLayer.lean` | **A separate layer L1** whose primitives *are* atomic `acq`/`rel`. It works over a high-level log with its own environment context ε_H (`HEnv`), and its replay tracks a single holder, so mutual exclusion is built into L1. **Refinement relation** `RelLog`: the L0 log replays to the L1 log. **ε_L ↦ ε_H** (`acquire_refines_atomic`, `release_refines_atomic`): for every ε_L satisfying `RelyP` (and `FairP` for acquire), an ε_H is *constructed* that reports only other CPUs' events and keeps the L1 log well formed (`HRely`). Under that ε_H, the one-line L1 call `acq()`/`rel()` succeeds in one step, and its final log is related to the final log of the C code, which cannot diverge. ε_H is built as a finite table from the deterministic low-level run, as in the CCAL proof. **Composition** (`critical_section_refines`): one ε_H serves a whole `acq(); rel()` critical section. Supporting fact: L0 replay and L1 replay agree on who holds the lock (`replay_hreplay`). |
| `FairEnv.lean` | **The fairness hypothesis is satisfiable.** A new invariant, `Fill`, says every ticket in `[now, ticket)` is owned by some CPU, which avoids a pigeonhole argument. `fairEnv` is a FIFO-fair scheduler for the other CPUs: the holder releases, otherwise the owner of ticket `now` acquires. It satisfies `RelyP` (`fairEnv_rely`) and `FairP` (`fairEnv_fair`) for every CPU, every ticket, and every reachable starting log. That gives **unconditional** termination (`acquire_correct_fair`) and atomic refinement (`acquire_refines_fair`) of the C `acquire` under arbitrary contention. A run with three contenders ahead of CPU 0 is checked by evaluation (`demo_contended`). |
| `Bench/Sim.lean`, `Bench/EmitC.lean`, `bench/` | **Executable artifacts and benchmarks.** `sim` runs the verified ASTs on several CPUs through `ClightL.step`, with CertiKOS's one switch point before each atomic operation. `emitc` prints the verified ASTs as C (the C1 trusted-compiler route). `bench/py_model.py` is a Python model of the same semantics; its logs are identical to the Lean model's in every tested configuration. `bench/run_all.py` measures native latency of CertiKOS's C (from OSDI'16 Fig. 7) vs. ours vs. Python threads; results in `bench/RESULTS.md`. |
| `PyL.lean` | **Python side: PyL**, a concurrent Python subset. Python `int`s (`//`/`%` as floor division and floor modulo), per-thread local frames, a shared heap of object attributes `o.f`, `with L:` for one global lock (`atomic`), and at most one heap access per step, matching CPython bytecode atomicity. A thread-pool semantics (`MStep`), with `Faults` and `Race`. |
| `PyCSL.lean` | **Concurrent separation logic for PyL, proved sound.** Assertions own heap fragments; a resource invariant `J` owns the lock-protected heap. Validity is semantic, and every rule is a theorem: assign, load, store, seq, if, while, `with L:` (`rule_atomic`), frame, consequence, exists. `pool_sound`: if each thread satisfies its triple and the initial heap splits as ⋆ Pᵢ ⋆ J, then for executions of every length there are no faults and no races, and at the end the heap splits as ⋆ Qᵢ ⋆ J. |
| `PySpinLock.lean` | **Ownership transfer, as in CertiKOS's `pull`/`push`.** A spin lock built on `with L:`; its invariant owns `d.val` while the lock is free. `spinlock_safe`: N threads, any interleaving, the unlocked `d.val` updates never race. Sanity checks show `Race` is reachable without the lock and that the pool really steps. |
| `ClightToPy.lean` | **One AST, two targets.** `tr` translates ClightL to PyL: values as `v.toNat`, `+`/`-` as `% 2**32` (relies on Python's floor modulo), a primitive call `x = p(args)` as a `with L:` block running a user-supplied Python implementation. The C side is the multicore machine `Bench/Sim.lean` runs (any CPU steps, shared abstract state). Given `PrimOK` (each block, run alone, does what its primitive does on related states), `py_to_c`: every Python pool run, under any interleaving, including threads running while another is midway through a block, is matched by a C machine run; `c_to_py`: the converse; `py_done`: finished Python ⇒ finished C, same locals, related shared state. |
| `TicketPy.lean` | **The ticket lock in Python, proved equivalent to the C.** Python blocks for `FAI_t`/`get_n`/`inc_n`/`hold` over `lk.ticket`/`lk.now`; the heap holds `ticket`/`now` of the log mod 2³². `primOK`, `python_refines_c`, `c_refines_python`, `python_done` for T threads × N iterations. `Bench/EmitPy.lean` prints the translated AST as runnable Python (`Bench/gen/ticket_from_c.py`). |
| `ClightToPyLive.lean` | **Liveness carried from C to Python, generically.** A C-side termination certificate (`LiveCert`: a potential no C step raises, which every step of an *active* CPU lowers; other CPUs' steps keep a CPU active; some CPU is active while any is unfinished) plus loop-free primitive blocks of bounded size (`ImplBound`) gives `fair_bound`: every `K`-fair Python run (each unfinished thread steps in every `K`-step window, so `L` must be fair too) has fewer than `(S0 + 3) * K * (Φ₀ + 1)` steps. The key lemma `rel_stepI` refines `rel_step`: a Python step of thread `i` is `n` C steps of CPU `i`, and if `n = 0` the thread's stutter measure `mu` shrinks. `rel_progress`: no reachable Python state is stuck unless all threads are done. |
| `TicketLive.lean` | **The ticket-lock certificate and the Python liveness theorems.** `At`: the 24 program points of the client loop, tied to the protocol state of the log, each with a weight; the wait loop weighs 16 while `now < tn`. `Cover` (every ticket in `[now, ticket)` is owned) shows the CPU whose ticket is `now` is never spinning, the global form of `FairP`/`loop_live`. `cert`, then `python_fair_terminates` (T ≤ 8 threads × N rounds: fair runs have fewer than `11·K·(T·(25N+4)+1)` steps), `python_no_deadlock`, `python_final` (`lk.ticket == lk.now` at the end). |
| `Link.lean` | **Multicore linking (parallel layer composition).** `compose`: if each CPU meets its per-CPU guarantee `Guar` (under *every* `ε` satisfying `RelyP`, every log it reaches replays), then every run of the shared-log machine is `Linked`: the global log replays, and each CPU's view is a run of its own layer `Star (prims ε c)` under an `ε` built from the run (answering each query with exactly the other CPUs' events since that CPU last moved), and that `ε` satisfies `RelyP`. The rely/guarantee circularity is broken by induction on the run. `transfer`: any per-CPU property proved under an arbitrary rely-respecting `ε` holds of every CPU of every multicore run. Instance: `client_guar` (per-CPU, on `L0[c]` alone), `ticket_linked`, and `multicore_cs_exclusive` (at most one CPU is in its critical section, from the per-CPU `client_cs` plus `mutex`). |
| `LiveLink.lean` | **Multicore linking, liveness half.** `CRun`: a finite run of the shared-log machine. `runEnv r c`: the environment CPU `c` sees in that run. At each of `c`'s calls it answers with the other CPUs' events since `c` last called; at every other log it answers like `eagerEnv` (holder releases, or the next owner takes the lock and releases), so `FairP`, which ranges over all logs, holds there too. `proj`: `c`'s multicore steps are a per-CPU run under `runEnv`. `runEnv_rely` (via `Link.compose`) and `runEnv_fair`: `FairP` with a counter read off the run (1 + steps left before `now` passes what `c` saw), bounded by `D + 1` under `EnvFair D` (whenever `c` polls out of turn, `now` advances within `D` multicore steps: CCAL's environment assumption). `multicore_acquire_bounded`: once `c` starts `acquire`, it issues at most `(NCPU+1)(D+2)+1` `get_n` events before its `hold`. It is the per-CPU `acquire_live_bounded`, unchanged, transported by determinism (`star_det`). |
| `SchedFair.lean` | **`EnvFair` derived from scheduler fairness.** `Fair K`: in every `K`-step window every unfinished CPU moves. `owner_window`: if `now` stayed at `v` for `17K` steps, the owner of ticket `v` (by `Cover`) is never spinning, so each of its steps lowers its weight (`own_step`) and nobody else's raises it (`at_other`). Fairness gives it 17 steps, but while it owns the current ticket its weight stays in a band of width 15 (`at_owner`; the iteration is fixed because it never writes `i`, `own_i`). `fair_envFair`: `EnvFair (17K)`. `multicore_acquire_fair`: under a `K`-fair scheduler, each acquire polls at most `(NCPU+1)(17K+2)+1` times. That is the per-CPU `acquire_live_bounded`, with no assumption left but scheduler fairness. |
| `CountTN.lean` | **The final count.** `left N t`: rounds CPU thread `t` has yet to start, read off its program point and loop counter `i`. `own_left`: a step keeps (own `incTicket` events + `left`) fixed; only `FAI_t` moves `left`, by one. `ci_steps`: in every reachable multicore state each CPU has `cntC i incTicket l + left N cs[i] = N`. `final_ticket`: all CPUs done ⇒ `ticket l = now l = T·N`. `python_count`: all Python threads done ⇒ `lk.ticket` and `lk.now` both hold `T·N mod 2³²`, the check `Bench/EmitPy.lean`'s script runs. |
| `ClientRefine.lean` | **Contextual refinement for every client.** Any client `P : Stmt HPrim` over atomic `acq`/`rel`, linked with the verified C code by inlining (`M`). `client_sim`: each L0 configuration of `M P` is related to P's L1 configuration, or is inside one C `acq`/`rel` whose end is reachable and related to the L1 configuration one atomic step later, or P already went wrong at L1. One ε_H (a table built from the run, `HRely`) serves the whole run. `client_final`: finished L0 ⇒ finished related L1. `client_final_fair`: non-vacuous under `fairEnv`. |
| `LockArray.lean`, `LockArrayCPU.lean`, `LockArrayAtomic.lean` | **Lock arrays with `pull`/`push`** (mC2's `L[NUM_LOCK]`). One global log of lock-indexed events. `areplay_proj`: every lock runs the single-lock protocol on its projection, so all single-lock lemmas apply per lock; `amutex`: per-lock mutual exclusion. Ownership: only the holder may `pull`/`push` a block. `areplay_di`: until the holder pushes, a block holds the value of the last release. Per CPU: `acquireA` (`FAI_t(i)`, wait loop, `hold(i)`, `v = pull(i)`) and `releaseA` (`push(i, v); inc_n(i)`), with `acquireA_guarantee` (pulls the last released value), `acquireA_live_bounded` ((NCPU+1)(K+1), per lock), `acquireA_sim`, `releaseA_guarantee`. Atomic layer with data: `acq(i)` returns the block, `rel(i, v)` stores it; `acquireA_refines`, `releaseA_refines`. |
| `LockArrayFair.lean` | **A concrete fair array scheduler.** `fairEnvA` moves every lock in the log independently: the holder releases, or else the next ticket's owner holds and releases. `fairA_rely` (`RelyA`) and `fairA_fair` (`FairA` with a zero counter: on the lock `c` waits for, `now` advances at once). So the lock-array theorems are not vacuous: `acquireA_bounded_fair` (NCPU+1 iterations), `acquireA_refines_fair`, and `demo_contendedA` (a contended run on two locks, checked by `decide`). |
| `ArrayClientRefine.lean` | **Contextual refinement for every lock-array client.** Clients over atomic `x := acq(e)` (returns block `e`) and `x := rel(e₁, e₂)` (stores `e₂`), any number of locks, nested or interleaved. Linking inlines `lk = e; acquire; x = v` and `lk = e₁; v = e₂; release; x = 0`. `Rel`: same point, same client locals, L0 log replays to the L1 log plus other CPUs' later events, every lock idle or held. `client_sim`: related, inside one C block whose end is reachable and related one atomic step later, or wrong at L1; one table-built ε_H (`HRelyA`); the data pulled equals what atomic `acq` returns. `client_final`, `client_final_fair` (under `fairEnvA`, from the empty log). Uses `phase_frame`: a lock block's own events stay on its lock. |
| `LinkA.lean`, `ArrayLinkClient.lean` | **Multicore linking for the lock array.** `LinkA`: the `Link.lean` framework for the array machine (`aprims` on one global array log, `noEnvA`): `composeA` (per-CPU `GuarA` under every `RelyA` env ⇒ every run is explained by per-CPU runs under run-built envs satisfying `RelyA`, and the global log is valid), `transferA`. Instance: each CPU runs `acquire(L c); release(L c)`. `AtA` (23 program points, safety only), `own_stepA`, `at_otherA`, `client_guarA` (per-CPU, any rely-respecting env, fair or not), `array_linked`, and `multicore_cs_exclusiveA`: two CPUs in their critical sections on the same lock are the same CPU. |
| `NoLostUpdate.lean` | **No lost updates on the multicore machine.** Each CPU runs `acquire(L c); v = v + 1; release(L c)`. `AtD`: 26 program points tied to the lock's protocol state and, inside the critical section, to the block's contents (`v = m` after `pull`, `v = m + 1` after the increment). `GD`, a global invariant: every CPU's pushes are on its own lock and number 0 or 1 according to its point, and every block holds the number of pushes made on it. Another CPU's `push` cannot touch a block we work on (ownership plus `amutex`). `no_lost_updates`: once all CPUs finish, block `j` holds the number of CPUs that used lock `j`, mod 2³². |
| `FairC.lean`, `ArrayLive.lean` | **Liveness of the lock array on the multicore machine.** `FairC.fair_terminates`: for any C multicore machine, a `LiveCert` (potential no step raises, every active CPU's step lowers, activity persists, some CPU active while any unfinished) bounds every `K`-fair run by `K * (Φ₀ + 1)` steps. `ArrayLive`: weighted program points `AtW` for the increment client (wait loop weighs 19 while not your turn), `own_stepW`, `at_otherW`, the potential `GL`, and `act_existsW`: per lock, the owner of the ticket being served (`Cover`) is never spinning. `array_fair_terminates`: every `K`-fair run of `T ≤ 8` CPUs has fewer than `K * (27 * T + 1)` steps. |
| `MCSProtocol.lean`, `MCSLock.lean` | **The MCS lock, with the same atomic interface.** Events `swap` (with the node writes folded in), `link`, `get_busy`, `hold`, `get_next`, `cas`, `handoff` on a shared log. The queue is tracked by ghost positions `[hd, tl)`: a CPU's predecessor sits at the position before its own, so the invariant `MInv` is arithmetic. `mutexM`; `mreplay_hreplay` (R₁ onto `AtomicLayer`'s atomic lock, the same as the ticket lock's). Per CPU: C `acquireM`/`releaseM`, fuel specs, `acquireM_sim`/`releaseM_sim`, guarantees, `acquireM_live` (under `FairB`: the queue ahead shrinks or a counter drops), `releaseM_live` (under `FairN`: the successor links or a counter drops), and `acquireM_refines_atomic`/`releaseM_refines_atomic` onto `hprims`. |
| `MCSFair.lean` | **A concrete fair MCS scheduler.** `fairEnvM`: when `c` holds the lock with no successor, one links (an idle CPU swaps in if needed); otherwise the queue head releases (taking the lock first, linking its successor if needed, else `cas`). It never acts as `c`. `fairM_rely` (`RelyM`), `fairM_B` and `fairM_N` (zero counters: the queue ahead shrinks, the successor links). So the MCS theorems are not vacuous: `acquireM_refines_fair`, `releaseM_refines_fair`, and `demo_mcs` (a contended run, by `decide`). |
| `LinkM.lean`, `MCSLink.lean` | **Multicore linking for the MCS lock.** `LinkM`: the linking framework for the MCS machine (`mprims` on one global MCS log): `composeM`, `transferM`. Instance: each CPU runs `acquireM; releaseM`. `AtM` (36 program points, safety only, each tied to the CPU's MCS phase and to what it last read of `p`, `busy`, `next` or the `cas` result), `own_stepM`, `at_otherM`, `client_guarM` (per CPU, under any rely-respecting environment), `mcs_linked`, and `multicore_cs_exclusiveM`: two CPUs between `acquireM` and `releaseM` are the same CPU. |
| `MCSLive.lean` | **Liveness of the MCS lock on the multicore machine.** `AtWM`: `AtM`'s 36 points with weights 41..0; the `busy` loop weighs a flat 29 while `busy` is set, the `next` loop a flat 8 while `next` is null. `own_stepWM` (a CPU's step lowers its weight unless it spins), `at_otherWM` (other CPUs' events never raise it: `busy` only clears, `next` only gets set, and while `c` holds the lock `hd` stays put). `act_existsWM`: if every unfinished CPU spun, the queue head would be waiting on `next` with a successor still mid-`link`, which is not a spin. `mcs_fair_terminates`: under any scheduler that moves each unfinished CPU within `K` steps, `T ≤ NCPU` CPUs running `acquireM; releaseM` finish in fewer than `K * (41T + 1)` steps. |
| `MCSBound.lean` | **Bound numbers in the MCS events** (Kim et al. §3.1, §4.4–4.5). `swap b` carries the critical-section bound the client promises; `mem` is a shared-memory event inside the critical section. `bcal`: ghost replay that runs `mstep`, records each CPU's bound, and keeps the holder's remaining budget (`hold` sets it to the bound; each `mem` uses one unit; a `mem` or release needs one unit left). `bcal_mreplay`: forgetting bounds and `mem` events gives a valid MCS log. `hbreplay` is the paper's `H_CalLock` (`WAIT_LOCK n`, `REL_LOCK`, memory events); `bcal_hbreplay` is R₁ with bounds. `crit_bound`: fewer than `n` memory events before the release. `waitW`, the paper's `M_i`: other CPUs' events never raise it, and non-polls lower it (`wait_step`). `wait_bound`: while `i` waits, others emit at most `waitW` non-poll events. `wait_bound_B`: with every bound ≤ `B`, at most `NCPU·(B+5)`. Examples by `decide`: a run within its bound is accepted, an overrun is rejected. |
| `MCSBoundC.lean` | **The bound as a C argument** (Kim et al. §4.3). `bprims`: MCS primitives over bounded logs; `swap` takes the bound as its argument and appends `swap b`; `mem` is the critical section's shared-memory primitive. `acquireB` is `acquireM` with `p = swap(bound)`; `clientB n` is `acquire(bound); mem() × n; release()`. `step_erase`: a bounded step, erased (drop the bound argument, `mem()` becomes an assignment, drop bounds and memory events from the log), is exactly the unbounded step, when the bounded environment erases to an unbounded one (`EnvErases`; `liftEnv` builds one from any `MEnv`). `star_lift`: unbounded runs lift to bounded runs. Since `erS acquireB = acquireM` (`rfl`), the `MCSLock` results carry over: `acquireB_terminates`, `clientB_terminates`. `clientB_records_bound`: the finished log has this CPU's `swap (σ "bound")`. `clientB_guarantee`: with `n < bound` and an environment that keeps the bounded log valid (`BRely`), the client finishes idle on a valid bounded log (so a valid `H_CalLock` log). |
| `MCSLiveN.lean` | **MCS on the multicore machine with a critical section.** Each CPU runs `acquireM; critM n; releaseM`, where `critM n` is `n` steps (the erasure of `n` memory calls). `AtWN n` is `AtWM` plus four critical-section points; weights before the critical section go up by `3n + 2`. `mcsN_fair_terminates`: `K`-fair runs end within `K * (T * (3n + 43) + 1)` steps. `reachN`: every run keeps the global invariant. `multicore_cs_exclusiveN`: two CPUs in their critical sections are the same CPU. |
| `MCSBoundMC.lean` | **The bounded multicore machine.** `PGB` runs `bprims` on one global bounded log; each CPU runs `clientB n = acquire(bound); mem() × n; release()`. `cstep_erase`/`cstep_lift`: bounded multicore steps erase to unbounded ones and lift back (`erS (clientB n) = codeN n`). `multicore_cs_exclusiveB` (mutual exclusion) and `bounded_fair_terminates` (`K * (T * (3n + 43) + 1)`) carry over. `bounded_global_valid`: if every CPU's bound exceeds `n`, every reachable global log is a valid bounded log, so a valid `H_CalLock` log (`bounded_global_hcal`). Invariant: the erased state satisfies `GLM`; per CPU, the recorded bound is the C argument, and a holder's budget exceeds the memory calls still to come. |
| `LockRegion.lean` | **Lock arrays protecting regions.** Each lock protects a block of cells (`Region := Nat → Val`); the holder writes cells one by one (`wr j v`), and a release records the whole region. `rmutex` (per lock), `rreplay_hreplay` (R₁), `RDI`/`acquire_sees` (an acquirer sees exactly the region of the last release), C primitives `rd`/`wr` and a client `clientR k`, and `demo_region` (the log of two CPUs each incrementing a region's cells, by `decide`). |
| `ClightCall.lean` | **C-to-C calls and modules.** Functions with parameters and a return variable, modules as function tables, `link`. `stepF`: a call runs the callee in a fresh frame, and only the result is written back. `call_sim`: a callee run lifts to a complete call from any caller frame. `acquire_call`/`release_call`: the lock-array functions, called through frames, refine the atomic `acq`/`rel`. Callees are leaf functions. |
| `PrintC.lean` | **A verified C printer.** Tokens, a printer (blocks for sequences, fully parenthesized expressions), a parser, and `parse_print`: parsing the printed tokens gives back the AST; `print_injective`. `Bench/EmitC.lean` prints through it (`emit_faithful`); only `render` (tokens to text) is unverified. |
| `CallStack.lean` | **Nested calls.** A call-stack machine `stepG`: function bodies call primitives and functions, to any depth. `star_stack` (a run ignores the frames below), `call_simG` (a complete body run lifts to a call from any caller at any depth), `lift_star`/`callee_split` (leaf code runs as plain ClightL, both directions). `inc_call`: `inc(lk)`, a function calling `acquire` and `release`, refines the two atomic steps. |
| `ClientCall.lean` | **Client refinement through real calls** (ticket lock). `MC P` replaces each atomic `acq`/`rel` in a client by a call into `ticketMod`. `acquire_complete`: a finished `acquire` meets its fuel spec. `call_to_inline`: a finished call-machine run gives a finished inlined run with the same log and client locals. `client_final_call`: every client linked by calls refines the atomic layer. |
| `PrintPy.lean` | **A verified Python printer.** Tokens with `indent`/`dedent`, printer, parser. `parse_print`: parsing the printed tokens of a source command gives it back with sequences nested to the right. `print_eq_iff`: two source programs print the same exactly when equal up to that nesting. `Bench/EmitPy.lean` prints through it (`emit_faithful`). |
| `LockRegionCPU.lean` | **Lock regions per CPU.** `rprimsA` adds `rd`/`wr` to the lock-array lock primitives. `step_erase`: lock-only code steps exactly as on the lock array once writes are erased, so `acquireA` and its liveness carry over (`star_liftR`); `lock_run_valid` keeps the region log valid. `crit_runR`: the critical section increments exactly its cells. `clientR_guarantee`: the client finishes idle on a valid log and releases the previous holder's region with cells `0..k-1` incremented. `clientR_fair`: an instance under a fair region scheduler. |
| `RegionLive.lean` | **Lock regions on the multicore machine.** `PGR`: all CPUs on one global region log; CPU `c` runs `clientM nc = acquire(L c); cell[j]++ for j < nc; release(L c)`. `AtW nc`: weighted program points (generated from `ArrayLive`'s, with read/write points per cell that record the cell and the value read). `reachR` (every reachable global log is valid), `region_cs_exclusive` (two CPUs touching the region of the same lock are the same CPU), `region_fair_terminates` (`K * (T * (27 + 6 * nc) + 1)`). |
| `RegionNoLost.lean` | **No lost updates for regions on the multicore machine.** `wrT`: writes still to come in a thread's code; `step_wr`: a step keeps it, a write uses one. `GD`: cell `j` of region `i` holds the number of CPUs on lock `i` that have written it. `gd_step` preserves it. `no_lost_updates_R`: when every CPU has finished, each of the first `nc` cells of region `i` holds the number of CPUs that used lock `i`. |
| `KernPAlloc.lean` | **Kernel: the physical page allocator** (mCertiKOS `MALInit`/`MALOp`/`MALT`). `cs_guarantee`: `acquire; C; release` for any verified critical section `C` on a region. `pallocSpec` (mark and return the first free page), `palloc_fresh`, `scan_run` (the C scan loop computes it), `palloc_guarantee` (`palloc` refines `pallocSpec`), `pfree_guarantee`. See `KERNEL.md`. |
| `KernFrame.lean` | **Kernel: critical sections that take a second lock.** `Runs` and its combinators (runs of structured code under any continuation). `fr_star`: a run changes only the variables its code assigns. `lk_star`: code that passes `lk` to every primitive has all its own events on that lock. `ext_frame`: events of other CPUs, and our own on another lock, leave our phase on lock `j` and, while we hold it, region `j` alone. `CSt`, `cst_rd`, `cst_wr`: the state inside a critical section and the rules for reading and writing a cell. `cs_guarantee2`: `acquire(i); C; release(i)` where `C` may take lock `j` inside. |
| `KernPT.lean` | **Kernel: two-level page tables** (mCertiKOS `MPTIntro`/`MPTOp`/`MPTCommon`). The directory holds the address of each second-level table's page. `ptInsertCS`: read the directory entry, call `palloc` on the allocation table's lock if the table is missing (`palloc_nested`), zero the page (`zero_run`), install it, write the entry. `ptInsert_guarantee`: `pt_insert` refines `ptInsertSpec`. `ptRmv_guarantee`, `ptRead_guarantee`. `PTInv` (present entries are addresses of allocated pages, no two share a page) with `insert_lookup_same`, `insert_lookup_other`, `insert_inv`, `rmv_lookup`. ClightL gains `*` for the address `nd + p * ne`. |
| `KernContainer.lean` | **Kernel: containers** (mCertiKOS `MContainer`): per-process quota, usage, parent, child count. `nest`, `nest_run`: lock-only code on another lock, called inside a critical section, keeps our lock and region. `ctAlloc_guarantee` (under quota: `palloc`, charge a page if it succeeded), `ctFree_guarantee` (give a page back, `pfree`), `ctSplit_guarantee` (set up a child with quota `amt`, charge the parent). `alloc_inv`, `free_inv`, `split_inv`: `usage ≤ quota` is kept, and a split leaves the child with quota `amt`, usage 0 and the right parent. |
| `KernOwner.lean` | **Prototype, not in mCertiKOS: page ownership.** Allocation-table cells are tags: 0 free, 1 kernel, `id + 2` container `id`. `CS1`, `cs_guarantee1`: the one-lock step with `Runs`. `pallocO_guarantee` (tag the first free page), `pfreeO_guarantee` (free only if the tag is the caller's; result says whether). `ctAllocO_guarantee`, `ctFreeO_guarantee`: `container_alloc` tags its page, `container_free` lowers the usage only if the container owned the page. `ostep_other`: a step by one owner leaves every other owner's set of pages as it was. `PTOwn`, `pt_osteps`: a page table whose pages are the kernel's keeps `PTInv` across any container steps. `insert_own`: `pt_insert` keeps `PTOwn`. |
| `MALOp.lean` | **Ported from mCertiKOS** (`MBoot`, `MALOp`): `ATInfo`, `PPgInfo`, `first_free`, `is_at_norm_spec` … `palloc'_spec`, `pfree'_spec`, `match_AT` (`MatchD`), `AT_kern`, `AT_usr`, `consistent_ppage`. The C code of `is_norm`, `at_get`, `at_set`, `at_set_c`, `get_nps`, `palloc`, `pfree`. `palloc_refines`, `pfree_refines`. |
| `MContainer.lean` | **Ported from mCertiKOS** (`MALT` code, `MContainer` interface): `Container`, the getter specs, `container_split_spec`, `container_alloc_spec`, `match_container` (`MatchC`). `getter_guarantee`, `container_alloc_refines`, `container_split_refines`. No `container_free`: mCertiKOS has none. |
| `MContainerInv.lean` | **Ported from mCertiKOS**: `child_quotas_bounded`, `Container_valid`, `sum_quotas`, `unused_pages_AT`, `quota_bounded_AT`. `alloc_valid`, `split_valid`, `alloc_quota_bounded`, `split_quota_bounded`, `alloc_at_inv`: the specs preserve the invariants. `alloc_defined`: `container_alloc_spec` is defined under them. (`palloc_inv`, `pfree_inv` are in `MALOp.lean`.) |
| `Layer.lean` | **Layer interface.** `Triple` (a primitive's spec as a triple with a write footprint), `Triple.seq`, `Triple.conseq`, `Triple.widen`, `Triple.lift` (frame: reuse a primitive when the state grows), `acquire_runs`, `release_runs`, `Triple.locked` (from a triple to `acquire; s; release`). |
| `MPTIntro.lean` | **Ported from mCertiKOS** (page-table pool accessors): `PTPerm`, `PTEInfo`, `PDE`, `PTData`; the eight specs `getPDE_spec` … `setIDPTE_spec`; `MatchPT`, `Layout`; `pool_update`, `pte_update`, `idp_update`, `pde_unique`; the C code of `get_PDE`, `set_PDE`, `rmv_PDE`, `set_PDEU`, `get_PTE`, `set_PTE`, `rmv_PTE`, `set_IDPTE`, each proved to refine its spec as a `Triple`. `set_pt` not ported (needs `CR3`). |
| `MPTOp.lean` | **Ported from mCertiKOS** (`MPTIntroCSource.v`): `PDX`, `PTX`; `pt_read`, `pt_read_pde`, `pt_rmv_aux`, `pt_rmv_pde`, `pt_insert_aux`, `pt_insert_pde` refine `ptRead_spec` … `ptInsertPDE_spec`. Each proof is the accessor's triple plus `Triple.assign_pre`. |
| `EnvFairGen.lean` | **Generic environment fairness.** `OwnerCert r T B`: valid log, queued CPUs are unfinished threads, and the owner of the current ticket takes at most `B` steps before `now` moves (CCAL's "releases within k steps"). `owner_persists` (protocol fact for any programs). `envFair_of_cert`: `EnvFair ((B+1)·K)` under any `K`-fair scheduler. `ticket_cert`: the ticket client has `B = 16`; `fair_envFair_gen` recovers `EnvFair (17K)`. |
| `ThreadLayer.lean` | **A minimal thread layer.** `TStep`: one CPU runs a pool of threads and switches only at yield points. `tsteps_csteps`: such a run is a multicore run with threads as CPUs. `thread_cs_exclusive`: mutual exclusion for threads on one CPU (ticket client). |

**Fidelity pass (2026-11-07).** See `COMPARISON.md` for a row-by-row comparison with CertiKOS.
- `hold` is now the linearization point (CCAL's R₁), and `get_n` is a pure read.
- L1 `rel` runs in CCAL's critical state, with no ε_H query (`held_no_env`).
- Liveness has an explicit bound, the analogue of n×m×k: `acquire_live_bounded` gives (NCPU+1)(K+1); under the fair scheduler it is 18 iterations (`acquire_bounded_fair`).

**Python side (2026-11-08).** The ClightL → PyL translation, its equivalence proof (`ClightToPy.lean`, `TicketPy.lean`) and liveness transfer (`ClightToPyLive.lean`, `TicketLive.lean`) are done. Under any scheduler that runs every unfinished thread within every `K` steps (letting it into `with L:`), the translated ticket-lock client finishes within an explicit bound, cannot deadlock, and ends with `lk.ticket == lk.now`. Not yet done:
- multicore linking now covers safety (`Link.lean`) and the per-CPU liveness proof (`LiveLink.lean`), with environment fairness derived from scheduler fairness (`SchedFair.lean`). The Python termination bound still comes from the direct global potential in `TicketLive.lean`, not from the linked per-CPU bound;
- fairness is assumed of the Python scheduler *and* of `L`. CPython guarantees neither; with 8 threads the generated Python ticket lock spends most of its time in GIL convoys, which is a performance problem, not a counterexample;
- infinite runs are handled only through the fairness bound; an unfair infinite Python run is not related to a C run;
- the printer `Bench/EmitPy.lean` (AST → Python source) is unverified, like `EmitC.lean`;
- PyL lacks allocation, exceptions, function calls, multiple locks, fractional permissions;
- the CSL (`PyCSL.lean`) and the translation are not yet combined (e.g. deriving race freedom of the translated code from the CSL).

**Not yet in the prototype** (in order):
- **C-to-C calls and modules.** Functions with call frames, modules and linking are in `ClightCall.lean`, and the lock functions called through frames refine the atomic layer. Nested calls are in `CallStack.lean`, and whole-client refinement through calls is proved for the ticket lock (`ClientCall.lean`). Missing: the same for lock-array and MCS clients, which still inline.
- **Rest of multicore linking.** Parallel composition and transfer (`Link.lean`) and per-CPU liveness on multicore runs (`LiveLink.lean`) are done. `EnvFair` is derived from a fair scheduler (`SchedFair.lean`), for the ticket-lock client only (its proof uses that client's program-point weights). A generic version is in `EnvFairGen.lean` (any client pool with an owner bound; the ticket client is its one instance), and a minimal thread layer in `ThreadLayer.lean` (threads as virtual CPUs, safety only). Missing: owner bounds for other clients; scheduler queues and thread liveness; thread-safe CompCertX.
- **Lock arrays: the rest.** Lock arrays with `pull`/`push` are done per CPU and at the atomic layer (`LockArray*.lean`). A concrete fair array scheduler shows they are not vacuous (`LockArrayFair.lean`). Contextual refinement for every client is done (`ArrayClientRefine.lean`). Multicore linking (safety) is done for an `acquire(L c); release(L c)` client (`ArrayLinkClient.lean`). No lost updates (`NoLostUpdate.lean`) and fair termination (`ArrayLive.lean`) are proved on the multicore machine. Regions: `LockRegion.lean` lets each lock protect a block of cells (protocol, R₁, data invariant, C primitives); the per-CPU C code and its no-lost-updates guarantee are in `LockRegionCPU.lean`, and the multicore machine (validity, mutual exclusion, fair termination, no lost updates across CPUs) in `RegionLive.lean` and `RegionNoLost.lean`. Missing for regions: client refinement for every client, and a linking framework.
- **MCS lock: the rest.** Protocol, per-CPU code, liveness and refinement to the shared atomic layer are done (`MCS*.lean`). A concrete fair scheduler shows the theorems are not vacuous (`MCSFair.lean`), multicore linking (safety) is done (`MCSLink.lean`), multicore liveness under a fair scheduler (`MCSLive.lean`), and bound numbers in the events with the bounded atomic layer and the bounded-waiting measure (`MCSBound.lean`). The C code takes the bound as an argument (`MCSBoundC.lean`), and the unbounded proofs carry over by erasure. The per-CPU bounded guarantee is proved (`clientB_guarantee`), and so are the bounded multicore machine's mutual exclusion, fair termination and global bounded validity (`MCSBoundMC.lean`).
- **ε_H generality.** ε_H is built per run, as a finite table.

Build:
```bash
PATH="$PWD/.tools/lean-4.35.0-darwin_aarch64/bin:$PATH" lake build
```
(The `~/.elan` toolchains on this machine are x86_64 builds and don't run without Rosetta, so an arm64 Lean 4.35.0 was unpacked into `.tools/`, which is git-ignored.)

---

## 1. What "the full CertiKOS spec" covers

From the mC2 page (Yale FLINT), mC2 is about **6,100 lines of C and 400 lines of x86 assembly**, organized as modules that each consist of many certified layers:

1. **Multicore machine model** → **CPU-local machine** (per-CPU view, with other CPUs abstracted into ε)
2. **Spinlock module:** ticket lock and MCS lock behind one interface
3. **Device driver module**
4. **Memory management:** physical memory, virtual memory (page tables), shared memory
5. **Thread management:** shared queue library, TCBs, scheduler (yield/sleep/wakeup)
6. **Thread-local machine** (per-thread view)
7. **Process management:** starvation-free condition variables, synchronous IPC
8. **Virtual machine management:** Intel hardware virtualization, so mC2 doubles as a hypervisor
9. **Trap handler module:** the whole-kernel spec, which is the top of the stack

The end-to-end theorem is **contextual refinement** of the compiled kernel (C compiled by CompCertX to LAsm, linked with hand-written LAsm modules) running on the multicore machine, against the trap-handler spec.

"Full parity" means all nine module groups, on the original target.

### 1a. Faithfulness: what that pins down
- **Target: 32-bit x86 (IA-32).** The CertiKOS artifacts build for `ia32-linux` with gcc-multilib. The later Stack-Aware CompCertX / CompCertMC is also limited to 32-bit x86 because it uses the RockSalt encoder. So ClightL's integer and pointer widths are 32-bit. Keep the width a parameter so a 64-bit port remains possible later.
- **Source and specs.** The **mC2 sources (C, asm, Coq layer specs and proofs) are only available *on request*** from the CertiKOS team, according to the OSDI'16 artifact site. Public alternatives: the PLDI'16 mCertiKOS artifact (sequential, 32 layers, the security work) and the `npe9/certikos` mirror (PLDI artifact: CompCert, CompCertX, liblayers). All of them target **Coq 8.4pl4**, which is too old to build on a modern toolchain, so treat them as *reference text*, not something to run.
- **Faithful = port the Coq specs.** Each layer's abstract state (`RData`), primitive specs, relations and invariants get transcribed into Lean as executable definitions, keeping the same layer names and boundaries. Then the C and asm are checked against the ported specs. This makes "same spec as CertiKOS" a reviewable claim: a side-by-side diff of Coq and Lean definitions. The proofs are re-done, not translated: Coq 8.4 tactic scripts don't port mechanically.
- **Licensing:** check the terms the sources come with before porting specs into a project you plan to publish.
- **Fidelity deviations to declare up front:** (1) fairness as a hypothesis rather than an axiom (§4.3); (2) whatever compiler-bridge option is chosen (§4.6) instead of CompCertX.

---

## 2. How CertiKOS gets liveness (checked against the MCS paper)

1. **All nondeterminism lives in ε.** Each CPU's execution is deterministic once ε is fixed. Any interleaving is modelled by picking a particular ε. ε may only return events from *other* CPUs and must preserve log well-formedness.
2. **Downward simulation suffices.** As in CompCert: if the implementation is deterministic and the spec does not get stuck, a forward (downward) simulation implies the backward one. Because ε also fixes the *future* behaviour of other CPUs, forward proofs work even for fine-grained code. The paper explicitly contrasts this with backward simulation, which would be "intractable" for low-level C.
3. **Specs are total functions with fuel.** Loops without an obvious decreasing quantity (lock wait loops) are specified as "the first *n* iterations", with failure if *n* runs out. Proving C matches the spec only needs runs where the spec returned, and the C loop can match any finite run.
4. **Bound numbers in events.** `acquire` takes a **bound** argument: the client's promise about how many events its critical section will produce. The bound is recorded in the lock events. A waiter's wait time is computed from other CPUs' bounds, and the holder must exit within its own bound. This makes liveness reasoning local.
5. **Ghost layer for liveness.** A data-representation layer exposes logical-only state (the holder's remaining counters `c1`/`c2`, the waiting queue, pending CPUs) that is computed from the log but absent from the C code.
6. **Fairness is a bounded assumption.** There is a constant *F* such that no queued CPU waits more than *F* events before running again (`CalBound`). In Coq this was stated as an **axiom about logs**, which the paper calls an expedient choice. Threading it through the machine model would be the cleaner alternative.
7. **A termination measure over events** combines `CalBound`, the bounds of holders and waiters, and the queue length. Lemmas show every event decreases it or resets `CalBound` while making progress. That gives loop termination, which makes the fuel-based spec defined, which makes the atomic `acquire` spec **total**.
8. **Result:** the C/asm lock *contextually refines atomic acquire/release* with **mutual exclusion and starvation freedom**. Higher layers see a total, atomic `acquire`.

**Why fairness of the lock itself matters:** the paper notes that with an unfair lock, a termination-sensitive refinement to a simple terminating spec is impossible. That is why ticket and MCS locks (FIFO) are used rather than test-and-set locks.

---

## 3. Why not Clift

What was checked in Clift's source:

| Clift component | Problem for the CertiKOS method |
|---|---|
| `corres` (backward simulation over `NondetM` result sets) | Diverging code has no results, so `corres` holds **vacuously**. A forever-spinning `acquire` "refines" an atomic `acquire`. It is also the wrong direction: CertiKOS proves *downward* and flips via determinism. |
| `NondetM` lifting (L1–L5) | No divergence outcome. `totalHoare` means "∃ a result". This is where all of Clift's proof convenience lives, and it is the part that would need replacing. |
| Relational `spec`, `AsmSpec` | Reintroduces nondeterminism outside ε, which breaks point 1 of §2. |
| `Concurrency.lean` | Single ISR, preemption points placed by hand, no fairness, no bounds, no barriers. Not reusable. |
| Big-step `Exec` | Can express "spec returns ⇒ code terminates in a related state" for deterministic code. But big-step has no notion of steps for simulation measures, and no connection to an assembly or compiler semantics. |
| Flat byte heap, 32-bit hard-coded, no `&local` | Needs restructuring anyway. A flat heap also differs from CompCert-style block memory, which is what a compiler-correctness bridge needs. |

**Verdict:** the parts of Clift worth keeping are the C *front end* idea (clang JSON → AST) and some tactic patterns. Everything that carries semantic weight needs replacing. So build the semantics ourselves. Clift's Python importer can be **adapted** as the trusted front end if that is convenient. It is about 4.4K lines and would need a new emitter for the ClightL AST.

---

## 4. Replacement architecture

### 4.1 ClightL: the C semantics
- **Syntax:** CompCert Clight-like. Side-effect-free expressions, statements, function calls, structs, unions, pointers, `&local` supported. Fixed-width integers (`BitVec`); **32-bit pointers and `int`/`long`, to match IA-32 mC2**.
- **Semantics:** **small-step, deterministic** transition function `step : Genv → State → Option (Event? × State)`. It is executable, so it can be evaluated and `simp`-unfolded in proofs.
- **Memory:** CompCert-style **block-based memory** with permissions. This makes push/pull ownership and stack frames clean, and the memory model lines up with a compiler proof.
- **External calls** are layer primitives: deterministic Lean functions `AbsState → ε → Args → Option (Ret × AbsState)`. They are the *only* way to touch shared state.
- **Undefined behaviour** = stuck (`none`). Theorems are about safe executions, as in CertiKOS.
- **Front end (trusted):** clang `-ast-dump=json` → ClightL AST, adapting Clift's importer or writing a new one. Alternatively, write kernel code directly as ClightL ASTs in a Lean DSL, which removes clang from the TCB.

### 4.2 Layer framework
- **Layer interface** `L = (AbsState, primitives, invariants, rely/guarantee)`.
- **Certified layer** `L₁ ⊢_R M : L₂`: every primitive of `L₂` is implemented by a ClightL or asm function in `M` running on `L₁`. Proved by **forward simulation with a well-founded stutter measure**. The framework lemma (determinism of `L₁ + M` given ε, plus a non-stuck `L₂`) yields the backward simulation and **termination preservation**.
- **Vertical and horizontal composition**, then **contextual refinement** as the end-to-end statement.
- **Per-function proof style** (from the paper): run the C semantics on the function, check the final state equals the spec's. Automate with a symbolic-execution tactic over `step`.

### 4.3 Concurrency core
- **Events, logs, ε**: ε is a structure carrying proofs of the two framework properties (no self-events, well-formedness preserved).
- **Fairness as an explicit hypothesis, not an `axiom`.** It is carried in the layer interfaces from the machine model up, and appears in the final theorem statement. This is the cleaner variant the paper mentions, and Lean makes it easy to audit with `#print axioms`.
- **Push/pull** ownership for non-atomic shared memory (§5).
- **Machine refinements:** multicore machine (hardware scheduler) → CPU-local machine (ε) → thread-local machine. These are the theoretical core and the highest-risk proofs.

### 4.4 Liveness kit (reusable library)
- Lock event types carrying **bound numbers**. `acquire` takes a bound argument.
- **Fuel-based loop specs**: a combinator `iterateFuel n body : Option _`, with lemmas that the C `while` matches any finite fuel run.
- A **ghost-layer pattern**: log replay to logical state (queue, counters).
- **Measure lemmas**: given fairness *F* and holders' bounds, the wait measure decreases or `CalBound` resets with progress. This gives a generic "FIFO lock ⇒ total atomic acquire" theorem, instantiated for ticket and MCS.
- **Vacuity check** in CI: a forever-spinning `acquire` must *fail* to verify.

### 4.5 Assembly
- **LAsm-like** semantics for the chosen ISA, in the same `step`/event style. Asm modules (context switch, trap entry, atomics, VMX ops) are certified layers like C modules.
- **IA-32 LAsm port.** Following CertiKOS, this is CompCert's IA-32 `Asm` plus kernel instructions: `cli`/`sti`, control registers, `lock`-prefixed atomics (`xchg`, `cmpxchg`, `xadd`), trap entry/exit, and the VMX instructions. Hand-written in Lean and transcribed from the CertiKOS LAsm definition. It is part of the machine model, so it is trusted the same way CertiKOS's was.
- **VT-x.** VMCS state, VM entry/exit, EPT, and `vmread`/`vmwrite`/`vmlaunch`/`vmresume` are modelled abstractly in the machine model, as in mC2. This is a sizeable trusted spec: review it against the Intel SDM as a separate task.

### 4.6 Compiler bridge (this is where "full" costs the most)
| Option | Gives | Cost |
|---|---|---|
| **C1. Trust the C compiler** | Theorem holds for ClightL semantics, not for the binary | Zero. Acceptable as a milestone, but not "full CertiKOS". |
| **C2. Translation validation** of each compiled function against ClightL | Binary-level guarantee, compiler untrusted | Large: the validator plus its proof. |
| **C3. Verified non-optimizing compiler** ClightL → IA-32 LAsm in Lean, preserving layer refinement (a "CompCertX-lite") | Same shape as CertiKOS: the most faithful option | Largest: likely 1.5–3 person-years even without optimizations, plus the memory-model/linking work CompCertX did for layers. IA-32 is CompCert's most mature backend, so its design is a good template. |

### 4.7 Proof engineering
- Specs are **executable** Lean functions (`Option`-valued, fuel for loops). Test them before proving anything.
- Automation needed early: symbolic execution of ClightL, log-replay simplification, invariant framing, and measure arithmetic (`omega`).

---

## 5. Preserving fine-grained concurrency: checks

1. **Bottom-layer granularity:** one event per atomic hardware action (load, store, xchg, CAS, fetch-and-add, fence).
2. **No plain shared access:** shared data is reachable only through primitives. Ordinary memory is CPU-local until a pull moves it in.
3. **Memory model:** CertiKOS's machine model is sequentially consistent. Real x86 is TSO; SC is defensible for race-free code that synchronizes with `lock`-prefixed instructions, which mC2's locks use. Keep the SC machine for fidelity, and list "TSO ≈ SC for this code" as an explicit assumption. An optional later task can prove it against an x86-TSO model.
4. **Compiler reordering:** only solved by C2/C3. Under C1 it is an explicit TCB item.
5. **Interrupts:** the kernel runs with interrupts disabled in mC2. Keep that, or extend ε with interrupt events.
6. **Liveness:** §2 and §4.4. Termination-sensitive refinement by construction, plus the vacuity check.
7. **Atomic syscalls are earned:** only the composition theorem can produce an atomic-syscall layer.

---

## 6. Work breakdown (full mC2 parity)

| Phase | Deliverable | Rough effort |
|---|---|---|
| P0 | Request the mC2 sources from the CertiKOS team; meanwhile, mine the public PLDI'16 artifact for LAsm and layer-library definitions. Decisions (§9). Spike: ClightL core for a tiny subset + a deterministic `step`. Prove one function against one primitive via forward sim ⇒ backward. Build the vacuity check. | 1–2 months |
| P1 | Full ClightL (syntax, block memory, semantics, determinism lemma). Trusted front end. Symbolic-execution tactic. | 4–6 months |
| P2 | Layer framework: interfaces, certified layers, simulation with measures, determinism ⇒ backward + termination preservation, vertical/horizontal composition, contextual refinement. | 4–6 months |
| P3 | Concurrency core: logs, ε with properties, fairness hypothesis, push/pull. Multicore → CPU-local machine. | 4–8 months (highest risk) |
| P4 | Liveness kit + **ticket lock** end-to-end (mutual exclusion + starvation freedom), then **MCS lock**. | 4–6 months |
| P5 | IA-32 LAsm semantics (ported). Certified context switch / trap entry. | 3–6 months |
| P6 | Memory management (physical, virtual, shared), device driver layer. | 6–12 months |
| P7 | CPU-local → thread-local machine. Thread management (queues, TCBs, scheduler), starvation-free condition variables, IPC, process management. | 9–15 months |
| P8 | Virtualization module: VT-x machine-model primitives, VMCS/EPT layers, VM entry/exit handling. | 6–12 months |
| P9 | Trap-handler whole-kernel spec + end-to-end contextual refinement theorem. | 2–4 months |
| P10 | Compiler bridge: C2 or C3. | 1–3 years, can run in parallel from P2 onward |

**Milestone 1** (about 1–1.5 person-years): P0–P4 plus a toy 3-layer kernel on top of the ticket lock, under compiler option C1.

---

## 7. Python equivalence

**Target:** the **trap-handler (whole-kernel) spec**, which is atomic per syscall/trap thanks to the lower layers. The Python model is a **sequential, deterministic step function** `step(state, cpu, trap, env) -> (state, ret)`, with ε (scheduler and environment choices) passed **explicitly**. It never uses Python threads. Fine-grained concurrency and liveness stay in the Lean proof below the top layer.

**Theorem shape:** `PyModel ≡ TrapSpec` (for related states, same ε), combined with `Kernel ⊑ TrapSpec` from the main proof, gives `Kernel ⊑ PyModel`. Liveness transfers too: TrapSpec is total under the fairness hypothesis, so the Python model must be shown total under the same hypothesis. Python loops must therefore carry fuel or a measure, mirroring §2.3.

**Getting Python into Lean:**

| Option | How | Trust | Effort |
|---|---|---|---|
| A. Trusted translator | Python subset → Lean defs, then prove equivalence to TrapSpec | Translator in TCB | 1–3 months |
| B. Deep embedding | Lean semantics for the Python subset + AST importer | Parser only | 3–6 months |
| C. Generate Python from Lean | Verified printer against B's semantics | As B | As B |
| D. Differential testing | Lean (executable) vs Python vs kernel on random traces | None (testing) | Weeks. **Do first.** |

**Subset rules:** masked fixed-width ints; no set iteration (or a fixed order); value semantics (no aliasing); exceptions mapped to error returns; no `random` or time (everything comes from ε); explicit fuel on loops.

**Verdict:** feasible for a disciplined subset, at roughly the cost of one or two kernel layers. Not feasible for arbitrary Python or a threaded Python model.

---

## 8. Top risks
1. **Machine refinements** (multicore → CPU-local → thread-local): deepest proofs, no Lean precedent.
2. **Compiler bridge:** C3 is CompCertX-scale work. Without C2 or C3 the result is not "full CertiKOS".
3. **Scale:** around 37+ layers in the original. Automation quality determines the cost per layer.
4. **Source access:** faithful parity depends on getting the mC2 sources and specs from the CertiKOS team. Without them, the specs must be reconstructed from the papers, which weakens the "same spec" claim.
5. **Trusted x86 + VT-x machine model:** large and hand-written. Without Sail-style generated models, review against the Intel SDM is the only check.
6. **Front-end trust:** a clang-based importer is in the TCB unless the kernel is written as ClightL ASTs directly.

## 9. Decisions needed
1. ~~ISA~~: **decided: faithful IA-32 mC2 including VT-x.** Action: request the mC2 sources (owner: you, by contacting the CertiKOS team).
2. ~~Compiler bridge~~: **decided (by Claude, under your "don't ask" instruction; easy to revisit): C1 for milestone 1, then C3.** C3 is the faithful CompCertX analogue, and ClightL is being designed as a CompCert-style source language with this in mind.
3. **Front end:** clang importer (trusted) or kernel written as ClightL ASTs in Lean?
4. **Python:** hand-written by others (A/B) or generated from Lean (C)?

## Sources
- Kim, Sjöberg, Gu, Shao, "Safety and Liveness of MCS Lock—Layer by Layer": https://cs.yale.edu/flint/certikos/publications/mcslock.pdf
- mC2 overview: https://cs.yale.edu/flint/certikos/mc2.html
- CertiKOS framework overview: https://cs.yale.edu/flint/certikos/framework.html
- mC2 OSDI'16 artifact (sources on request): https://certikos.github.io/certikos-artifact
- PLDI'16 mCertiKOS security artifact: https://flint.cs.yale.edu/flint/publications/pldi16-security
- npe9/certikos mirror: https://github.com/npe9/certikos
- CompCertMC / Stack-Aware CompCertX: https://certikos.github.io/compcertmc
- Clight semantics (Blazy & Leroy): https://xavierleroy.org/bibrefs/Blazy-Leroy-Clight-09.html
- Clift: https://github.com/eisbaw/Clift
- iris-lean: https://github.com/leanprover-community/iris-lean
