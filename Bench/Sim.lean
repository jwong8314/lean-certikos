import CertiKOS

/-!
# Executable multi-CPU run of the verified ClightL ticket lock

Each CPU runs the *verified* ASTs `acquireCode` / `releaseCode` through the
ClightL small-step semantics `ClightL.step`, with the L0 primitive table
`Ticket.prims`. The log is global; the environment context returns nothing
because every CPU's events are appended directly to the shared log.

Scheduling follows CertiKOS (OSDI'16 §3.5): there is exactly one switch point
before each atomic operation. A turn runs a CPU's local steps up to and
including its next primitive call. CPUs take turns round-robin.

Usage: `sim T N` runs T CPUs × N acquire/release pairs and prints
`lean-model T N <log length> <fnv64 of log> <replay ok> <ms>`.
-/

open ClightL Ticket

def noEnv : EnvCtx where
  query _ _ := []
  noSelf := by intro c l e he; simp at he

/-- `i = 0; while (i != N) { acquire(); release(); i = i + 1; }` -/
def clientCode (N : Nat) : Stmt Prim :=
  .seq (.assign "i" (.const 0))
    (.while (.bin .ne (.var "i") (.const (BitVec.ofNat 32 N)))
      (.seq acquireCode (.seq releaseCode (.assign "i" (.bin .add (.var "i") (.const 1))))))

/-- Run CPU `c` up to and including its next primitive call.
`none` means the CPU has finished (or is stuck). -/
partial def runTurn (c : CPU) (cfg : Config Prim Log) : Option (Config Prim Log) :=
  match cfg.stmt with
  | .call .. => step (prims noEnv c) cfg
  | _ =>
    match step (prims noEnv c) cfg with
    | none => none
    | some cfg' => runTurn c cfg'

def simulate (T N : Nat) : IO Log := do
  let mut cfgs : Array (Option (Config Prim Log)) :=
    Array.replicate T (some ⟨clientCode N, .stop, fun _ => 0, []⟩)
  let mut log : Log := []
  let mut active := T
  let mut k := 0
  while active > 0 do
    match cfgs[k]! with
    | none => pure ()
    | some cfg =>
      match runTurn k { cfg with abs := log } with
      | none =>
        cfgs := cfgs.set! k none
        active := active - 1
      | some cfg' =>
        log := cfg'.abs
        cfgs := cfgs.set! k (some cfg')
    k := (k + 1) % T
  return log

def kindCode : EvKind → Nat
  | .incTicket => 0 | .getNow => 1 | .incNow => 2 | .hold => 3

/-- FNV-1a (64-bit) over the tokens `cpu:kind;`, oldest event first. -/
def fnv (l : Log) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for e in l.reverse do
    for ch in s!"{e.cpu}:{kindCode e.kind};".toList do
      h := (h ^^^ ch.toNat.toUInt64) * 1099511628211
  return h

def main (args : List String) : IO Unit := do
  let T := (args.getD 0 "2").toNat!
  let N := (args.getD 1 "10").toNat!
  let t0 ← IO.monoNanosNow
  let log ← simulate T N
  let len := log.length
  let t1 ← IO.monoNanosNow
  let ok := (replay log).isSome
  IO.println s!"lean-model {T} {N} {len} {fnv log} {ok} {(t1 - t0).toFloat / 1e6}"
