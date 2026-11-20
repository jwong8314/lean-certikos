import CertiKOS.TDispatch

/-!
# mCertiKOS `TSysCall`: the kernel's entry points, ported

The top layer of mCertiKOS exports three primitives, each a whole passage
through the kernel: enter from user mode, do the work, leave to user mode.

Ported from `trap/SysCallGenSpec.v`: `sys_dispatch_c_spec_low_step`,
`pagefault_handler_spec_low_step`, `sys_yield_spec_low_step`. Ported from
`trap/SysCallGenAsmSource.v`: the three entry points, which are assembly
there:

```
syscall_dispatch: proc_exit_user; syscall_dispatch_c; proc_start_user
pgf_handler:      proc_exit_user; ptfault_resv(fault address); proc_start_user
sys_yield:        proc_exit_user; thread_yield        (resumes at proc_start_user)
```

* `syscall_dispatch_run`, `syscall_dispatch_ustar`: **a system call.** If
  `proc_exit_user_spec`, `sys_dispatch_c_spec` and `proc_start_user_spec` are
  defined in turn, the machine goes from the trap back to user mode, with the
  registers `proc_start_user_spec` returns, and the region matches the final
  state.
* `pgf_handler_run`, `pgf_handler_ustar`: **a page fault**, likewise with
  `ptfault_resv_spec`.
* `sys_yield_run`: **a yield.** The caller's kernel computation is parked,
  about to run `proc_start_user`, and the head of the ready queue runs.
* `resume_user_ustar`: a thread parked that way, once resumed, leaves the
  kernel with its own user context.
* `sys_yield_ustar`: **from user mode in one process to user mode in
  another**: the two together. The registers are the other process's saved
  user context.

What differs:
* As in mCertiKOS the theorems say: if the specifications are defined, the
  code runs as they say. They assume the invariants mCertiKOS carries
  (valid current thread, queue and container invariants).
* The fault address is the local `vaddr` at the trap (`CR2`), not a field
  `ti` of the state.
* All of this is inside a critical section: the lock is held on entry and
  still held on exit.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TSysCall

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU PProc FlatMem TTrap
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## The code (`SysCallGenAsmSource.v`) -/

/-- `syscall_dispatch`: `proc_exit_user; syscall_dispatch_c; proc_start_user`. -/
def sysEntryK (cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart pb cpub : Nat) : Stmt KPrim :=
  .seq (mapS .base (procExitUserS cidb ucb pb cpub))
    (.seq (sysDispatchK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart)
      (mapS .base (procStartUserS cidb ucb pb cpub)))

/-- `pgf_handler`: `proc_exit_user; ptfault_resv(vaddr); proc_start_user`. -/
def pgfEntryS (cb cidb maxpage pb fb ucb cpub : Nat) : Stmt APrim :=
  .seq (procExitUserS cidb ucb pb cpub)
    (.seq (ptfaultResvS cb cidb maxpage pb fb) (procStartUserS cidb ucb pb cpub))

/-- `sys_yield`: `proc_exit_user; thread_yield;` and, when resumed,
`proc_start_user`. -/
def sysYieldK (tb qb num_proc num_chan cidb ucb pb cpub : Nat) : Stmt KPrim :=
  .seq (mapS .base (procExitUserS cidb ucb pb cpub))
    (.seq (threadYieldK tb qb num_proc num_chan cidb) (mapS .base (procStartUserS cidb ucb pb cpub)))

/-! ## Shapes of the two mode switches -/

theorem exit_shape {rs : UContext} {d d1 : UData} (h : proc_exit_user_spec rs d = some d1) :
    d1 = { d with ikern := true, PT := 0, ipt := true, uctxt := setAt d.uctxt d.cid rs } ∧ d.pg = true := by
  unfold proc_exit_user_spec at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    exact ⟨h.symm, hc.2.1⟩
  · cases h

theorem start_shape {d d' : UData} {rs : UContext} (h : proc_start_user_spec d = some (d', rs)) :
    d' = { d with ikern := false, ipt := false, PT := d.cid } ∧ rs = d.uctxt d.cid ∧ d.pg = true := by
  unfold proc_start_user_spec at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm, hc.2.1⟩
  · cases h

theorem ptfault_cid {maxpage num_proc vadr : Nat} {d d' : UData}
    (h : ptfault_resv_spec maxpage num_proc vadr d = some d') : d'.cid = d.cid := by
  unfold ptfault_resv_spec at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb elb cpub : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb
local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb
local notation "MUP" => MatchUP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub

/-! ### A system call -/

/-- **`syscall_dispatch` on the kernel machine**: from the trap, on an empty
kernel stack, to the end of the kernel computation. The registers of the trap
are in `u0` … `u16`, and so are the registers for user mode at the end. -/
theorem syscall_dispatch_run (code : Nat → Stmt KPrim)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hnum : cb + 5 * num_id < 2 ^ 32)
    (hnn : num_id ≤ num_proc) (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub) {mc pstart : Nat}
    {elf : Nat → Nat} (hov : num_id * mc + mc + 1 < 2 ^ 32) (hps : pstart < 2 ^ 32) {σ : Locals} {l : RLog}
    {K : Cont KPrim}
    {b : Region} {d d1 d2 d3 : UData} {rs rs' : UContext} (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b)
    (hM : MUP d b) (hE : MatchELF num_id elb elf b) (hcid : d.cid < num_proc)
    (hI : AInv num_proc num_chan d.toAData) (hCV : Container_valid num_id mc d.AC)
    (hcu : (d.AC d.cid).cused = true) (hrs : ∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v)
    (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : sys_dispatch_c_spec num_id mc num_chan code pstart elf d1 = some d2)
    (h3 : proc_start_user_spec d2 = some (d3, rs')) :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      KStar εR c code
        ⟨⟨sysEntryK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart pb cpub, K, σ⟩, d.kctxt, l⟩
        ⟨⟨.skip, K, σ'⟩, d3.kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MUP d3 b' ∧ MatchELF num_id elb elf b' ∧
      (∀ n, n < 17 → ∀ v, rs' n = some v → σ' (ureg n) = v) ∧ σ' "lk" = σ "lk" := by
  have hCL := hL.ilay.clay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  obtain ⟨hd1, hpg⟩ := exit_shape h1
  -- `proc_exit_user`
  obtain ⟨σ1, l1, b1, d1', r1, c1, m1, k1, f1, hq1, fr1⟩ := procExitUser_triple εR c i0 hL hcp0 hcp1 rs σ l b d
    hlk hcs hM ⟨hcid, hrs, d1, h1⟩
  rw [h1] at hq1
  simp only [Option.some.injEq] at hq1
  subst hq1
  have hlk1 : (σ1 "lk").toNat = i0 := by rw [k1]; exact hlk
  have hE1 : MatchELF num_id elb elf b1 := fun i hi => by
    rw [f1 _ (fun h => by rcases h with ⟨h3', h4'⟩ | h3' <;> omega)]
    exact hE i hi
  have hne1 : b1 (cpub + 1) ≠ 0 := m1.2.2.1 (by rw [hd1]; exact hpg)
  have hI1 : AInv num_proc num_chan d1.toAData := by
    rw [hd1]; exact ⟨hI.tc, hI.qc, hI.niq, hI.cnt, hI.inq⟩
  have hcid1 : d1.cid < num_proc := by rw [hd1]; exact hcid
  have hCV1 : Container_valid num_id mc d1.AC := by rw [hd1]; exact hCV
  have hcu1 : (d1.AC d1.cid).cused = true := by rw [hd1]; exact hcu
  have hk1 : d1.kctxt = d.kctxt := by rw [hd1]
  -- `syscall_dispatch_c`
  obtain ⟨σ2, l2, b2, hks, c2, m2, hE2, k2, f2, hc2⟩ := sysDispatch_run εR c i0 code hL hnum hnn hel0
    (by omega) hov hps (σ := σ1) (K := .seq (mapS .base (procStartUserS cidb ucb pb cpub)) K) hlk1 c1 m1.1
    hE1 hcid1 hI1 hCV1 hcu1 h2
  -- `proc_start_user`
  obtain ⟨hd3, -, hpg2⟩ := start_shape h3
  have hne2 : b2 (cpub + 1) ≠ 0 := by
    rw [f2 _ (fun h => by rcases h with (⟨h3', h4'⟩ | ⟨h3', h4'⟩ | ⟨h3', h4'⟩) | ⟨h3', h4'⟩ <;> omega)]
    exact hne1
  obtain ⟨σ3, l3, b3, r3, c3, m3, hreg, f3⟩ := procStartUser_run εR c i0 hL hcp0 hcp1 (σ := σ2)
    (by rw [k2]; exact hlk1) c2 m2 ⟨fun _ => hne2, fun _ => hpg2⟩ (by rw [hc2]; exact hcid1) h3
  have hk3 : d3.kctxt = d2.kctxt := by rw [hd3]
  refine ⟨σ3, l3, b3, ?_, c3, m3, fun i hi => ?_, hreg, ?_⟩
  · rw [hk3]
    refine (kstar_seq r1 _ K d.kctxt).trans ((KStar.single (kstep_seq _ _ K σ1 d.kctxt l1)).trans ?_)
    rw [← hk1]
    exact hks.trans ((KStar.single (kstep_skip_seq _ K σ2 d2.kctxt l2)).trans
      (kstar_base r3 K d2.kctxt))
  · rw [f3 _ (by omega)]
    exact hE2 i hi
  · rw [r3.frame rfl, k2, k1]

/-- **A system call, from user mode to user mode.** -/
theorem syscall_dispatch_ustar (code : Nat → Stmt KPrim) (entry : Nat → Nat) (lk : Val) (tn : Nat)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hnum : cb + 5 * num_id < 2 ^ 32)
    (hnn : num_id ≤ num_proc) (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub) {mc pstart : Nat}
    {elf : Nat → Nat} (hov : num_id * mc + mc + 1 < 2 ^ 32) (hps : pstart < 2 ^ 32)
    (hentry : code (entry tn) = sysEntryK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart pb cpub)
    {σ : Locals} {l : RLog} {b : Region} {d d1 d2 d3 : UData} {rs rs' : UContext} (ur0 : Nat → Val)
    (hlkσ : σ "lk" = lk) (hlk : lk.toNat = i0) (hcs : CS1 c i0 l b) (hM : MUP d b)
    (hE : MatchELF num_id elb elf b) (hcid : d.cid < num_proc) (hI : AInv num_proc num_chan d.toAData)
    (hCV : Container_valid num_id mc d.AC) (hcu : (d.AC d.cid).cused = true)
    (hrs : ∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : sys_dispatch_c_spec num_id mc num_chan code pstart elf d1 = some d2)
    (h3 : proc_start_user_spec d2 = some (d3, rs')) :
    ∃ (ur : Nat → Val) (l' : RLog) (b' : Region),
      UStar εR c code entry lk (.user ur0 d.kctxt l) (.user ur d3.kctxt l') ∧
      CS1 c i0 l' b' ∧ MUP d3 b' ∧ MatchELF num_id elb elf b' ∧
      ∀ n, n < 17 → ∀ v, rs' n = some v → ur n = v := by
  obtain ⟨σ', l', b', hks, hcs', hM', hE', hreg, -⟩ := syscall_dispatch_run εR c i0 code hL hcp0 hcp1 hnum hnn hel0
    hec hov hps (σ := σ) (by rw [hlkσ]; exact hlk) hcs hM hE hcid hI hCV hcu hrs h1 h2 h3
  exact ⟨regsOf σ', l', b', UStar.syscall tn hlkσ (by rw [hentry]; exact hks), hcs', hM', hE', hreg⟩

/-! ### A page fault -/

/-- **`pgf_handler`**: the fault address is in `vaddr`. -/
theorem pgf_handler_run (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hmax : 3 * maxpage < 2 ^ 32)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20) (hnn : num_proc ≤ num_id) {kl kh : Nat}
    {vadr : Nat} (hv : vadr < 2 ^ 32) {σ : Locals} {l : RLog} {b : Region} {d d1 d2 d3 : UData}
    {rs rs' : UContext} (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MUP d b)
    (hva : σ "vaddr" = BitVec.ofNat 32 vadr) (hcid : d.cid < num_proc)
    (hAT : ATInv maxpage kl kh d.toPData) (hq : (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota)
    (hrs : ∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : ptfault_resv_spec maxpage num_proc vadr d1 = some d2)
    (h3 : proc_start_user_spec d2 = some (d3, rs')) :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      Runs (rprimsA εR c) (pgfEntryS cb cidb maxpage pb fb ucb cpub) σ l σ' l' ∧ CS1 c i0 l' b' ∧ MUP d3 b' ∧
      (∀ n, n < 17 → ∀ v, rs' n = some v → σ' (ureg n) = v) ∧
      ∀ k, cb + 5 * num_id ≤ k → k < cpub → b' k = b k := by
  have hCL := hL.ilay.clay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  have := hCL.qlay.tlay.hte
  obtain ⟨hd1, hpg⟩ := exit_shape h1
  obtain ⟨σ1, l1, b1, d1', r1, c1, m1, k1, f1, hq1, fr1⟩ := procExitUser_triple εR c i0 hL hcp0 hcp1 rs σ l b d
    hlk hcs hM ⟨hcid, hrs, d1, h1⟩
  rw [h1] at hq1
  simp only [Option.some.injEq] at hq1
  subst hq1
  have hlk1 : (σ1 "lk").toNat = i0 := by rw [k1]; exact hlk
  have hne1 : b1 (cpub + 1) ≠ 0 := m1.2.2.1 (by rw [hd1]; exact hpg)
  have hcid1 : d1.cid < num_proc := by rw [hd1]; exact hcid
  -- `ptfault_resv`
  obtain ⟨σ2, l2, b2, d2', r2, c2, m2, k2, f2, hq2⟩ := ptfaultResv_triple εR c i0 hL hmax hnum hmp hnn
    (kl := kl) (kh := kh) vadr hv σ1 l1 b1 d1 hlk1 c1 m1.1
    ⟨by rw [fr1 "vaddr" (by decide) (by decide)]; exact hva, by omega, by rw [hd1]; exact hAT,
      by rw [hd1]; exact hq, d2, h2⟩
  rw [h2] at hq2
  simp only [Option.some.injEq] at hq2
  subst hq2
  obtain ⟨hd3, -, hpg2⟩ := start_shape h3
  have hne2 : b2 (cpub + 1) ≠ 0 := by
    rw [f2 _ (by omega)]
    exact hne1
  obtain ⟨σ3, l3, b3, r3, c3, m3, hreg, f3⟩ := procStartUser_run εR c i0 hL hcp0 hcp1 (σ := σ2)
    (by rw [k2]; exact hlk1) c2 m2 ⟨fun _ => hne2, fun _ => hpg2⟩ (by rw [ptfault_cid h2]; exact hcid1) h3
  refine ⟨σ3, l3, b3, Runs.seq r1 (Runs.seq r2 r3), c3, m3, hreg, fun k h1 h2 => ?_⟩
  rw [f3 k (by omega), f2 k (fun h => by rcases h with h | h <;> omega),
    f1 k (fun h => by rcases h with ⟨h3, h4⟩ | h3 <;> omega)]

/-- **A page fault, from user mode to user mode.** -/
theorem pgf_handler_ustar (code : Nat → Stmt KPrim) (entry : Nat → Nat) (lk : Val) (tn : Nat)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hmax : 3 * maxpage < 2 ^ 32)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20) (hnn : num_proc ≤ num_id) {kl kh : Nat}
    (hentry : code (entry tn) = mapS .base (pgfEntryS cb cidb maxpage pb fb ucb cpub)) {vadr : Nat}
    (hv : vadr < 2 ^ 32) {σ : Locals} {l : RLog} {b : Region} {d d1 d2 d3 : UData} {rs rs' : UContext}
    (ur0 : Nat → Val) (pool : Nat → KCtx) (hlkσ : σ "lk" = lk) (hlk : lk.toNat = i0) (hcs : CS1 c i0 l b)
    (hM : MUP d b) (hva : σ "vaddr" = BitVec.ofNat 32 vadr) (hcid : d.cid < num_proc)
    (hAT : ATInv maxpage kl kh d.toPData) (hq : (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota)
    (hrs : ∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : ptfault_resv_spec maxpage num_proc vadr d1 = some d2)
    (h3 : proc_start_user_spec d2 = some (d3, rs')) :
    ∃ (ur : Nat → Val) (l' : RLog) (b' : Region),
      UStar εR c code entry lk (.user ur0 pool l) (.user ur pool l') ∧ CS1 c i0 l' b' ∧ MUP d3 b' ∧
      ∀ n, n < 17 → ∀ v, rs' n = some v → ur n = v := by
  obtain ⟨σ', l', b', hr, hcs', hM', hreg, -⟩ := pgf_handler_run εR c i0 hL hcp0 hcp1 hmax hnum hmp hnn
    (kl := kl) (kh := kh) hv (σ := σ) (by rw [hlkσ]; exact hlk) hcs hM hva hcid hAT hq hrs h1 h2 h3
  exact ⟨regsOf σ', l', b', UStar.syscall tn hlkσ (by rw [hentry]; exact kstar_base hr .stop pool), hcs', hM',
    hreg⟩

/-! ### A yield -/

/-- **`sys_yield` on the kernel machine.** The caller is parked, about to run
`proc_start_user`; the head `la` of the ready queue runs. -/
theorem sys_yield_run (code : Nat → Stmt KPrim)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) {σ : Locals} {l : RLog} {b : Region} {d d1 : UData}
    {rs : UContext} {ql : List Nat} {la : Nat} {K : Cont KPrim} (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MUP d b)
    (hcid : d.cid < num_proc) (hI : AInv num_proc num_chan d.toAData) (hcv : CurIDValid d.toCData)
    (hrs : ∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) (h1 : proc_exit_user_spec rs d = some d1)
    (hq : d.abq num_chan = .AbQValid ql) (hla : ql.getLastD num_proc = la) (hne : la ≠ num_proc) :
    ∃ (σf : Locals) (l' : RLog) (b' : Region),
      KStar εR c code ⟨⟨sysYieldK tb qb num_proc num_chan cidb ucb pb cpub, K, σ⟩, d.kctxt, l⟩
        ⟨d.kctxt la, (yieldOut num_chan la ql
          ⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) K, σf.set "_" 0⟩ (toK d1)).kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧
      MU (putK d1 (yieldOut num_chan la ql
        ⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) K, σf.set "_" 0⟩ (toK d1))) b' ∧
      b' (cpub + 1) ≠ 0 ∧
      AInv num_proc num_chan (yieldOut num_chan la ql
        ⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) K, σf.set "_" 0⟩ (toK d1)).toAData ∧
      la < num_proc ∧
      CurIDValid (yieldOut num_chan la ql
        ⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) K, σf.set "_" 0⟩ (toK d1)).toCData ∧
      σf "lk" = σ "lk" ∧ ∀ k, cb + 5 * num_id ≤ k → k < cpub → b' k = b k := by
  have hCL := hL.ilay.clay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  have := hCL.hce
  obtain ⟨hd1, hpg⟩ := exit_shape h1
  obtain ⟨σ1, l1, b1, d1', r1, c1, m1, k1, f1, hq1, fr1⟩ := procExitUser_triple εR c i0 hL hcp0 hcp1 rs σ l b d
    hlk hcs hM ⟨hcid, hrs, d1, h1⟩
  rw [h1] at hq1
  simp only [Option.some.injEq] at hq1
  subst hq1
  have hlk1 : (σ1 "lk").toNat = i0 := by rw [k1]; exact hlk
  have hne1 : b1 (cpub + 1) ≠ 0 := m1.2.2.1 (by rw [hd1]; exact hpg)
  have hk1 : d1.kctxt = d.kctxt := by rw [hd1]
  -- `thread_yield`
  obtain ⟨σf, l2, b2, hfr, hks, c2, m2, hI2, hcv2, hlt, f2⟩ := thread_yield_run εR c i0 code hCL (σ := σ1)
    (K := .seq (mapS .base (procStartUserS cidb ucb pb cpub)) K) (d := toK d1) (ql := ql) (la := la) hlk1 c1
    m1.1.1.1 (by rw [hd1]; exact ⟨hI.tc, hI.qc, hI.niq, hI.cnt, hI.inq⟩) (by rw [hd1]; exact hcid)
    (by rw [hd1]; exact hcv) (by rw [hd1]; exact hpg) (by rw [hd1]; rfl) (by rw [hd1]; exact hq) hla hne
  refine ⟨σf, l2, b2, ?_, c2, matchU_putC hL _ m1.1 m2 (fun k h3' h4' => f2 k (fun hk => by
    rcases hk with (⟨h5, h6⟩ | ⟨h5, h6⟩) | h5 <;> omega)), ?_, hI2, hlt, hcv2,
    by rw [hfr "lk" rfl rfl, k1], fun k h1' h2' => ?_⟩
  · refine (kstar_seq r1 _ K d.kctxt).trans ((KStar.single (kstep_seq _ _ K σ1 d.kctxt l1)).trans ?_)
    have e : (toK d1).kctxt = d.kctxt := hk1
    rw [← e]
    exact hks
  · rw [f2 _ (fun hk => by rcases hk with (⟨h5, h6⟩ | ⟨h5, h6⟩) | h5 <;> omega)]
    exact hne1
  · rw [f2 k (fun hk => by rcases hk with (⟨h5, h6⟩ | ⟨h5, h6⟩) | h5 <;> omega),
      f1 k (fun h => by rcases h with ⟨h3, h4⟩ | h3 <;> omega)]

/-- **A parked thread, resumed, leaves the kernel** with its own user
context. -/
theorem resume_user_ustar (code : Nat → Stmt KPrim) (entry : Nat → Nat) (lk : Val)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) {σ : Locals} {l : RLog} {b : Region}
    {d d' : UData} {rs : UContext} (pool : Nat → KCtx) (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b)
    (hM : MU d b) (hpg : d.pg = true ↔ b (cpub + 1) ≠ 0) (hcid : d.cid < num_proc)
    (hs : proc_start_user_spec d = some (d', rs)) :
    ∃ (ur : Nat → Val) (l' : RLog) (b' : Region),
      UStar εR c code entry lk
        (.kern ⟨⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) .stop, σ⟩, pool, l⟩)
        (.user ur pool l') ∧
      CS1 c i0 l' b' ∧ MUP d' b' ∧ ∀ n, n < 17 → ∀ v, rs n = some v → ur n = v := by
  obtain ⟨ur, l', b', hu, hcs', hM', hreg, -⟩ := start_user_ustar εR c i0 code entry lk hL hcp0 hcp1 pool hlk hcs
    hM hpg hcid hs
  exact ⟨ur, l', b', .step (.kern (kstep_skip_seq _ .stop σ pool l)) hu, hcs', hM', hreg⟩

/-- **A yield, from user mode in one process to user mode in another.** The
process `la` at the head of the ready queue was parked by an earlier yield;
it leaves the kernel with the user context saved for it. -/
theorem sys_yield_ustar (code : Nat → Stmt KPrim) (entry : Nat → Nat) (lk : Val) (tn : Nat)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb)
    (hentry : code (entry tn) = sysYieldK tb qb num_proc num_chan cidb ucb pb cpub) {σ σB : Locals} {l : RLog}
    {b : Region} {d d1 : UData} {rs : UContext} {ql : List Nat} {la : Nat} (ur0 : Nat → Val)
    (hlkσ : σ "lk" = lk) (hlk : lk.toNat = i0) (hcs : CS1 c i0 l b) (hM : MUP d b) (hcid : d.cid < num_proc)
    (hI : AInv num_proc num_chan d.toAData) (hcv : CurIDValid d.toCData) (hinit : d.init = true)
    (hih : d.ihost = true) (hrs : ∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v)
    (h1 : proc_exit_user_spec rs d = some d1) (hq : d.abq num_chan = .AbQValid ql)
    (hla : ql.getLastD num_proc = la) (hne : la ≠ num_proc)
    (hB : d.kctxt la = ⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) .stop, σB⟩)
    (hlkB : (σB "lk").toNat = i0) :
    ∃ (ur : Nat → Val) (pool' : Nat → KCtx) (l' : RLog) (b' : Region) (d3 : UData),
      UStar εR c code entry lk (.user ur0 d.kctxt l) (.user ur pool' l') ∧ CS1 c i0 l' b' ∧ MUP d3 b' ∧
      d3.cid = la ∧ d3.ikern = false ∧ ∀ n, n < 17 → ∀ v, d.uctxt la n = some v → ur n = v := by
  obtain ⟨hd1, hpg⟩ := exit_shape h1
  obtain ⟨σf, l2, b2, hks, c2, m2, hne2, hI2, hlt, -⟩ := sys_yield_run εR c i0 code hL hcp0 hcp1 (σ := σ)
    (by rw [hlkσ]; exact hlk) hcs hM hcid hI hcv hrs h1 hq hla hne
  -- the process resumed is not the caller
  obtain ⟨s, hai⟩ := hI.inq la num_chan ql hlt (Nat.le_refl _) hq (last_mem hla hne)
  have hlc : la ≠ d.cid := by
    intro e
    have h := hcv.2
    rw [← e, hai] at h
    injection h with e1 e2
    omega
  -- `proc_start_user_spec` is defined in the state reached
  have hpgY : (putK d1 (yieldOut num_chan la ql
      ⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) .stop, σf.set "_" 0⟩ (toK d1))).pg = true := by
    rw [hd1]; exact hpg
  have hs : proc_start_user_spec (putK d1 (yieldOut num_chan la ql
      ⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) .stop, σf.set "_" 0⟩ (toK d1))) =
      some ({ putK d1 (yieldOut num_chan la ql
          ⟨.skip, .seq (mapS .base (procStartUserS cidb ucb pb cpub)) .stop, σf.set "_" 0⟩ (toK d1)) with
        ikern := false, ipt := false, PT := la }, d1.uctxt la) := by
    unfold proc_start_user_spec
    exact if_pos ⟨by rw [hd1]; rfl, hpgY, by rw [hd1]; exact hih, by rw [hd1]; rfl, by rw [hd1]; exact hinit⟩
  rw [hB] at hks
  obtain ⟨ur, l3, b3, hu, c3, m3, hreg⟩ := resume_user_ustar εR c i0 code entry lk hL hcp0 hcp1 (σ := σB) _ hlkB
    c2 m2 ⟨fun _ => hne2, fun _ => hpgY⟩ hlt hs
  refine ⟨ur, _, l3, b3, _, .step (.trap ur0 d.kctxt l tn σ hlkσ) (by
    rw [hentry]; exact (UStar.of_kstar hks).trans hu), c3, m3, rfl, rfl, fun n hn v hv => hreg n hn v ?_⟩
  rw [hd1]
  show setAt d.uctxt d.cid rs la n = some v
  rw [setAt_ne _ _ hlc]
  exact hv

end Code

end TSysCall
