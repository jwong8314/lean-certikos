import CertiKOS.PThreadSwitch

/-!
# mCertiKOS `kctxt_new` and `thread_spawn`, ported

Ported from `objects/ObjThread.v`: `kctxt_new_spec`, `thread_spawn_spec`.
Ported from `proc/PKContextCSource.v` and `proc/PCurIDCSource.v`: the C code.

```
kctxt_new(entry, id, quota):  i = pt_new(id, quota);
                              if (i == num_proc) return num_proc;
                              set_SP(i, top of stack i); set_RA(i, entry); return i;
thread_spawn(entry, id, quota): i = kctxt_new(entry, id, quota);
                              set_state(i, READY); enqueue(num_chan, i); return i;
```

* `liftPC`: **an operation of the page-table layers keeps its triple in the
  state with threads, queues and the current thread**, if it writes only
  cells of those layers and keeps `pg`. This is the passthrough mCertiKOS
  states layer by layer; here it crosses the shared-memory table, the
  control blocks, the queues, the list view and the current thread at once.
* `kctxt_new_run`: `kctxt_new` on the kernel machine does what
  `kctxt_new_spec` says: a child container, and a context that starts at
  `entry` on an empty stack.
* `thread_spawn_run`: **`thread_spawn` does what `thread_spawn_spec` says**:
  the new thread is ready, at the back of the ready queue.
* `split_child_free`: the slot a split gives is unused before
  (`Container_valid`). With `NotInQ` that puts the new thread on no queue,
  which `enqueue` requires; mCertiKOS's code proof makes the same argument.

What differs: `entry` is a number, looked up in the machine's text. The
branch `i == num_proc` of `kctxt_new` is never taken under the
specification, as in mCertiKOS.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PSched

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID KMach PKCtx
open MALInit (tn asg_run)

/-! ## Specifications -/

/-- **`kctxt_new_spec`**: `pt_new`, then the child's context starts at
`entry` on an empty stack. -/
def kctxt_new_spec (num_id mc : Nat) (code : Nat → Stmt KPrim) (entry id q : Nat) (d : KData) :
    Option (KData × Nat) :=
  match pt_new_spec num_id mc id q d.toPTData with
  | some (p, i) =>
    some ({ d with
      toPTData := p
      kctxt := setAt d.kctxt i { d.kctxt i with cont := .stop, stmt := code entry } }, i)
  | none => none

/-- **`thread_spawn_spec`**: `kctxt_new`, then the child is ready and at the
back of the ready queue. -/
def thread_spawn_spec (num_id mc nc : Nat) (code : Nat → Stmt KPrim) (entry id q : Nat) (d : KData) :
    Option (KData × Nat) :=
  match kctxt_new_spec num_id mc code entry id q d with
  | some (d1, i) =>
    match d1.abq nc with
    | .AbQValid l =>
      some ({ d1 with
        abtcb := setAt d1.abtcb i (.AbTCBValid .READY nc)
        abq := setAt d1.abq nc (.AbQValid (i :: l)) }, i)
    | .AbQUndef => none
  | none => none

/-- The slot a split gives is unused. -/
theorem split_child_free {num_id mc : Nat} {C : ContainerPool} (h : Container_valid num_id mc C) {id : Nat}
    (hu : (C id).cused = true) (hL : (C id).cchildren.length < mc) :
    (C (id * mc + 1 + (C id).cchildren.length)).cused = false := by
  cases hc : (C (id * mc + 1 + (C id).cchildren.length)).cused with
  | false => rfl
  | true =>
    exfalso
    have hmul : id ≤ id * mc := Nat.le_mul_of_pos_right _ (by omega)
    have hI0 : id * mc + 1 + (C id).cchildren.length ≠ 0 := by omega
    have hdiv : (id * mc + 1 + (C id).cchildren.length - 1) / mc = id := by
      have e : id * mc + 1 + (C id).cchildren.length - 1 = (C id).cchildren.length + mc * id := by
        rw [Nat.mul_comm]; omega
      rw [e, Nat.add_mul_div_left _ _ (by omega : 0 < mc), Nat.div_eq_of_lt hL]; omega
    have hp := h.cvalid_parent_id _ hc
    rw [if_neg hI0, hdiv] at hp
    have hm := h.cvalid_parents_child _ hc hI0
    rw [hp] at hm
    have := (h.cvalid_child_id_range id hu _ hm).2
    omega

/-- What `pt_new_spec` does when it is defined. -/
theorem pt_new_shape {num_id mc id q : Nat} {d p : PTData} {i : Nat}
    (hs : pt_new_spec num_id mc id q d = some (p, i)) :
    d.pg = true ∧ d.ipt = true ∧ (d.AC id).cused = true ∧ (d.AC id).cchildren.length < mc ∧
    i = id * mc + 1 + (d.AC id).cchildren.length ∧ i < num_id ∧
    p = { d with AC := setAt (setAt d.AC id ⟨(d.AC id).cquota, (d.AC id).cusage + q, (d.AC id).cparent,
      i :: (d.AC id).cchildren, (d.AC id).cused⟩) i ⟨q, 0, id, [], true⟩ } := by
  unfold pt_new_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true
  · rw [if_pos hc] at hs
    cases hsp : container_split_spec num_id mc id q d.toRData with
    | none => rw [hsp] at hs; cases hs
    | some pr =>
      obtain ⟨r1, i'⟩ := pr
      rw [hsp] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨hp, hi⟩ := hs
      subst hp; subst hi
      unfold container_split_spec at hsp
      simp only at hsp
      by_cases hc2 : (d.AC id).cused = true ∧ id * mc + 1 + (d.AC id).cchildren.length < num_id ∧
          (d.AC id).cchildren.length < mc ∧ q + (d.AC id).cusage ≤ (d.AC id).cquota
      · rw [if_pos hc2] at hsp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp
        obtain ⟨hr, hi⟩ := hsp
        subst hr; subst hi
        exact ⟨hc.1, hc.2, hc2.1, hc2.2.2.1, rfl, hc2.2.1, rfl⟩
      · rw [if_neg hc2] at hsp; cases hsp
  · rw [if_neg hc] at hs; cases hs

/-! ## The code -/

/-- `kctxt_new(entry, id, amt)`, result in `r`. -/
def kctxtNewK (cb mc num_proc : Nat) : Stmt KPrim :=
  .seq (mapS .base (ptNewS cb mc))
    (.ite (.bin .eq (.var "r") (.const (BitVec.ofNat 32 num_proc))) .skip
      (.seq (.call "_" .setSP [.var "r"]) (.call "_" .setRA [.var "r", .var "entry"])))

/-- `set_state(r, READY); enqueue(num_chan, r);` -/
def spawnTailS (tb qb num_proc num_chan : Nat) : Stmt APrim :=
  .seq (setTStateS tb (.var "r") (.const 0))
    (.seq (.assign "chan_index" (.const (BitVec.ofNat 32 num_chan)))
      (.seq (.assign "proc_index" (.var "r")) (enqueueS tb qb num_proc)))

/-- `thread_spawn(entry, id, amt)`, result in `r`. -/
def threadSpawnK (cb mc tb qb num_proc num_chan : Nat) : Stmt KPrim :=
  .seq (kctxtNewK cb mc num_proc) (mapS .base (spawnTailS tb qb num_proc num_chan))

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb

/-- **Passthrough.** A triple of the page-table layers holds in the state
with threads, queues and the current thread, if it writes only their cells
and keeps `pg`. -/
theorem liftPC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb)
    {P : Locals → PTData → Prop} {s : Stmt APrim} {Q : Locals → PTData → Locals → PTData → Prop}
    {F : Nat → Prop} (h : Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) F P s Q)
    (hF : ∀ k, F k → k < cb + 5 * num_id ∨ pb ≤ k)
    (hpg : ∀ σ d σ' d', P σ d → Q σ d σ' d' → d'.pg = d.pg) :
    Triple εR c i0 MC F (fun σ d => P σ d.toPTData) s
      (fun σ d σ' d' => ∃ p : PTData, d' = { d with toPTData := p } ∧ Q σ d.toPTData σ' p) := by
  intro σ l b d hlk hcs ⟨⟨q, hQ, hS, hR, hInv⟩, hcid⟩ hp
  have hSL := hL.qlay.tlay.slay
  have := hSL.hsb; have := hSL.hse; have := hL.qlay.tlay.htb; have := hL.qlay.tlay.hte
  have := hL.qlay.hqb; have := hL.qlay.hqe; have := hL.hcb; have := hL.hce
  have eP : d.toPTData = q.toPTData := congrArg SData.toPTData hS
  have hp' : P σ q.toPTData := eP ▸ hp
  obtain ⟨σ', l', b', p, hr, hcs', hA', hlk', hf, hq⟩ := h σ l b q.toPTData hlk hcs hQ.t.s.all hp'
  have hgap : ∀ k, cb + 5 * num_id ≤ k → k < pb → b' k = b k := fun k h1 h2 =>
    hf k (fun hk => by have := hF k hk; omega)
  have hq' : Q σ d.toPTData σ' p := by rw [eP]; exact hq
  refine ⟨σ', l', b', { d with toPTData := p }, hr, hcs',
    ⟨⟨({ q with toPTData := p } : QData), ⟨⟨⟨hA', fun q1 q2 g1 g2 => ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩,
      ?_, hR, fun hpg' => hInv ?_⟩, ?_⟩, hlk', hf, p, rfl, hq'⟩
  · have hlt := scell_lt (sb := sb) g1 g2 (show 2 < 3 by decide)
    have e : ∀ k, k < 3 → b' (scell sb num_proc q1 q2 k) = b (scell sb num_proc q1 q2 k) := fun k hk =>
      hgap _ (by unfold scell at *; omega) (by unfold scell at *; omega)
    show MatchSMS (q.smspool q1 q2) _ _ _
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
    exact hQ.t.s.sp q1 q2 g1 g2
  · show MatchTCB (q.tcb j) _ _ _
    rw [hgap _ (by unfold tcell; omega) (by unfold tcell; omega),
      hgap _ (by unfold tcell; omega) (by unfold tcell; omega),
      hgap _ (by unfold tcell; omega) (by unfold tcell; omega)]
    exact hQ.t.tp j hj
  · show MatchTDQ (q.tdq j) _ _
    rw [hgap _ (by unfold qcell; omega) (by unfold qcell; omega),
      hgap _ (by unfold qcell; omega) (by unfold qcell; omega)]
    exact hQ.qp j hj
  · show ({ d.toSData with toPTData := p } : SData) = { q.toSData with toPTData := p }
    rw [hS]
  · have e := hpg σ q.toPTData σ' p hp' hq
    show q.toPTData.pg = true
    rw [← e]; exact hpg'
  · show d.cid = (b' cidb).toNat
    rw [hgap cidb (by omega) (by omega)]; exact hcid

/-- `pt_new` in the state with the current thread. -/
theorem ptNewC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb)
    (hnum : cb + 5 * num_id < 2 ^ 32) {σ : Locals} {l : RLog} {b : Region} {d : CData} {mc id q : Nat}
    {p : PTData} {i : Nat} (hid : id < num_id) (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MC d b)
    (h1 : σ "id" = BitVec.ofNat 32 id) (h2 : σ "amt" = BitVec.ofNat 32 q)
    (hs : pt_new_spec num_id mc id q d.toPTData = some (p, i)) :
    ∃ σ' l' b', Runs (rprimsA εR c) (ptNewS cb mc) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MC ({ d with toPTData := p } : CData) b' ∧ σ' "lk" = σ "lk" ∧ σ' "r" = BitVec.ofNat 32 i := by
  have hT := liftPC εR c i0 hL (ptNew_triple εR c i0 hL.qlay.tlay.slay.lay hnum mc id q hid (ida := ida))
    (fun k hk => Or.inl hk.2)
    (fun σ d σ' d' _ hq => by
      obtain ⟨r, hq1, -⟩ := hq
      rw [(pt_new_shape hq1).2.2.2.2.2.2])
  obtain ⟨σ', l', b', d', hr, hcs', hM', hlk', -, p', hd', r, hq, hrr⟩ := hT σ l b d hlk hcs hM ⟨h1, h2, p, i, hs⟩
  rw [hs] at hq
  injection hq with e
  injection e with e1 e2
  subst e1; subst e2; subst hd'
  exact ⟨σ', l', b', hr, hcs', hM', hlk', hrr⟩

/-- **`kctxt_new` on the kernel machine.** -/
theorem kctxt_new_run (code : Nat → Stmt KPrim)
    (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hnn : num_id ≤ num_proc) {σ : Locals} {K : Cont KPrim} {l : RLog}
    {b : Region} {d d' : KData} {mc entry id q i : Nat} (hid : id < num_id) (hent : entry < 2 ^ 32)
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MC d.toCData b)
    (h1 : σ "id" = BitVec.ofNat 32 id) (h2 : σ "amt" = BitVec.ofNat 32 q)
    (h3 : σ "entry" = BitVec.ofNat 32 entry)
    (hs : kctxt_new_spec num_id mc code entry id q d = some (d', i)) :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      KStar εR c code ⟨⟨kctxtNewK cb mc num_proc, K, σ⟩, d.kctxt, l⟩ ⟨⟨.skip, K, σ'⟩, d'.kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MC d'.toCData b' ∧ σ' "lk" = σ "lk" ∧ σ' "r" = BitVec.ofNat 32 i := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL.qlay
  unfold kctxt_new_spec at hs
  cases hp : pt_new_spec num_id mc id q d.toPTData with
  | none => rw [hp] at hs; cases hs
  | some pr =>
    obtain ⟨p, i'⟩ := pr
    rw [hp] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hd, hi⟩ := hs
    subst hd; subst hi
    obtain ⟨-, -, -, -, -, hilt, -⟩ := pt_new_shape hp
    obtain ⟨σ1, l1, b1, hr, hcs1, hM1, hlk1, hr1⟩ := ptNewC εR c i0 hL hnum hid hlk hcs hM h1 h2 hp
    have hent1 : σ1 "entry" = BitVec.ofNat 32 entry := (hr.frame rfl).trans h3
    have hg : (Expr.bin .eq (.var "r") (.const (BitVec.ofNat 32 num_proc))).eval σ1 = 0 :=
      eqc_false hr1 (by omega) hnp (by omega)
    have er : ((Expr.var "r").eval σ1).toNat = i' := by
      show (σ1 "r").toNat = _
      rw [hr1, tn (by omega)]
    have er' : ((Expr.var "r").eval (σ1.set "_" 0)).toNat = i' := by
      show ((σ1.set "_" 0) "r").toNat = _
      rw [Locals.set_other _ _ (by decide), hr1, tn (by omega)]
    have ee : ((Expr.var "entry").eval (σ1.set "_" 0)).toNat = entry := by
      show ((σ1.set "_" 0) "entry").toNat = _
      rw [Locals.set_other _ _ (by decide), hent1, tn hent]
    have k1 := kstar_seq (εR := εR) (c := c) (code := code) hr
      (.ite (.bin .eq (.var "r") (.const (BitVec.ofNat 32 num_proc))) .skip
        (.seq (.call "_" .setSP [.var "r"]) (.call "_" .setRA [.var "r", .var "entry"]))) K d.kctxt
    have k2 : kstep εR c code ⟨⟨.ite (.bin .eq (.var "r") (.const (BitVec.ofNat 32 num_proc))) .skip
        (.seq (.call "_" .setSP [.var "r"]) (.call "_" .setRA [.var "r", .var "entry"])), K, σ1⟩, d.kctxt, l1⟩ =
        some ⟨⟨.seq (.call "_" .setSP [.var "r"]) (.call "_" .setRA [.var "r", .var "entry"]), K, σ1⟩,
          d.kctxt, l1⟩ := by
      rw [kstep_ite, if_pos hg]
    have k3 := kstep_seq (εR := εR) (c := c) (code := code) (.call "_" .setSP [.var "r"])
      (.call "_" .setRA [.var "r", .var "entry"]) K σ1 d.kctxt l1
    have k4 := kstep_setSP (εR := εR) (c := c) (code := code) "_" (.var "r")
      (.seq (.call "_" .setRA [.var "r", .var "entry"]) K) σ1 d.kctxt l1
    rw [er] at k4
    have k5 := kstep_skip_seq (εR := εR) (c := c) (code := code) (.call "_" .setRA [.var "r", .var "entry"]) K
      (σ1.set "_" 0) (setAt d.kctxt i' { d.kctxt i' with cont := .stop }) l1
    have k6 := kstep_setRA (εR := εR) (c := c) (code := code) "_" (.var "r") (.var "entry") K (σ1.set "_" 0)
      (setAt d.kctxt i' { d.kctxt i' with cont := .stop }) l1
    rw [er', ee, setAt_eq, setAt_setAt] at k6
    refine ⟨(σ1.set "_" 0).set "_" 0, l1, b1,
      k1.trans (.step k2 (.step k3 (.step k4 (.step k5 (.single k6))))), hcs1, hM1, ?_, ?_⟩
    · simp [Locals.set, hlk1]
    · simp [Locals.set, hr1]

/-- **`thread_spawn` on the kernel machine.** -/
theorem thread_spawn_run (code : Nat → Stmt KPrim)
    (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hnn : num_id ≤ num_proc) {σ : Locals} {K : Cont KPrim} {l : RLog}
    {b : Region} {d d' : KData} {mc entry id q i : Nat} (hid : id < num_id) (hent : entry < 2 ^ 32)
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MC d.toCData b)
    (h1 : σ "id" = BitVec.ofNat 32 id) (h2 : σ "amt" = BitVec.ofNat 32 q)
    (h3 : σ "entry" = BitVec.ofNat 32 entry) (hI : AInv num_proc num_chan d.toAData)
    (hCV : Container_valid num_id mc d.AC)
    (hs : thread_spawn_spec num_id mc num_chan code entry id q d = some (d', i)) :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      KStar εR c code ⟨⟨threadSpawnK cb mc tb qb num_proc num_chan, K, σ⟩, d.kctxt, l⟩
        ⟨⟨.skip, K, σ'⟩, d'.kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MC d'.toCData b' ∧ σ' "lk" = σ "lk" ∧ σ' "r" = BitVec.ofNat 32 i ∧
      AInv num_proc num_chan d'.toAData := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL.qlay
  unfold thread_spawn_spec at hs
  cases hk : kctxt_new_spec num_id mc code entry id q d with
  | none => rw [hk] at hs; cases hs
  | some pr =>
    obtain ⟨d1, i'⟩ := pr
    rw [hk] at hs
    simp only at hs
    cases hq : d1.abq num_chan with
    | AbQUndef => rw [hq] at hs; cases hs
    | AbQValid ql =>
      rw [hq] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨hd, hi⟩ := hs
      subst hd; subst hi
      -- what `kctxt_new` did
      have hk0 := hk
      unfold kctxt_new_spec at hk
      cases hp : pt_new_spec num_id mc id q d.toPTData with
      | none => rw [hp] at hk; cases hk
      | some pr =>
        obtain ⟨p, i''⟩ := pr
        rw [hp] at hk
        simp only [Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hd1, hi1⟩ := hk
        have hi1' := hi1.symm
        subst hi1'
        obtain ⟨hpg, hipt, hu, hLen, hi, hilt, hpe⟩ := pt_new_shape hp
        have hi'lt : i' < num_proc := by omega
        have hfree : (d.AC i').cused = false := by rw [hi]; exact split_child_free hCV hu hLen
        have hidne : i' ≠ id := by
          have hmul : id ≤ id * mc := Nat.le_mul_of_pos_right _ (by omega)
          omega
        -- the child's control block
        have hv := hI.tc i' hi'lt
        cases hai : d.abtcb i' with
        | AbTCBUndef => rw [hai] at hv; exact hv.elim
        | AbTCBValid st b0 =>
          have hb0 : b0 = -1 := hI.niq i' st b0 hi'lt hfree hai
          subst hb0
          -- facts about the state after `kctxt_new`
          have e1 : d1.toPTData = p := by rw [← hd1]
          have epg : d1.pg = true := by
            show d1.toPTData.pg = true
            rw [e1, hpe]; exact hpg
          have eipt : d1.ipt = true := by
            show d1.toPTData.ipt = true
            rw [e1, hpe]; exact hipt
          have eAC : ∀ j, (d1.AC j).cused = if j = i' then true else (d.AC j).cused := by
            intro j
            show (d1.toPTData.AC j).cused = _
            rw [e1, hpe]
            show (setAt (setAt d.AC id _) i' _ j).cused = _
            by_cases ej : j = i'
            · rw [if_pos ej, ej, setAt_eq]
            · rw [if_neg ej, setAt_ne _ _ ej]
              by_cases ej2 : j = id
              · rw [ej2, setAt_eq]
              · rw [setAt_ne _ _ ej2]
          have etcb : d1.abtcb = d.abtcb := by rw [← hd1]
          have eabq : d1.abq = d.abq := by rw [← hd1]
          have hI1 : AInv num_proc num_chan d1.toAData := by
            refine ⟨by show AbTCBCorrect_range _ _ d1.abtcb; rw [etcb]; exact hI.tc,
              by show AbQCorrect_range _ _ d1.abq; rw [eabq]; exact hI.qc, ?_,
              by show QCount _ _ d1.abtcb d1.abq; rw [etcb, eabq]; exact hI.cnt,
              by show InQ _ _ d1.abtcb d1.abq; rw [etcb, eabq]; exact hI.inq⟩
            intro j s b' hj hcu hjt
            have hjt' : d.abtcb j = .AbTCBValid s b' := by rw [← etcb]; exact hjt
            have hcu' : (d1.AC j).cused = false := hcu
            rw [eAC] at hcu'
            by_cases ej : j = i'
            · rw [if_pos ej] at hcu'; cases hcu'
            · rw [if_neg ej] at hcu'; exact hI.niq j s b' hj hcu' hjt'
          have hcu1 : (d1.AC i').cused = true := by rw [eAC, if_pos rfl]
          have hai1 : d1.abtcb i' = .AbTCBValid st (-1) := by rw [etcb]; exact hai
          obtain ⟨a1, hss, henq⟩ := park_factors (np := num_proc) (nc := num_chan) (a := d1.toAData)
            (cid := i') (q := num_chan) (sv := 0) (ts := .READY) epg eipt hi'lt (Nat.le_refl _) hcu1 hai1 rfl hq
          -- the machine run
          obtain ⟨σ1, l1, b1, hks, hcs1, hM1, hlk1, hr1⟩ := kctxt_new_run εR c i0 code hL hnum hnn
            (K := .seq (mapS .base (spawnTailS tb qb num_proc num_chan)) K) hid hent hlk hcs hM h1 h2 h3 hk0
          have hlk1' : (σ1 "lk").toNat = i0 := by rw [hlk1]; exact hlk
          obtain ⟨l2, b2, r2, c2, m2⟩ := setStateC εR c i0 hL (σ := σ1) (ie := .var "r") (ve := .const 0)
            (n := i') (sv := 0) hlk1' hcs1 hM1 hr1 rfl hss
          have hI2 := set_state0_keeps hss hI1
          obtain ⟨σ3, l3, b3, r3, c3, m3, k3⟩ := enqueueC εR c i0 hL
            (σ := ((σ1.set "_" 0).set "chan_index" (BitVec.ofNat 32 num_chan)).set "proc_index"
              (BitVec.ofNat 32 i')) (n := num_chan) (i := i')
            (by simpa [Locals.set] using hlk1') c2 m2 (by simp [Locals.set]) (by simp [Locals.set]) hI2 henq
          have hr3 : σ3 "r" = BitVec.ofNat 32 i' := by
            rw [r3.frame rfl]; simp [Locals.set, hr1]
          have htail : Runs (rprimsA εR c) (spawnTailS tb qb num_proc num_chan) σ1 l1 σ3 l3 :=
            Runs.seq r2 (Runs.seq (Runs.assign _ _) (Runs.seq
              (asg_run "proc_index" (.var "r") (by simp [Expr.eval, Locals.set, hr1])) r3))
          refine ⟨σ3, l3, b3, ?_, c3, m3, by rw [k3]; simp [Locals.set, hlk1], hr3, enqueue0_keeps henq hI2⟩
          exact (KStar.single (kstep_seq _ _ K σ d.kctxt l)).trans
            (hks.trans ((KStar.single (kstep_skip_seq _ K σ1 d1.kctxt l1)).trans (kstar_base htail K d1.kctxt)))

end Code

end PSched
