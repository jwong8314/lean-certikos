import CertiKOS.TInv
import CertiKOS.SecurityBigstep

/-!
# The security invariants, carried from one trap to the next

The security proof (`Security`, `SecurityBigstep`) assumes `SecInv` of every
state where it uses integrity or confidentiality. mCertiKOS proves those
invariants preserved (`secure_inv_preserved`). Here:

* `PUp`: what an operation does to the memory model that the invariants
  read: every page a process maps stays in use (`MappedUsed`), and a free
  page still holds nothing (`FreeNone`). `alloc_up`, `allocPDE_up`,
  `insertPTE_up`, `ptInsert_up`, `ptResv_up`: a reservation is such an
  operation.
* `yield_kinv`: **a yield keeps the kernel invariant**, at the level of the
  specifications (from `park_factors` and `sched_factors`).
* `kpass_keeps`: **every passage through the kernel keeps `KInv`**, and ends
  in user mode.
* `kpass_secinv`: **every passage keeps `SecInv`**, given `KInv`.
* `IdleU`, `BStepU`, `ExecU`: the executions of `SecurityBigstep` without the
  invariant as a premise of each step. `execU_exec`: from a state with
  `KInv` and `SecInv`, such an execution is one of `SecurityBigstep`'s.
* `noninterference_inv`: **noninterference, assuming the invariants only of
  the first states.**
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TInv

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt PProc TTrap TSysCall MMInv Security

/-! ## Reservations and the memory invariants -/

/-- The memory invariants survive. -/
def PUp (d d' : PTData) : Prop := (∀ j, MappedUsed j d → MappedUsed j d') ∧ (FreeNone d → FreeNone d')

theorem PUp.refl (d : PTData) : PUp d d := ⟨fun _ h => h, fun h => h⟩

theorem PUp.trans {d1 d2 d3 : PTData} (h1 : PUp d1 d2) (h2 : PUp d2 d3) : PUp d1 d3 :=
  ⟨fun j h => h2.1 j (h1.1 j h), fun h => h2.2 (h1.2 h)⟩

theorem notFree_used {AT : ATable} {v c0 : Nat} : NotFree (setAt AT v (.ATValid true .ATNorm c0)) v := by
  intro c; rw [setAt_eq]; intro h; cases h

/-- A page made used: the free pages are fewer. -/
theorem free_of_set {AT : ATable} {x v c0 c : Nat} (h : setAt AT x (.ATValid true .ATNorm c0) v = .ATValid false .ATNorm c) :
    v ≠ x ∧ AT v = .ATValid false .ATNorm c := by
  by_cases e : v = x
  · rw [e, setAt_eq] at h; cases h
  · rw [setAt_ne _ _ e] at h; exact ⟨e, h⟩

theorem alloc_up {n : Nat} {d : PTData} {r1 : RData} {b : Nat} (h : container_alloc_spec n d.toRData = some (r1, b)) :
    PUp d { d with toRData := r1 } := by
  unfold container_alloc_spec at h
  simp only at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
       first
         | exact PUp.refl _
         | (refine ⟨fun j hm k pi pte hp m w p hw => notFree_set (hm k pi pte hp m w p hw), fun hf v c hv a ha => ?_⟩
            exact hf v c (free_of_set hv).2 a ha); done)
    | cases h

theorem allocPDE_up {np nn vadr : Nat} {d d' : PTData} {v : Nat} (h : ptAllocPDE_spec np nn vadr d = some (d', v)) :
    PUp d d' := by
  unfold ptAllocPDE_spec at h
  simp only at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
       first
         | exact PUp.refl _
         | (rename_i pi _
            refine ⟨fun j hm k pi' pte hp m w p hw => ?_, fun hf v' c hv a ha => ?_⟩
            · apply notFree_set
              by_cases ej : j = nn
              · subst ej
                have hp' : setAt (d.ptpool j) (PDX vadr) (.PDEValid pi real_init_PTE) k = .PDEValid pi' pte := by
                  have := hp; simp only [setAt_eq] at this; exact this
                by_cases ek : k = PDX vadr
                · subst ek; rw [setAt_eq] at hp'; injection hp' with e1 e2; subst e2
                  simp only [real_init_PTE, initPTE] at hw; split at hw <;> cases hw
                · rw [setAt_ne _ _ ek] at hp'; exact hm k pi' pte hp' m w p hw
              · have hp' : d.ptpool j k = .PDEValid pi' pte := by
                  have := hp; simp only [setAt_ne _ _ ej] at this; exact this
                exact hm k pi' pte hp' m w p hw
            · obtain ⟨hne, hv0⟩ := free_of_set hv
              show free_page pi d.HP a = none
              unfold free_page; split
              · rfl
              · exact hf v' c hv0 a ha); done)
    | cases h

theorem insertPTE_up {nn vadr padr : Nat} {p : PTPerm} {d d' : PTData} (h : ptInsertPTE_spec nn vadr padr p d = some d') :
    PUp d d' := by
  unfold ptInsertPTE_spec at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h
       rename_i pi pdt hpd _ _ c _ _
       refine ⟨fun j hm k pi' pte hp m w p' hw => ?_, fun hf v' c' hv a ha => hf v' c' (free_of_set hv).2 a ha⟩
       by_cases ej : j = nn
       · subst ej
         have hp' : setAt (d.ptpool j) (PDX vadr) (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid padr p))) k =
             .PDEValid pi' pte := by
           have := hp; simp only [setAt_eq] at this; exact this
         by_cases ek : k = PDX vadr
         · subst ek; rw [setAt_eq] at hp'; injection hp' with e1 e2; subst e2
           by_cases em : m = PTX vadr
           · subst em; rw [setAt_eq] at hw; injection hw with e3 e4; subst e3; exact notFree_used
           · rw [setAt_ne _ _ em] at hw; exact notFree_set (hm _ pi pdt hpd m w p' hw)
         · rw [setAt_ne _ _ ek] at hp'; exact notFree_set (hm k pi' pte hp' m w p' hw)
       · have hp' : d.ptpool j k = .PDEValid pi' pte := by
           have := hp; simp only [setAt_ne _ _ ej] at this; exact this
         exact notFree_set (hm k pi' pte hp' m w p' hw); done)
    | cases h

theorem ptInsert_up {mp np nn vadr padr perm : Nat} {d d' : PTData} {r : Nat}
    (h : ptInsert_spec mp np nn vadr padr perm d = some (d', r)) : PUp d d' := by
  unfold ptInsert_spec at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i d2 hi
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          exact insertPTE_up hi
        · cases h
      · split at h
        · rename_i d2 v ha
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
            exact allocPDE_up ha
          · split at h
            · rename_i d3 hi
              simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
              exact (allocPDE_up ha).trans (insertPTE_up hi)
            · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem ptResv_up {mp np n vadr perm : Nat} {d d' : PTData} {r : Nat}
    (h : ptResv_spec mp np n vadr perm d = some (d', r)) : PUp d d' := by
  unfold ptResv_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h; simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact PUp.refl _
    · exact (alloc_up hA).trans (ptInsert_up h)

/-! ## The yield, at the level of the specifications -/

section
variable {num_id mc num_proc num_chan maxpage kl kh : Nat}

local notation "KI" => KInv num_id mc num_proc num_chan maxpage kl kh

/-- **A yield keeps the kernel invariant.** -/
theorem yield_kinv {rs : UContext} {d d1 : UData} {ql : List Nat} {la : Nat} {rsK : KCtx}
    (h1 : proc_exit_user_spec rs d = some d1) (hq : d.abq num_chan = .AbQValid ql) (hla : ql.getLastD num_proc = la)
    (hnp : la ≠ num_proc) (hI : KI d) : KI (putK d1 (yieldOut num_chan la ql rsK (toK d1))) := by
  obtain ⟨hd1, hpg⟩ := exit_shape h1
  subst hd1
  have hmem := last_mem hla hnp
  have hlt : la < num_proc := q_lt hI.ainv.qc (Nat.le_refl _) hq hmem
  obtain ⟨s, hai⟩ := hI.ainv.inq la num_chan ql hlt (Nat.le_refl _) hq hmem
  have hcu := cused_of_inq hI.ainv hlt hai
  have hne2 : d.cid ≠ la := by
    intro e
    have h := hI.cur.2
    rw [e, hai] at h
    injection h with e1 e2
    omega
  -- park the caller, then schedule `la`
  let D1 : UData := { d with ikern := true, PT := 0, ipt := true, uctxt := setAt d.uctxt d.cid rs }
  have hipt : D1.ipt = true := rfl
  obtain ⟨a1, hss, henq⟩ := park_factors (np := num_proc) (nc := num_chan) (a := (toK D1).toAData) (cid := d.cid)
    (q := num_chan) (sv := 0) (ts := .READY) hpg hipt hI.cid (Nat.le_refl _) hI.cur.1 hI.cur.2 rfl hq
  have hA0 : AInv num_proc num_chan (toK D1).toAData := ⟨hI.ainv.tc, hI.ainv.qc, hI.ainv.niq, hI.ainv.cnt, hI.ainv.inq⟩
  have hP := enqueue0_keeps henq (set_state0_keeps hss hA0)
  let A := { (toK D1).toAData with
    abtcb := setAt (toK D1).abtcb d.cid (.AbTCBValid .READY num_chan)
    abq := setAt (toK D1).abq num_chan (.AbQValid (d.cid :: ql)) }
  have hai' : A.abtcb la = .AbTCBValid s num_chan := by
    show setAt d.abtcb d.cid _ la = _; rw [setAt_ne _ _ (Ne.symm hne2)]; exact hai
  obtain ⟨a2, hdq, hst⟩ := sched_factors (np := num_proc) (nc := num_chan) (a := A) (ql := d.cid :: ql) (la := la)
    hpg hipt (setAt_eq _ _ _) (last_cons hla hnp _) hnp hlt hcu hai'
  have hY := set_state0_keeps hst (dequeue0_keeps hdq hP).1
  refine ⟨hlt, ⟨hcu, ?_⟩, ?_, hI.cv, hI.atinv, hI.uq, hpg, hI.ihost, hI.init⟩
  · show setAt (setAt d.abtcb d.cid _) la _ la = _
    rw [setAt_eq]
  · have e : (yieldOut num_chan la ql rsK (toK D1)).toAData = { A with
        abtcb := setAt A.abtcb la (.AbTCBValid .RUN (-1))
        abq := setAt A.abq num_chan (.AbQValid (remove la (d.cid :: ql))) } :=
      AData.ext3 rfl rfl (by show setAt d.abq num_chan _ = setAt (setAt d.abq num_chan _) num_chan _; rw [setAt_setAt]; rfl)
    show AInv num_proc num_chan (yieldOut num_chan la ql rsK (toK D1)).toAData
    rw [e]; exact hY

end

/-! ## Every passage keeps the invariants -/

/-- What a passage does to what `SecInv` reads. -/
def SecMono (d d' : UData) : Prop :=
  (∀ j, (d.AC j).cused = true → (d'.AC j).cused = true) ∧ PUp d.toPTData d'.toPTData

theorem SecMono.refl (d : UData) : SecMono d d := ⟨fun _ h => h, PUp.refl _⟩

theorem SecMono.trans {d1 d2 d3 : UData} (h1 : SecMono d1 d2) (h2 : SecMono d2 d3) : SecMono d1 d3 :=
  ⟨fun j h => h2.1 j (h1.1 j h), h1.2.trans h2.2⟩

theorem setReg_mono {reg n : Nat} {d d' : UData} (h : uctx_set_reg_spec reg n d = some d') : SecMono d d' := by
  obtain ⟨U, e⟩ := set_reg_shape h; subst e; exact SecMono.refl _

theorem exit_mono {rs : UContext} {d d1 : UData} (h : proc_exit_user_spec rs d = some d1) : SecMono d d1 := by
  obtain ⟨e, -⟩ := exit_shape h; subst e; exact ⟨fun _ h => h, fun _ h => h, fun h => h⟩

theorem start_mono {d d' : UData} {rs : UContext} (h : proc_start_user_spec d = some (d', rs)) : SecMono d d' := by
  obtain ⟨e, -, -⟩ := start_shape h; subst e; exact ⟨fun _ h => h, fun _ h => h, fun h => h⟩

theorem create_mono {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart uentry q : Nat} {d d' : UData}
    {i : Nat} (hs : proc_create_spec num_id mc num_chan code pstart uentry q d = some (d', i)) : SecMono d d' := by
  unfold proc_create_spec at hs
  simp only at hs
  split at hs
  · cases hq : d.abq num_chan with
    | AbQUndef => rw [hq] at hs; cases hs
    | AbQValid l =>
      rw [hq] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨fun j hj => ?_, fun _ h => h, fun h => h⟩
      show (setAt (setAt d.AC d.cid _) _ _ j).cused = true
      by_cases e1 : j = d.cid * mc + 1 + (d.AC d.cid).cchildren.length
      · rw [e1, setAt_eq]
      · rw [setAt_ne _ _ e1]
        by_cases e2 : j = d.cid
        · rw [e2, setAt_eq]; rw [e2] at hj; exact hj
        · rw [setAt_ne _ _ e2]; exact hj
  · cases hs

theorem dispatch_mono {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
    {d d' : UData} (hs : sys_dispatch_c_spec num_id mc num_chan code pstart elf d = some d') : SecMono d d' := by
  unfold sys_dispatch_c_spec at hs
  cases e1 : uctx_arg1_spec d with
  | none => rw [e1] at hs; cases hs
  | some a =>
    rw [e1] at hs; simp only at hs
    by_cases h2 : a = 2
    · rw [if_pos h2] at hs
      unfold trap_proc_create_spec at hs
      repeat' split at hs
      all_goals first
        | exact setReg_mono hs
        | exact (create_mono ‹proc_create_spec _ _ _ _ _ _ _ _ = some _›).trans
            ((setReg_mono ‹uctx_set_retval1_spec _ _ = some _›).trans (setReg_mono hs))
        | cases hs
    · rw [if_neg h2] at hs
      by_cases h26 : a = 26
      · rw [if_pos h26] at hs
        obtain ⟨U, e⟩ := get_quota_shape hs
        subst e
        exact SecMono.refl _
      · rw [if_neg h26] at hs
        exact setReg_mono hs

theorem pgf_mono {maxpage num_proc vadr : Nat} {d d' : UData} (hs : ptfault_resv_spec maxpage num_proc vadr d = some d') :
    SecMono d d' := by
  unfold ptfault_resv_spec at hs
  split at hs
  · split at hs
    · cases hr : ptResv_spec maxpage num_proc d.cid vadr 7 d.toPTData with
      | none => rw [hr] at hs; cases hs
      | some pr =>
        obtain ⟨p, r⟩ := pr
        rw [hr] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        obtain ⟨hm, -, -⟩ := ptResv_facts hr
        exact ⟨fun j hj => by
          show (p.AC j).cused = true
          rw [(hm j).2.2.2.1]; exact hj, ptResv_up hr⟩
    · simp only [Option.some.injEq] at hs; subst hs; exact SecMono.refl _
  · cases hs

section
variable {num_id mc num_proc num_chan maxpage kl kh : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
  {elf : Nat → Nat}

local notation "KI" => KInv num_id mc num_proc num_chan maxpage kl kh
local notation "KP" => KPass num_id mc num_chan num_proc maxpage code pstart elf

/-- **Every passage through the kernel keeps `KInv`**, ends in user mode, and
keeps what `SecInv` reads. -/
theorem kpass_keeps (hnn : num_id ≤ num_proc) {t : Trap} {d d' : UData} {rs' : UContext} (hp : KP t d d' rs')
    (hI : KI d) : KI d' ∧ d'.ikern = false ∧ SecMono d d' := by
  cases hp with
  | syscall h1 h2 h3 =>
    obtain ⟨k, e⟩ := start_keeps h3 (dispatch_keeps hnn h2 (exit_keeps h1 hI))
    exact ⟨k, e, (exit_mono h1).trans ((dispatch_mono h2).trans (start_mono h3))⟩
  | pgf h1 h2 h3 =>
    obtain ⟨k, e⟩ := start_keeps h3 (pgf_keeps h2 (exit_keeps h1 hI))
    exact ⟨k, e, (exit_mono h1).trans ((pgf_mono h2).trans (start_mono h3))⟩
  | yield h1 hq hla hne h3 hnp =>
    obtain ⟨k, e⟩ := start_keeps h3 (yield_kinv h1 hq hla hnp hI)
    refine ⟨k, e, (exit_mono h1).trans (SecMono.trans ?_ (start_mono h3))⟩
    exact ⟨fun _ h => h, fun _ h => h, fun h => h⟩

/-- **Every passage keeps `SecInv`.** -/
theorem kpass_secinv (hnn : num_id ≤ num_proc) {i : Nat} {t : Trap} {d d' : UData} {rs' : UContext}
    (hp : KP t d d' rs') (hI : KI d) (hS : SecInv num_id mc i d) : KI d' ∧ SecInv num_id mc i d' := by
  obtain ⟨hK, -, hm⟩ := kpass_keeps hnn hp hI
  exact ⟨hK, ⟨hK.cv, hK.cur.1, hm.1 i hS.obs, hm.2.1 i hS.mu, hm.2.2 hS.fn, hK.init, hK.ihost⟩⟩

end

/-! ## Executions without the invariants as premises -/

section Exec
variable (num_id mc num_chan num_proc maxpage : Nat) (code : Nat → Stmt KPrim) (pstart : Nat) (elf : Nat → Nat)
variable (i : Nat)

/-- Passages of other processes while `i` is parked. -/
inductive IdleU : UData → UData → Prop
  | refl (d : UData) : IdleU d d
  | step {t : Trap} {d d1 d2 : UData} {rs : UContext}
      (hp : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d1 rs) (h1 : i ≠ d.cid) (h2 : i ≠ d1.cid)
      (hrest : IdleU d1 d2) : IdleU d d2

/-- A big step of process `i`. -/
inductive BStepU : Trap → UData → UData → UContext → Prop
  | stay {t : Trap} {d d' : UData} {r : UContext} (hp : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d' r)
      (hi : i = d.cid) (hi' : i = d'.cid) : BStepU t d d' r
  | away {t t2 : Trap} {d d1 d2 d' : UData} {r1 r : UContext}
      (hp : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d1 r1) (hi : i = d.cid) (h1 : i ≠ d1.cid)
      (hidle : IdleU num_id mc num_chan num_proc maxpage code pstart elf i d1 d2) (hp2 : KPass num_id mc num_chan num_proc maxpage code pstart elf t2 d2 d' r)
      (h2 : i ≠ d2.cid) (hi' : i = d'.cid) : BStepU t d d' r

/-- An execution of process `i` running program `P`. -/
inductive ExecU (P : Prog) : Nat → UData → UContext → UData → UContext → Prop
  | zero (d : UData) (r : UContext) : ExecU P 0 d r d r
  | succ {n : Nat} {d d1 d' : UData} {r r1 r' : UContext}
      (hb : BStepU num_id mc num_chan num_proc maxpage code pstart elf i (P r (observe i d)) d d1 r1)
      (hrest : ExecU P n d1 r1 d' r') : ExecU P (n + 1) d r d' r'

end Exec

section
variable {num_id mc num_proc num_chan maxpage kl kh : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
  {elf : Nat → Nat} {i : Nat}

local notation "KI" => KInv num_id mc num_proc num_chan maxpage kl kh

theorem idleU_idle (hnn : num_id ≤ num_proc) {d d' : UData}
    (h : IdleU num_id mc num_chan num_proc maxpage code pstart elf i d d') :
    KI d → SecInv num_id mc i d → Idle num_id mc num_chan num_proc maxpage code pstart elf i d d' ∧ KI d' ∧
      SecInv num_id mc i d' := by
  induction h with
  | refl d => exact fun hK hS => ⟨.refl d, hK, hS⟩
  | step hp h1 h2 _ ih =>
    intro hK hS
    obtain ⟨hK1, hS1⟩ := kpass_secinv hnn hp hK hS
    obtain ⟨hI, hK2, hS2⟩ := ih hK1 hS1
    exact ⟨.step hS hp h1 h2 hI, hK2, hS2⟩

theorem bstepU_bstep (hnn : num_id ≤ num_proc) {t : Trap} {d d' : UData} {r : UContext}
    (h : BStepU num_id mc num_chan num_proc maxpage code pstart elf i t d d' r) (hK : KI d)
    (hS : SecInv num_id mc i d) :
    BStep num_id mc num_chan num_proc maxpage code pstart elf i t d d' r ∧ KI d' ∧ SecInv num_id mc i d' := by
  cases h with
  | stay hp hi hi' =>
    obtain ⟨hK1, hS1⟩ := kpass_secinv hnn hp hK hS
    exact ⟨.stay hS hp hi hi', hK1, hS1⟩
  | away hp hi h1 hidle hp2 h2 hi' =>
    obtain ⟨hK1, hS1⟩ := kpass_secinv hnn hp hK hS
    obtain ⟨hI, hK2, hS2⟩ := idleU_idle hnn hidle hK1 hS1
    obtain ⟨hK3, hS3⟩ := kpass_secinv hnn hp2 hK2 hS2
    exact ⟨.away hS hp hi h1 hI hS2 hp2 h2 hi', hK3, hS3⟩

/-- **An execution from a state with the invariants is one of
`SecurityBigstep`'s**: the invariants hold at every step. -/
theorem execU_exec (hnn : num_id ≤ num_proc) {P : Prog} :
    ∀ {n : Nat} {d d' : UData} {r r' : UContext},
      ExecU num_id mc num_chan num_proc maxpage code pstart elf i P n d r d' r' → KI d → SecInv num_id mc i d →
      Exec num_id mc num_chan num_proc maxpage code pstart elf i P n d r d' r' ∧ KI d' ∧ SecInv num_id mc i d'
  | _, _, _, _, _, .zero d r, hK, hS => ⟨.zero d r, hK, hS⟩
  | _, _, _, _, _, .succ hb hrest, hK, hS => by
    obtain ⟨hb', hK1, hS1⟩ := bstepU_bstep hnn hb hK hS
    obtain ⟨hx, hK2, hS2⟩ := execU_exec hnn hrest hK1 hS1
    exact ⟨.succ hb' hx, hK2, hS2⟩

/-- **Noninterference, with the invariants assumed only of the first
states.** -/
theorem noninterference_inv (hnn : num_id ≤ num_proc) (P : Prog) {n : Nat} {d e d' e' : UData} {r rd re : UContext}
    (x1 : ExecU num_id mc num_chan num_proc maxpage code pstart elf i P n d r d' rd)
    (x2 : ExecU num_id mc num_chan num_proc maxpage code pstart elf i P n e r e' re)
    (hKd : KI d) (hSd : SecInv num_id mc i d) (hKe : KI e) (hSe : SecInv num_id mc i e) (h : ObsEq i d e) :
    ObsEq i d' e' ∧ rd = re :=
  noninterference P n (execU_exec hnn x1 hKd hSd).1 (execU_exec hnn x2 hKe hSe).1 h

end

end TInv
