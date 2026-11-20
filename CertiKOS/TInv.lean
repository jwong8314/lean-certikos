import CertiKOS.TSysCall
import CertiKOS.MMInv

/-!
# The kernel's invariant, from one trap to the next

The entry points of `TSysCall` (`syscall_dispatch`, `pgf_handler`,
`sys_yield`) assume of the state at the trap what mCertiKOS keeps as
invariants: the current thread is a valid running process, the queue and
container invariants hold, the allocation table is consistent and every
container is within its quota. Here those assumptions become one invariant,
`KInv`, and every passage through the kernel is shown to re-establish it, so
that it holds at the next trap.

* `KInv`: the invariant of a state in user mode.
* `exit_keeps`, `start_keeps`: the two mode switches keep it.
* `create_keeps`: `proc_create` keeps it (the new child's container comes
  from a split of the caller's, and the child is put on the ready queue).
* `dispatch_keeps`: **`sys_dispatch_c_spec` keeps it**, for every number.
* `ptResv_facts`, `pgf_keeps`: **`ptfault_resv_spec` keeps it** (a
  reservation raises usages within quota, and changes nothing else about the
  containers).

The machine-level theorems are in `TInvRun.lean`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TInv

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt PProc TTrap TSysCall MMInv

/-- **The invariant at a trap.** -/
structure KInv (num_id mc num_proc num_chan maxpage kl kh : Nat) (d : UData) : Prop where
  cid : d.cid < num_proc
  cur : CurIDValid d.toCData
  ainv : AInv num_proc num_chan d.toAData
  cv : Container_valid num_id mc d.AC
  atinv : ATInv maxpage kl kh d.toPData
  uq : UQ d.AC
  pg : d.pg = true
  ihost : d.ihost = true
  init : d.init = true

section
variable {num_id mc num_proc num_chan maxpage kl kh : Nat}

local notation "KI" => KInv num_id mc num_proc num_chan maxpage kl kh

/-- The invariant reads only these fields. -/
theorem KInv.congr {d d' : UData} (h : KI d) (e1 : d'.cid = d.cid) (e2 : d'.abtcb = d.abtcb)
    (e3 : d'.abq = d.abq) (e4 : d'.AC = d.AC) (e5 : d'.toPData = d.toPData) (e6 : d'.pg = d.pg)
    (e7 : d'.ihost = d.ihost) : KI d' := by
  have hinit : d'.init = d.init := by
    show d'.toPData.init = d.toPData.init
    rw [e5]
  refine ⟨by rw [e1]; exact h.cid, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [e4]; exact h.cv,
    by rw [e5]; exact h.atinv, by rw [e4]; exact h.uq, by rw [e6]; exact h.pg, by rw [e7]; exact h.ihost,
    by rw [hinit]; exact h.init⟩
  · show (d'.AC d'.cid).cused = true
    rw [e4, e1]; exact h.cur.1
  · show d'.abtcb d'.cid = _
    rw [e2, e1]; exact h.cur.2
  · show AbTCBCorrect_range _ _ d'.abtcb
    rw [e2]; exact h.ainv.tc
  · show AbQCorrect_range _ _ d'.abq
    rw [e3]; exact h.ainv.qc
  · show NotInQ _ d'.AC d'.abtcb
    rw [e2, e4]; exact h.ainv.niq
  · show QCount _ _ d'.abtcb d'.abq
    rw [e2, e3]; exact h.ainv.cnt
  · show InQ _ _ d'.abtcb d'.abq
    rw [e2, e3]; exact h.ainv.inq

theorem setReg_keeps {reg n : Nat} {d d' : UData} (h : uctx_set_reg_spec reg n d = some d') (hI : KI d) :
    KI d' := by
  obtain ⟨U, e⟩ := set_reg_shape h
  subst e
  exact hI.congr rfl rfl rfl rfl rfl rfl rfl

/-- **Entering the kernel keeps the invariant.** -/
theorem exit_keeps {rs : UContext} {d d1 : UData} (h : proc_exit_user_spec rs d = some d1) (hI : KI d) : KI d1 := by
  obtain ⟨e, -⟩ := exit_shape h
  subst e
  exact hI.congr rfl rfl rfl rfl rfl rfl rfl

/-- **Leaving the kernel keeps the invariant**, and the machine is in user
mode. -/
theorem start_keeps {d d' : UData} {rs : UContext} (h : proc_start_user_spec d = some (d', rs)) (hI : KI d) :
    KI d' ∧ d'.ikern = false := by
  obtain ⟨e, -, -⟩ := start_shape h
  subst e
  exact ⟨hI.congr rfl rfl rfl rfl rfl rfl rfl, rfl⟩

/-! ## `proc_create` -/

theorem pt_new_split {id q : Nat} {d p : PTData} {i : Nat} (hs : pt_new_spec num_id mc id q d = some (p, i)) :
    container_split_spec num_id mc id q d.toRData = some (p.toRData, i) := by
  unfold pt_new_spec at hs
  split at hs
  · cases hsp : container_split_spec num_id mc id q d.toRData with
    | none => rw [hsp] at hs; cases hs
    | some pr =>
      obtain ⟨r1, i'⟩ := pr
      rw [hsp] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rfl
  · cases hs

theorem split_guard {id q : Nat} {r r' : RData} {i : Nat} (hs : container_split_spec num_id mc id q r = some (r', i)) :
    q + (r.AC id).cusage ≤ (r.AC id).cquota := by
  unfold container_split_spec at hs
  simp only at hs
  split at hs
  · rename_i hc; exact hc.2.2.2
  · cases hs

/-- **`proc_create` keeps the invariant.** -/
theorem create_keeps (hnn : num_id ≤ num_proc) {code : Nat → Stmt KPrim} {pstart uentry q : Nat} {d d' : UData}
    {i : Nat} (hs : proc_create_spec num_id mc num_chan code pstart uentry q d = some (d', i)) (hI : KI d) :
    KI d' := by
  obtain ⟨k1, hts, hd', hpg, hipt, hi, hcid⟩ := proc_create_factors hI.cur.1 hs
  subst hd'
  unfold thread_spawn_spec at hts
  cases hk : kctxt_new_spec num_id mc code pstart d.cid q (toK d) with
  | none => rw [hk] at hts; cases hts
  | some pr =>
    obtain ⟨d1, i'⟩ := pr
    rw [hk] at hts
    simp only at hts
    cases hq : d1.abq num_chan with
    | AbQUndef => rw [hq] at hts; cases hts
    | AbQValid ql =>
      rw [hq] at hts
      simp only [Option.some.injEq, Prod.mk.injEq] at hts
      obtain ⟨hk1, hii⟩ := hts
      subst hk1; subst hii
      unfold kctxt_new_spec at hk
      cases hp : pt_new_spec num_id mc d.cid q (toK d).toPTData with
      | none => rw [hp] at hk; cases hk
      | some pr =>
        obtain ⟨p, i''⟩ := pr
        rw [hp] at hk
        simp only [Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hd1, hi1⟩ := hk
        subst hi1; subst hd1
        have hsplit := pt_new_split hp
        have hguard := split_guard hsplit
        obtain ⟨-, -, hu, hLen, hi'', hilt, hpe⟩ := pt_new_shape hp
        have hCVd : Container_valid num_id mc d.AC := hI.cv
        have hfree : (d.AC i'').cused = false := by rw [hi'']; exact split_child_free hCVd hu hLen
        have hidne : i'' ≠ d.cid := by
          have hmc : 0 < mc := by omega
          have hmul : d.cid ≤ d.cid * mc := Nat.le_mul_of_pos_right _ hmc
          omega
        have hi''lt : i'' < num_proc := by omega
        have ePT : p.toRData.toPData = d.toPData := by rw [hpe]; rfl
        have eAC : p.AC = setAt (setAt d.AC d.cid ⟨(d.AC d.cid).cquota, (d.AC d.cid).cusage + q,
            (d.AC d.cid).cparent, i'' :: (d.AC d.cid).cchildren, (d.AC d.cid).cused⟩) i'' ⟨q, 0, d.cid, [], true⟩ := by
          rw [hpe]; rfl
        -- the child's control block
        have hv := hI.ainv.tc i'' hi''lt
        cases hai : d.abtcb i'' with
        | AbTCBUndef => rw [hai] at hv; exact hv.elim
        | AbTCBValid st b0 =>
          have hb0 : b0 = -1 := hI.ainv.niq i'' st b0 hi''lt hfree hai
          subst hb0
          -- the queue invariants, as in `thread_spawn_run`
          let D1 : KData :=
            { toK d with
              toPTData := p
              kctxt := setAt (toK d).kctxt i'' { (toK d).kctxt i'' with cont := .stop, stmt := code pstart } }
          have eAC1 : ∀ j, (D1.AC j).cused = if j = i'' then true else (d.AC j).cused := by
            intro j
            show (p.AC j).cused = _
            rw [eAC]
            by_cases ej : j = i''
            · rw [if_pos ej, ej, setAt_eq]
            · rw [if_neg ej, setAt_ne _ _ ej]
              by_cases ej2 : j = d.cid
              · rw [ej2, setAt_eq]
              · rw [setAt_ne _ _ ej2]
          have hI1 : AInv num_proc num_chan D1.toAData := by
            refine ⟨hI.ainv.tc, hI.ainv.qc, ?_, hI.ainv.cnt, hI.ainv.inq⟩
            intro j s b' hj hcu hjt
            have hcu' : (D1.AC j).cused = false := hcu
            rw [eAC1] at hcu'
            by_cases ej : j = i''
            · rw [if_pos ej] at hcu'; cases hcu'
            · rw [if_neg ej] at hcu'; exact hI.ainv.niq j s b' hj hcu' hjt
          have hpg1 : D1.pg = true := by show p.pg = true; rw [hpe]; exact hpg
          have hipt1 : D1.ipt = true := by show p.ipt = true; rw [hpe]; exact hipt
          have hcu1 : (D1.AC i'').cused = true := by rw [eAC1, if_pos rfl]
          obtain ⟨a1, hss, henq⟩ := PSched.park_factors (np := num_proc) (nc := num_chan) (a := D1.toAData)
            (cid := i'') (q := num_chan) (sv := 0) (ts := .READY) hpg1 hipt1 hi''lt (Nat.le_refl _) hcu1 hai rfl hq
          have hI3 := enqueue0_keeps henq (set_state0_keeps hss hI1)
          refine ⟨hI.cid, ⟨?_, ?_⟩, hI3, ?_, ?_, ?_, hpg1, hI.ihost,
            by show p.init = true; rw [hpe]; exact hI.init⟩
          · show (p.AC d.cid).cused = true
            rw [eAC, setAt_ne _ _ (Ne.symm hidne), setAt_eq]; exact hI.cur.1
          · show setAt d.abtcb i'' _ d.cid = _
            rw [setAt_ne _ _ (Ne.symm hidne)]; exact hI.cur.2
          · exact split_valid hCVd hsplit
          · show ATInv maxpage kl kh p.toRData.toPData
            rw [ePT]; exact hI.atinv
          · intro j
            show (p.AC j).cusage ≤ (p.AC j).cquota
            rw [eAC]
            by_cases ej : j = i''
            · rw [ej, setAt_eq]; exact Nat.zero_le _
            · rw [setAt_ne _ _ ej]
              by_cases ej2 : j = d.cid
              · rw [ej2, setAt_eq]
                have hg : q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota := hguard
                show (d.AC d.cid).cusage + q ≤ (d.AC d.cid).cquota; omega
              · rw [setAt_ne _ _ ej2]; exact hI.uq j

/-- **The dispatcher keeps the invariant**, for every number. -/
theorem dispatch_keeps (hnn : num_id ≤ num_proc) {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
    {d d' : UData} (hs : sys_dispatch_c_spec num_id mc num_chan code pstart elf d = some d') (hI : KI d) : KI d' := by
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
        | cases hs
        | exact setReg_keeps hs hI
        | exact setReg_keeps hs (setReg_keeps ‹uctx_set_retval1_spec _ _ = some _›
            (create_keeps hnn ‹proc_create_spec _ _ _ _ _ _ _ _ = some _› hI))
    · rw [if_neg h2] at hs
      by_cases h26 : a = 26
      · rw [if_pos h26] at hs
        obtain ⟨U, e⟩ := get_quota_shape hs
        subst e
        exact hI.congr rfl rfl rfl rfl rfl rfl rfl
      · rw [if_neg h26] at hs
        exact setReg_keeps hs hI

/-! ## `ptfault_resv` -/

/-- Containers keep everything but their usage, which only grows. -/
def ACMono (C C' : ContainerPool) : Prop :=
  ∀ j, (C' j).cquota = (C j).cquota ∧ (C' j).cparent = (C j).cparent ∧ (C' j).cchildren = (C j).cchildren ∧
    (C' j).cused = (C j).cused ∧ (C j).cusage ≤ (C' j).cusage

theorem ACMono.refl (C : ContainerPool) : ACMono C C := fun _ => ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem ACMono.trans {C1 C2 C3 : ContainerPool} (h1 : ACMono C1 C2) (h2 : ACMono C2 C3) : ACMono C1 C3 :=
  fun j => ⟨(h2 j).1.trans (h1 j).1, (h2 j).2.1.trans (h1 j).2.1, (h2 j).2.2.1.trans (h1 j).2.2.1,
    (h2 j).2.2.2.1.trans (h1 j).2.2.2.1, Nat.le_trans (h1 j).2.2.2.2 (h2 j).2.2.2.2⟩

theorem bump_mono (C : ContainerPool) (n : Nat) :
    ACMono C (setAt C n ⟨(C n).cquota, (C n).cusage + 1, (C n).cparent, (C n).cchildren, (C n).cused⟩) := by
  intro j
  by_cases e : j = n
  · subst e; rw [setAt_eq]; exact ⟨rfl, rfl, rfl, rfl, Nat.le_succ _⟩
  · rw [setAt_ne _ _ e]; exact ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem bump_mono' (C : ContainerPool) (n : Nat) (c : Container) (hq : c.cquota = (C n).cquota)
    (hp : c.cparent = (C n).cparent) (hc : c.cchildren = (C n).cchildren) (hu : c.cused = (C n).cused)
    (hs : (C n).cusage ≤ c.cusage) : ACMono C (setAt C n c) := by
  intro j
  by_cases e : j = n
  · subst e; rw [setAt_eq]; exact ⟨hq, hp, hc, hu, hs⟩
  · rw [setAt_ne _ _ e]; exact ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem alloc_facts' {n : Nat} {r r1 : RData} {b : Nat} (h : container_alloc_spec n r = some (r1, b)) :
    ACMono r.AC r1.AC ∧ r1.init = r.init := by
  unfold container_alloc_spec at h
  simp only at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
       refine ⟨?_, rfl⟩
       first | exact ACMono.refl _ | exact bump_mono' _ _ _ rfl rfl rfl rfl (Nat.le_succ _); done)
    | cases h

theorem allocPDE_facts {np nn vadr : Nat} {d d' : PTData} {v : Nat} (h : ptAllocPDE_spec np nn vadr d = some (d', v)) :
    ACMono d.AC d'.AC ∧ d'.init = d.init ∧ d'.pg = d.pg := by
  unfold ptAllocPDE_spec at h
  simp only at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
       refine ⟨?_, rfl, rfl⟩
       first | exact ACMono.refl _ | exact bump_mono' _ _ _ rfl rfl rfl rfl (Nat.le_succ _); done)
    | cases h

theorem insertPTE_facts {nn vadr padr : Nat} {p : PTPerm} {d d' : PTData} (h : ptInsertPTE_spec nn vadr padr p d = some d') :
    d'.AC = d.AC ∧ d'.init = d.init ∧ d'.pg = d.pg := by
  unfold ptInsertPTE_spec at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
    | cases h

theorem ptInsert_facts {mp np nn vadr padr perm : Nat} {d d' : PTData} {r : Nat}
    (h : ptInsert_spec mp np nn vadr padr perm d = some (d', r)) : ACMono d.AC d'.AC ∧ d'.init = d.init ∧ d'.pg = d.pg := by
  unfold ptInsert_spec at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i d2 hi
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          obtain ⟨a, b, c'⟩ := insertPTE_facts hi
          exact ⟨by rw [a]; exact ACMono.refl _, b, c'⟩
        · cases h
      · split at h
        · rename_i d2 v ha
          obtain ⟨a1, b1, c1⟩ := allocPDE_facts ha
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
            exact ⟨a1, b1, c1⟩
          · split at h
            · rename_i d3 hi
              simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
              obtain ⟨a2, b2, c2⟩ := insertPTE_facts hi
              exact ⟨by rw [a2]; exact a1, b2.trans b1, c2.trans c1⟩
            · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- What a reservation does to the containers and flags. -/
theorem ptResv_facts {mp np n vadr perm : Nat} {d d' : PTData} {r : Nat}
    (h : ptResv_spec mp np n vadr perm d = some (d', r)) : ACMono d.AC d'.AC ∧ d'.init = d.init ∧ d'.pg = d.pg := by
  unfold ptResv_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h; simp only at h
    obtain ⟨a1, b1⟩ := alloc_facts' hA
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact ⟨ACMono.refl _, rfl, rfl⟩
    · obtain ⟨a2, b2, c2⟩ := ptInsert_facts h
      exact ⟨a1.trans a2, b2.trans b1, c2⟩

/-- **`ptfault_resv` keeps the invariant.** -/
theorem pgf_keeps {vadr : Nat} {d d' : UData} (hs : ptfault_resv_spec maxpage num_proc vadr d = some d') (hI : KI d) :
    KI d' := by
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
        obtain ⟨hm, hinit, hpg⟩ := ptResv_facts hr
        obtain ⟨hat, huq⟩ := ptResv_keeps (maxpage := maxpage) (kl := kl) (kh := kh) ⟨hI.atinv, hI.uq⟩ hr
        have hcu : ∀ j, (p.AC j).cused = (d.AC j).cused := fun j => (hm j).2.2.2.1
        refine ⟨hI.cid, ⟨?_, hI.cur.2⟩, ⟨hI.ainv.tc, hI.ainv.qc, ?_, hI.ainv.cnt, hI.ainv.inq⟩, ?_, hat, huq,
          by show p.pg = true; rw [hpg]; exact hI.pg, hI.ihost, by show p.init = true; rw [hinit]; exact hI.init⟩
        · show (p.AC d.cid).cused = true
          rw [hcu]; exact hI.cur.1
        · intro j s b' hj hc hjt
          have hc' : (p.AC j).cused = false := hc
          rw [hcu] at hc'
          exact hI.ainv.niq j s b' hj hc' hjt
        · exact Container_valid.of_same hI.cv (fun j => (hm j).1) (fun j => (hm j).2.1) (fun j => (hm j).2.2.1) hcu
            (fun j _ => ⟨(hm j).2.2.2.2, by rw [← (hm j).1]; exact huq j⟩)
    · simp only [Option.some.injEq] at hs; subst hs; exact hI
  · cases hs

end

end TInv
