import CertiKOS.Confidentiality

/-!
# mCertiKOS security: confidentiality of the page-fault handler, ported

Ported from `security/Confidentiality.v`: `conf_alloc`, `conf_ptAllocPDE0`,
`conf_ptInsertPTE0`, `conf_ptInsert0`, `conf_ptfault_resv`.

A page fault gives the faulting process a fresh page. Which physical page it
gets depends on what the other processes have allocated, so it must not be
observable, and it is not: the observation hides physical pages. What the
process does see afterwards is a function of what it saw before.

* `resvKind`: the four things `pt_resv` can do for the caller: nothing (no
  quota), map a page under an existing table, allocate a page but find no
  quota for the table, or allocate a page and a table and map it.
  `resvKind_obs`: which one happens is determined by the observation.
* `ptResv_view`: what the result looks like in each case.
* `vlook`: the lookup both `vread` and `vread_perm` are built on.
  `look_resv`: the lookup after `pt_resv`, from the lookup before.
* `vread_resv`, `vperm_resv`: the address space after, as a function of the
  address space before.
* `conf_ptfault_resv`: **confidentiality of `ptfault_resv`.**
* `confidentiality_pgf`: **confidentiality of a page fault**, from the trap
  to the return.

What is assumed, as in mCertiKOS's `high_level_invariant`: the pages a
process maps are not free (`MappedUsed`), and a free page holds no data
(`FreeNone`, mCertiKOS's `dirty_ppage`), so a fresh page reads the same in
any two states.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Security

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt PProc TTrap TSysCall

variable {i : Nat}

/-! ## The lookup behind `vread` and `vread_perm` -/

/-- What the page table of process `i` says about a user address. -/
inductive Look
  | out
  | pdeID
  | pdeUnp
  | pdeUndef
  | pteUnp
  | pteUndef
  | page (w : Nat) (p : PTPerm)

def vlook (i v : Nat) (ptp : PMapPool) : Look :=
  if 1073741824 ≤ v ∧ v < 4026531840 then
    match ptp i (PDX v) with
    | .PDEValid _ pte =>
      match pte (PTX v) with
      | .PTEValid w p => .page w p
      | .PTEUnPresent => .pteUnp
      | .PTEUndef => .pteUndef
    | .PDEUnPresent => .pdeUnp
    | .PDEID => .pdeID
    | .PDEUndef => .pdeUndef
  else .out

/-- `vread`, from the lookup. -/
def readOf (v : Nat) (hp : Nat → Option Val) : Look → Option (Option Val)
  | .page w _ => some (hp (w * 1024 + v % 4096 / 4))
  | _ => none

/-- `vread_perm`, from the lookup. -/
def permOf (pp : Nat → PPgInfo) : Look → Option ObsPerm
  | .page w p => some (.ObsValid p (pp w))
  | .pteUnp => some .ObsPTEUnPresent
  | .pteUndef => some .ObsPTEUndef
  | .pdeUnp => some .ObsPDEUnPresent
  | .pdeID => some .ObsPDEID
  | .pdeUndef => some .ObsPDEUndef
  | .out => none

theorem vread_look (v : Nat) (ptp : PMapPool) (hp : Nat → Option Val) :
    vread i v ptp hp = readOf v hp (vlook i v ptp) := by
  unfold vread vlook
  split
  · cases ptp i (PDX v) with
    | PDEValid pi pte => simp only; cases pte (PTX v) <;> rfl
    | PDEID => rfl
    | PDEUnPresent => rfl
    | PDEUndef => rfl
  · rfl

theorem vperm_look (v : Nat) (ptp : PMapPool) (pp : Nat → PPgInfo) :
    vread_perm i v ptp pp = permOf pp (vlook i v ptp) := by
  unfold vread_perm vlook
  split
  · cases ptp i (PDX v) with
    | PDEValid pi pte => simp only; cases pte (PTX v) <;> rfl
    | PDEID => rfl
    | PDEUnPresent => rfl
    | PDEUndef => rfl
  · rfl

/-! ## What `pt_resv` does for the caller -/

/-- A free page holds no data (`dirty_ppage`). -/
def FreeNone (d : PTData) : Prop :=
  ∀ v c, d.AT v = .ATValid false .ATNorm c → ∀ a, a / 1024 = v → d.HP a = none

/-- The four outcomes of `pt_resv(n, vadr)`: 0 no quota, 1 a page under an
existing table, 2 a page but no quota for the table, 3 a page and a table. -/
def resvKind (n vadr : Nat) (d : PTData) : Nat :=
  if (d.AC n).cusage < (d.AC n).cquota then
    match d.ptpool n (PDX vadr) with
    | .PDEValid _ _ => 1
    | .PDEUnPresent => if (d.AC n).cusage + 1 < (d.AC n).cquota then 3 else 2
    | .PDEID => 0
    | .PDEUndef => 0
  else 0

/-- Pages charged to the caller. -/
def resvCost (k : Nat) : Nat := if k = 1 then 1 else if k = 2 then 1 else if k = 3 then 2 else 0

/-- What the result of `pt_resv` looks like to the caller. -/
structure ResvView (n vadr : Nat) (d d' : PTData) : Prop where
  hAC : d'.AC n = ⟨(d.AC n).cquota, (d.AC n).cusage + resvCost (resvKind n vadr d), (d.AC n).cparent,
    (d.AC n).cchildren, (d.AC n).cused⟩
  same : resvKind n vadr d ≠ 1 → resvKind n vadr d ≠ 3 → d'.ptpool n = d.ptpool n
  k1 : resvKind n vadr d = 1 → ∃ b pi pdt, (∃ c, d.AT b = .ATValid false .ATNorm c) ∧ d'.pperm b = .PGAlloc ∧
    (∀ a, a / 1024 = b → d'.HP a = d.HP a) ∧ d.ptpool n (PDX vadr) = .PDEValid pi pdt ∧
    d'.ptpool n = setAt (d.ptpool n) (PDX vadr) (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid b .PTU)))
  k3 : resvKind n vadr d = 3 → ∃ b pi2, (∃ c, d.AT b = .ATValid false .ATNorm c) ∧ d'.pperm b = .PGAlloc ∧
    (∀ a, a / 1024 = b → d'.HP a = d.HP a) ∧ d.ptpool n (PDX vadr) = .PDEUnPresent ∧
    d'.ptpool n = setAt (d.ptpool n) (PDX vadr)
      (.PDEValid pi2 (setAt real_init_PTE (PTX vadr) (.PTEValid b .PTU)))

/-- The shape of `ptInsertPTE_spec`'s result. -/
theorem insertPTE_view {n vadr padr : Nat} {p : PTPerm} {d d' : PTData}
    (h : ptInsertPTE_spec n vadr padr p d = some d') :
    ∃ pi pdt c, d.ptpool n (PDX vadr) = .PDEValid pi pdt ∧
      d' = { d with AT := setAt d.AT padr (.ATValid true .ATNorm (c + 1)),
                    ptpool := setAt d.ptpool n (setAt (d.ptpool n) (PDX vadr)
                      (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid padr p)))) } := by
  unfold ptInsertPTE_spec at h
  split at h
  · split at h
    · cases h
    · cases hp : d.ptpool n (PDX vadr) with
      | PDEValid pi pdt =>
        rw [hp] at h
        simp only at h
        split at h
        · cases hat : d.AT padr with
          | ATUndef => rw [hat] at h; cases h
          | ATValid b t c =>
            rw [hat] at h
            cases b <;> cases t <;> simp only at h <;> try (cases h)
            split at h
            · simp only [Option.some.injEq] at h
              exact ⟨pi, pdt, c, rfl, h.symm⟩
            · cases h
        · cases h
      | PDEID => rw [hp] at h; cases h
      | PDEUnPresent => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
  · cases h

/-- The shape of `ptAllocPDE_spec`'s result. -/
theorem allocPDE_view {np n vadr : Nat} {d d' : PTData} {v : Nat}
    (h : ptAllocPDE_spec np n vadr d = some (d', v)) :
    d.ptpool n (PDX vadr) = .PDEUnPresent ∧
      ((¬ (d.AC n).cusage < (d.AC n).cquota ∧ d' = d ∧ v = 0) ∨
       ((d.AC n).cusage < (d.AC n).cquota ∧ 0 < v ∧ (∃ c, d.AT v = .ATValid false .ATNorm c) ∧
        d' = { d with HP := free_page v d.HP, AT := setAt d.AT v (.ATValid true .ATNorm 0),
                      pperm := setAt d.pperm v (.PGHide n (PDX vadr)),
                      ptpool := setAt d.ptpool n (setAt (d.ptpool n) (PDX vadr) (.PDEValid v real_init_PTE)),
                      AC := setAt d.AC n ⟨(d.AC n).cquota, (d.AC n).cusage + 1, (d.AC n).cparent,
                        (d.AC n).cchildren, (d.AC n).cused⟩ })) := by
  unfold ptAllocPDE_spec at h
  simp only at h
  split at h
  · split at h
    · cases h
    · cases hp : d.ptpool n (PDX vadr) with
      | PDEUnPresent =>
        rw [hp] at h
        simp only at h
        refine ⟨rfl, ?_⟩
        by_cases hq : (d.AC n).cusage < (d.AC n).cquota
        · rw [if_pos hq] at h
          cases hff : first_free d.AT d.nps with
          | none => rw [hff] at h; cases h
          | some pi =>
            rw [hff] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hd, hv⟩ := h
            subst hv
            obtain ⟨hpos, -, hc0, -⟩ := first_free_some hff
            exact Or.inr ⟨hq, hpos, hc0, hd.symm⟩
        · rw [if_neg hq] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact Or.inl ⟨hq, h.1.symm, h.2.symm⟩
      | PDEValid _ _ => rw [hp] at h; cases h
      | PDEID => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
  · cases h

theorem ZtoPerm7 : ZtoPerm 7 = some .PTU := by decide

/-- **What `pt_resv` does for the caller**, case by case. -/
theorem ptResv_view {mp np n vadr : Nat} {d d' : PTData} {r : Nat}
    (h : ptResv_spec mp np n vadr 7 d = some (d', r)) : ResvView n vadr d d' := by
  unfold ptResv_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h
    simp only at h
    unfold container_alloc_spec at hA
    simp only at hA
    by_cases hg : d.init = true ∧ (d.AC n).cused = true
    · rw [if_pos hg] at hA
      by_cases hq : (d.AC n).cusage < (d.AC n).cquota
      · rw [if_pos hq] at hA
        cases hff : first_free d.AT d.nps with
        | none => rw [hff] at hA; cases hA
        | some b0 =>
          rw [hff] at hA
          simp only [Option.some.injEq, Prod.mk.injEq] at hA
          obtain ⟨hr1, hb⟩ := hA
          subst hb
          obtain ⟨hb0, -, hc0, -⟩ := first_free_some hff
          rw [if_neg (by omega)] at h
          -- the state after the first allocation
          obtain ⟨D1, hD1⟩ : ∃ D1 : PTData, D1 = { d with toRData := r1 } := ⟨_, rfl⟩
          rw [← hD1] at h
          have hpt1 : D1.ptpool = d.ptpool := by rw [hD1]
          have hHP1 : D1.HP = d.HP := by rw [hD1]
          have hAT1 : D1.AT = setAt d.AT b0 (.ATValid true .ATNorm 0) := by rw [hD1, ← hr1]
          have hpp1 : D1.pperm = setAt d.pperm b0 .PGAlloc := by rw [hD1, ← hr1]
          have hAC1 : D1.AC n = ⟨(d.AC n).cquota, (d.AC n).cusage + 1, (d.AC n).cparent, (d.AC n).cchildren,
              (d.AC n).cused⟩ := by
            rw [hD1, ← hr1]
            exact setAt_eq _ _ _
          clear hr1 hD1
          unfold ptInsert_spec at h
          split at h
          · rw [ZtoPerm7] at h
            simp only at h
            rw [hpt1] at h
            cases hp : d.ptpool n (PDX vadr) with
            | PDEValid pi pdt =>
              rw [hp] at h
              simp only at h
              split at h
              · rename_i d1 hi
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, -⟩ := h
                obtain ⟨pi', pdt', c, hp', hd1⟩ := insertPTE_view hi
                rw [hpt1, hp] at hp'
                injection hp' with e1 e2
                subst e1; subst e2
                have hk : resvKind n vadr d = 1 := by unfold resvKind; rw [if_pos hq, hp]
                subst hd1
                have hn3 : resvKind n vadr d ≠ 3 := by rw [hk]; decide
                refine ⟨?_, fun e => absurd hk e, fun _ => ⟨b0, pi, pdt, hc0, ?_, fun a _ => ?_, hp, ?_⟩,
                  fun e => absurd e hn3⟩
                · rw [hk]; exact hAC1
                · show D1.pperm b0 = _
                  rw [hpp1, setAt_eq]
                · show D1.HP a = _
                  rw [hHP1]
                · show setAt D1.ptpool n _ n = _
                  rw [setAt_eq, hpt1]
              · cases h
            | PDEUnPresent =>
              rw [hp] at h
              simp only at h
              split at h
              · rename_i D2 v ha
                obtain ⟨-, hcase⟩ := allocPDE_view ha
                rcases hcase with ⟨hq2, hD2, hv⟩ | ⟨hq2, hv, ⟨c2, hfree2⟩, hD2⟩
                · rw [hAC1] at hq2
                  have hD2' : D1 = D2 := hD2.symm
                  subst hv; subst hD2'
                  rw [if_pos rfl] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, -⟩ := h
                  have hk : resvKind n vadr d = 2 := by
                    unfold resvKind
                    rw [if_pos hq, hp]
                    exact if_neg hq2
                  have hn1 : resvKind n vadr d ≠ 1 := by rw [hk]; decide
                  have hn3 : resvKind n vadr d ≠ 3 := by rw [hk]; decide
                  have hACk : D1.AC n = ⟨(d.AC n).cquota, (d.AC n).cusage + resvCost (resvKind n vadr d),
                      (d.AC n).cparent, (d.AC n).cchildren, (d.AC n).cused⟩ := by rw [hk]; exact hAC1
                  have hptk : D1.ptpool n = d.ptpool n := by rw [hpt1]
                  exact ⟨hACk, fun _ _ => hptk, fun e => absurd e hn1, fun e => absurd e hn3⟩
                · rw [hAC1] at hq2
                  rw [if_neg (by omega)] at h
                  split at h
                  · rename_i d2 hi
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, -⟩ := h
                    obtain ⟨pi', pdt', c, hp', hd2⟩ := insertPTE_view hi
                    have hbv : b0 ≠ v := by
                      intro e
                      rw [hAT1, ← e, setAt_eq] at hfree2
                      cases hfree2
                    have hk : resvKind n vadr d = 3 := by
                      unfold resvKind
                      rw [if_pos hq, hp]
                      exact if_pos hq2
                    subst hD2
                    have hp'' : setAt D1.ptpool n (setAt (D1.ptpool n) (PDX vadr) (.PDEValid v real_init_PTE)) n
                        (PDX vadr) = .PDEValid pi' pdt' := hp'
                    rw [setAt_eq, setAt_eq] at hp''
                    injection hp'' with e1 e2
                    subst e1; subst e2
                    subst hd2
                    have hn1 : resvKind n vadr d ≠ 1 := by rw [hk]; decide
                    refine ⟨?_, fun _ e => absurd hk e, fun e => absurd e hn1,
                      fun _ => ⟨b0, v, hc0, ?_, fun a ha => ?_, hp, ?_⟩⟩
                    · rw [hk]
                      show setAt D1.AC n _ n = _
                      rw [setAt_eq, hAC1]
                      rfl
                    · show setAt D1.pperm v _ b0 = _
                      rw [setAt_ne _ _ hbv, hpp1, setAt_eq]
                    · show free_page v D1.HP a = _
                      unfold free_page
                      rw [if_neg (by rw [ha]; exact hbv), hHP1]
                    · show setAt (setAt D1.ptpool n (setAt (D1.ptpool n) (PDX vadr) (.PDEValid v real_init_PTE)))
                        n _ n = _
                      rw [setAt_eq]
                      show setAt (setAt D1.ptpool n (setAt (D1.ptpool n) (PDX vadr) (.PDEValid v real_init_PTE)) n)
                        (PDX vadr) _ = _
                      rw [setAt_eq, setAt_setAt, hpt1]
                  · cases h
              · cases h
            | PDEID => rw [hp] at h; cases h
            | PDEUndef => rw [hp] at h; cases h
          · cases h
      · rw [if_neg hq] at hA
        simp only [Option.some.injEq, Prod.mk.injEq] at hA
        obtain ⟨hr1, hb⟩ := hA
        subst hr1; subst hb
        rw [if_pos rfl] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have hk : resvKind n vadr d = 0 := by unfold resvKind; rw [if_neg hq]
        have hn1 : resvKind n vadr d ≠ 1 := by rw [hk]; decide
        have hn3 : resvKind n vadr d ≠ 3 := by rw [hk]; decide
        have hACk : d.AC n = ⟨(d.AC n).cquota, (d.AC n).cusage + resvCost (resvKind n vadr d),
            (d.AC n).cparent, (d.AC n).cchildren, (d.AC n).cused⟩ := by rw [hk]; rfl
        exact ⟨hACk, fun _ _ => rfl, fun e => absurd e hn1, fun e => absurd e hn3⟩
    · rw [if_neg hg] at hA; cases hA

/-! ## The address space after, from the address space before -/

theorem real_init_unp {k : Nat} (hk : k < 1024) : real_init_PTE k = .PTEUnPresent := by
  unfold real_init_PTE initPTE
  rw [if_pos hk]

theorem PTX_lt (v : Nat) : PTX v < 1024 := by unfold PTX; omega

/-- `vread` after `pt_resv` of kind `k` at `vadr`. -/
def resvHP (vadr k v : Nat) (old : Option (Option Val)) : Option (Option Val) :=
  if k = 1 then
    if (1073741824 ≤ v ∧ v < 4026531840) ∧ PDX v = PDX vadr ∧ PTX v = PTX vadr then some none else old
  else if k = 3 then
    if (1073741824 ≤ v ∧ v < 4026531840) ∧ PDX v = PDX vadr then
      (if PTX v = PTX vadr then some none else none)
    else old
  else old

/-- `vread_perm` after `pt_resv` of kind `k` at `vadr`. -/
def resvPerm (vadr k v : Nat) (old : Option ObsPerm) : Option ObsPerm :=
  if k = 1 then
    if (1073741824 ≤ v ∧ v < 4026531840) ∧ PDX v = PDX vadr ∧ PTX v = PTX vadr then
      some (.ObsValid .PTU .PGAlloc)
    else old
  else if k = 3 then
    if (1073741824 ≤ v ∧ v < 4026531840) ∧ PDX v = PDX vadr then
      (if PTX v = PTX vadr then some (.ObsValid .PTU .PGAlloc) else some .ObsPTEUnPresent)
    else old
  else old

theorem look_page {v w : Nat} {p : PTPerm} {ptp : PMapPool} (h : vlook i v ptp = .page w p) :
    ∃ pi pte, ptp i (PDX v) = .PDEValid pi pte ∧ pte (PTX v) = .PTEValid w p := by
  unfold vlook at h
  split at h
  · cases hp : ptp i (PDX v) with
    | PDEValid pi pte =>
      rw [hp] at h
      simp only at h
      cases hq : pte (PTX v) with
      | PTEValid w' p' =>
        rw [hq] at h
        simp only [Look.page.injEq] at h
        exact ⟨pi, pte, rfl, by rw [hq, h.1, h.2]⟩
      | PTEUnPresent => rw [hq] at h; cases h
      | PTEUndef => rw [hq] at h; cases h
    | PDEID => rw [hp] at h; cases h
    | PDEUnPresent => rw [hp] at h; cases h
    | PDEUndef => rw [hp] at h; cases h
  · cases h

/-- The lookup after mapping page `b` at `vadr` under the existing table. -/
theorem look_k1 {vadr b pi : Nat} {pdt : PTE} {ptp ptp' : PMapPool} (hp : ptp i (PDX vadr) = .PDEValid pi pdt)
    (hpt : ptp' i = setAt (ptp i) (PDX vadr) (.PDEValid pi (setAt pdt (PTX vadr) (.PTEValid b .PTU))))
    (v : Nat) :
    vlook i v ptp' = if (1073741824 ≤ v ∧ v < 4026531840) ∧ PDX v = PDX vadr ∧ PTX v = PTX vadr then
      .page b .PTU else vlook i v ptp := by
  unfold vlook
  rw [hpt]
  by_cases hr : 1073741824 ≤ v ∧ v < 4026531840
  · rw [if_pos hr, if_pos hr]
    by_cases e1 : PDX v = PDX vadr
    · by_cases e2 : PTX v = PTX vadr
      · rw [if_pos ⟨hr, e1, e2⟩, e1, setAt_eq]
        simp only
        rw [e2, setAt_eq]
      · rw [if_neg (fun c => e2 c.2.2), e1, setAt_eq, hp]
        simp only
        rw [setAt_ne _ _ e2]
    · rw [if_neg (fun c => e1 c.2.1), setAt_ne _ _ e1]
  · rw [if_neg hr, if_neg hr, if_neg (fun c => hr c.1)]

/-- The lookup after mapping page `b` at `vadr` under a new table. -/
theorem look_k3 {vadr b pi2 : Nat} {ptp ptp' : PMapPool} (hp : ptp i (PDX vadr) = .PDEUnPresent)
    (hpt : ptp' i = setAt (ptp i) (PDX vadr)
      (.PDEValid pi2 (setAt real_init_PTE (PTX vadr) (.PTEValid b .PTU)))) (v : Nat) :
    vlook i v ptp' = if (1073741824 ≤ v ∧ v < 4026531840) ∧ PDX v = PDX vadr then
      (if PTX v = PTX vadr then .page b .PTU else .pteUnp) else vlook i v ptp := by
  unfold vlook
  rw [hpt]
  by_cases hr : 1073741824 ≤ v ∧ v < 4026531840
  · rw [if_pos hr, if_pos hr]
    by_cases e1 : PDX v = PDX vadr
    · rw [if_pos ⟨hr, e1⟩]
      by_cases e2 : PTX v = PTX vadr
      · rw [if_pos e2, e1, setAt_eq]
        simp only
        rw [e2, setAt_eq]
      · rw [if_neg e2, e1, setAt_eq]
        simp only
        rw [setAt_ne _ _ e2, real_init_unp (PTX_lt v)]
    · rw [if_neg (fun c => e1 c.2), setAt_ne _ _ e1]
  · rw [if_neg hr, if_neg hr, if_neg (fun c => hr c.1)]

/-- **The address space after `pt_resv`**, as a function of the address
space before and of the kind of outcome. -/
theorem resv_obs {vadr : Nat} {d d' : PTData} (hv : ResvView i vadr d d') (hf : PFrame i d d')
    (hmu : MappedUsed i d) (hfn : FreeNone d) (v : Nat) :
    vread i v d'.ptpool d'.HP = resvHP vadr (resvKind i vadr d) v (vread i v d.ptpool d.HP) ∧
    vread_perm i v d'.ptpool d'.pperm = resvPerm vadr (resvKind i vadr d) v (vread_perm i v d.ptpool d.pperm) := by
  -- the pages the caller maps keep their contents and their type
  have hold : readOf v d'.HP (vlook i v d.ptpool) = readOf v d.HP (vlook i v d.ptpool) ∧
      permOf d'.pperm (vlook i v d.ptpool) = permOf d.pperm (vlook i v d.ptpool) := by
    cases hl : vlook i v d.ptpool with
    | page w p =>
      obtain ⟨pi, pte, h1, h2⟩ := look_page hl
      obtain ⟨a1, a2, -⟩ := hf.used w (hmu _ pi pte h1 _ w p h2)
      exact ⟨by show some (d'.HP _) = some (d.HP _); rw [a2 _ (by omega)],
        by show some (ObsPerm.ObsValid p (d'.pperm w)) = some (ObsPerm.ObsValid p (d.pperm w)); rw [a1]⟩
    | out => exact ⟨rfl, rfl⟩
    | pdeID => exact ⟨rfl, rfl⟩
    | pdeUnp => exact ⟨rfl, rfl⟩
    | pdeUndef => exact ⟨rfl, rfl⟩
    | pteUnp => exact ⟨rfl, rfl⟩
    | pteUndef => exact ⟨rfl, rfl⟩
  rw [vread_look, vread_look, vperm_look, vperm_look]
  by_cases k1 : resvKind i vadr d = 1
  · obtain ⟨b, pi, pdt, ⟨c, hfree⟩, hpp, hHP, hp, hpt⟩ := hv.k1 k1
    rw [k1, look_k1 hp hpt v]
    unfold resvHP resvPerm
    rw [if_pos rfl, if_pos rfl]
    by_cases hc : (1073741824 ≤ v ∧ v < 4026531840) ∧ PDX v = PDX vadr ∧ PTX v = PTX vadr
    · rw [if_pos hc, if_pos hc, if_pos hc]
      refine ⟨?_, ?_⟩
      · show some (d'.HP (b * 1024 + v % 4096 / 4)) = some none
        rw [hHP _ (by omega), hfn b c hfree _ (by omega)]
      · show some (ObsPerm.ObsValid .PTU (d'.pperm b)) = _
        rw [hpp]
    · rw [if_neg hc, if_neg hc, if_neg hc]
      exact hold
  · by_cases k3 : resvKind i vadr d = 3
    · obtain ⟨b, pi2, ⟨c, hfree⟩, hpp, hHP, hp, hpt⟩ := hv.k3 k3
      rw [k3, look_k3 hp hpt v]
      unfold resvHP resvPerm
      rw [if_neg (show ¬ (3 = 1) by decide), if_pos rfl, if_neg (show ¬ (3 = 1) by decide), if_pos rfl]
      by_cases hc : (1073741824 ≤ v ∧ v < 4026531840) ∧ PDX v = PDX vadr
      · rw [if_pos hc, if_pos hc, if_pos hc]
        by_cases e2 : PTX v = PTX vadr
        · rw [if_pos e2, if_pos e2, if_pos e2]
          refine ⟨?_, ?_⟩
          · show some (d'.HP (b * 1024 + v % 4096 / 4)) = some none
            rw [hHP _ (by omega), hfn b c hfree _ (by omega)]
          · show some (ObsPerm.ObsValid .PTU (d'.pperm b)) = _
            rw [hpp]
        · rw [if_neg e2, if_neg e2, if_neg e2]
          exact ⟨rfl, rfl⟩
      · rw [if_neg hc, if_neg hc, if_neg hc]
        exact hold
    · have hlook : vlook i v d'.ptpool = vlook i v d.ptpool := by
        unfold vlook
        rw [hv.same k1 k3]
      unfold resvHP resvPerm
      rw [if_neg k1, if_neg k3, if_neg k1, if_neg k3, hlook]
      exact hold

/-! ## The kind of outcome is observable -/

/-- Whether the directory entry of a user address is a table, or absent, can
be read off `vread_perm`. -/
theorem perm_pde {v : Nat} (hin : 1073741824 ≤ v ∧ v < 4026531840) {ptp1 ptp2 : PMapPool}
    {pp1 pp2 : Nat → PPgInfo} (h : vread_perm i v ptp1 pp1 = vread_perm i v ptp2 pp2) :
    ((∃ pi pdt, ptp1 i (PDX v) = .PDEValid pi pdt) ↔ (∃ pi pdt, ptp2 i (PDX v) = .PDEValid pi pdt)) ∧
    (ptp1 i (PDX v) = .PDEUnPresent ↔ ptp2 i (PDX v) = .PDEUnPresent) := by
  unfold vread_perm at h
  rw [if_pos hin, if_pos hin] at h
  cases h1 : ptp1 i (PDX v) <;> cases h2 : ptp2 i (PDX v) <;> rw [h1, h2] at h <;> simp only at h
  all_goals first
    | exact ⟨Iff.rfl, Iff.rfl⟩
    | exact ⟨⟨fun _ => ⟨_, _, rfl⟩, fun _ => ⟨_, _, rfl⟩⟩, ⟨nofun, nofun⟩⟩
    | (exfalso; cases h)
    | (exfalso; split at h <;> cases h)

theorem resvKind_obs {vadr : Nat} {d1 d2 : UData} (h : ObsEq i d1 d2)
    (hin : 1073741824 ≤ vadr ∧ vadr < 4026531840) :
    resvKind i vadr d1.toPTData = resvKind i vadr d2.toPTData := by
  obtain ⟨hv, hu⟩ := perm_pde hin (h.hperm vadr)
  have hq := h.hquota
  have e1 : (d1.AC i).cusage < (d1.AC i).cquota ↔ (d2.AC i).cusage < (d2.AC i).cquota := by omega
  have e2 : (d1.AC i).cusage + 1 < (d1.AC i).cquota ↔ (d2.AC i).cusage + 1 < (d2.AC i).cquota := by omega
  unfold resvKind
  by_cases c1 : (d1.AC i).cusage < (d1.AC i).cquota
  · rw [if_pos c1, if_pos (e1.1 c1)]
    cases p1 : d1.ptpool i (PDX vadr) with
    | PDEValid pi pdt =>
      obtain ⟨pi2, pdt2, p2⟩ := hv.1 ⟨_, _, p1⟩
      rw [p2]
    | PDEUnPresent =>
      rw [hu.1 p1]
      simp only
      by_cases c2 : (d1.AC i).cusage + 1 < (d1.AC i).cquota
      · rw [if_pos c2, if_pos (e2.1 c2)]
      · rw [if_neg c2, if_neg (fun c => c2 (e2.2 c))]
    | PDEID =>
      cases p2 : d2.ptpool i (PDX vadr) with
      | PDEValid pi2 pdt2 =>
        obtain ⟨pi, pdt, p1'⟩ := hv.2 ⟨_, _, p2⟩
        rw [p1] at p1'; cases p1'
      | PDEUnPresent => have p1' := hu.2 p2; rw [p1] at p1'; cases p1'
      | PDEID => rfl
      | PDEUndef => rfl
    | PDEUndef =>
      cases p2 : d2.ptpool i (PDX vadr) with
      | PDEValid pi2 pdt2 =>
        obtain ⟨pi, pdt, p1'⟩ := hv.2 ⟨_, _, p2⟩
        rw [p1] at p1'; cases p1'
      | PDEUnPresent => have p1' := hu.2 p2; rw [p1] at p1'; cases p1'
      | PDEID => rfl
      | PDEUndef => rfl
  · rw [if_neg c1, if_neg (fun c => c1 (e1.2 c))]

/-! ## Confidentiality -/

/-- **Confidentiality of `ptfault_resv`** (`conf_ptfault_resv`). -/
theorem conf_ptfault_resv {mp np vadr : Nat} {d1 d2 d1' d2' : UData} (hmu1 : MappedUsed i d1.toPTData)
    (hmu2 : MappedUsed i d2.toPTData) (hfn1 : FreeNone d1.toPTData) (hfn2 : FreeNone d2.toPTData)
    (h1 : ptfault_resv_spec mp np vadr d1 = some d1') (h2 : ptfault_resv_spec mp np vadr d2 = some d2')
    (hi : i = d1.cid) (h : ObsEq i d1 d2) : ObsEq i d1' d2' := by
  have hi2 := h.hcid.1 hi
  unfold ptfault_resv_spec at h1 h2
  split at h1
  · split at h2
    · by_cases hr : 1073741824 ≤ vadr ∧ vadr < 4026531840
      · rw [if_pos hr] at h1 h2
        cases hp1 : ptResv_spec mp np d1.cid vadr 7 d1.toPTData with
        | none => rw [hp1] at h1; cases h1
        | some pr1 =>
          obtain ⟨p1, r1⟩ := pr1
          rw [hp1] at h1
          simp only [Option.some.injEq] at h1
          subst h1
          cases hp2 : ptResv_spec mp np d2.cid vadr 7 d2.toPTData with
          | none => rw [hp2] at h2; cases h2
          | some pr2 =>
            obtain ⟨p2, r2⟩ := pr2
            rw [hp2] at h2
            simp only [Option.some.injEq] at h2
            subst h2
            rw [← hi] at hp1
            rw [← hi2] at hp2
            have v1 := ptResv_view hp1
            have f1 := ptResv_frame hp1
            have v2 := ptResv_view hp2
            have f2 := ptResv_frame hp2
            have hk := resvKind_obs h hr
            have hq := h.hquota
            have hA1 : p1.AC i = _ := v1.hAC
            have hA2 : p2.AC i = _ := v2.hAC
            refine ⟨fun v => ?_, fun v => ?_, ?_, ?_, ?_, h.hcid, h.hkctxt, h.huctxt, h.hikern, h.hihost,
              fun e => ?_, fun e => ?_, fun e => ?_⟩
            · show vread i v p1.ptpool p1.HP = vread i v p2.ptpool p2.HP
              rw [(resv_obs v1 f1 hmu1 hfn1 v).1, (resv_obs v2 f2 hmu2 hfn2 v).1, hk, h.hHP v]
            · show vread_perm i v p1.ptpool p1.pperm = vread_perm i v p2.ptpool p2.pperm
              rw [(resv_obs v1 f1 hmu1 hfn1 v).2, (resv_obs v2 f2 hmu2 hfn2 v).2, hk, h.hperm v]
            · show ((p1.AC i).cquota : Int) - (p1.AC i).cusage = ((p2.AC i).cquota : Int) - (p2.AC i).cusage
              rw [hA1, hA2, hk]
              show ((d1.AC i).cquota : Int) - ((d1.AC i).cusage + resvCost (resvKind i vadr d2.toPTData) : Nat) =
                ((d2.AC i).cquota : Int) - ((d2.AC i).cusage + resvCost (resvKind i vadr d2.toPTData) : Nat)
              omega
            · show (p1.AC i).cchildren.length = (p2.AC i).cchildren.length
              rw [hA1, hA2]
              exact h.hnchildren
            · show (p1.AC i).cused = (p2.AC i).cused
              rw [hA1, hA2]
              exact h.hused
            · show p1.pg = p2.pg
              rw [f1.flags.1, f2.flags.1]
              exact h.hpg e
            · show p1.ipt = p2.ipt
              rw [f1.flags.2.1, f2.flags.2.1]
              exact h.hipt e
            · show p1.init = p2.init
              rw [f1.flags.2.2, f2.flags.2.2]
              exact h.hinit e
      · rw [if_neg hr] at h1 h2
        simp only [Option.some.injEq] at h1 h2
        subst h1; subst h2
        exact h
    · cases h2
  · cases h1

/-- **Confidentiality of a page fault**, from the trap to the return. -/
theorem confidentiality_pgf {mp np vadr : Nat} {d d1 d2 d3 e e1 e2 e3 : UData} {rs rsd rse : UContext}
    (hmu1 : MappedUsed i d.toPTData) (hmu2 : MappedUsed i e.toPTData) (hfn1 : FreeNone d.toPTData)
    (hfn2 : FreeNone e.toPTData) (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : ptfault_resv_spec mp np vadr d1 = some d2) (h3 : proc_start_user_spec d2 = some (d3, rsd))
    (g1 : proc_exit_user_spec rs e = some e1) (g2 : ptfault_resv_spec mp np vadr e1 = some e2)
    (g3 : proc_start_user_spec e2 = some (e3, rse)) (hi : i = d.cid) (h : ObsEq i d e) :
    ObsEq i d3 e3 ∧ rsd = rse := by
  obtain ⟨hd1, -⟩ := exit_shape h1
  obtain ⟨he1, -⟩ := exit_shape g1
  have hi1 : i = d1.cid := by rw [hd1]; exact hi
  have o1 := conf_proc_exit_user h1 g1 hi h
  have o2 := conf_ptfault_resv (i := i) (by rw [hd1]; exact hmu1) (by rw [he1]; exact hmu2)
    (by rw [hd1]; exact hfn1) (by rw [he1]; exact hfn2) h2 g2 hi1 o1
  exact conf_proc_start_user h3 g3 (by rw [ptfault_cid h2]; exact hi1) o2

end Security
