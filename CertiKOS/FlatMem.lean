import CertiKOS.MPTOp
import CertiKOS.MALInitC
import CertiKOS.LayerStep

/-!
# mCertiKOS `flatmem_copy`: copying between two pages, ported

Ported from `objects/ObjFlatMem.v`: `flatmem_copy_aux`, `flatmem_copy_spec`.

`flatmem_copy(len, from, to)` copies `len` words from the page at byte address
`from` to the page at byte address `to`. Both pages must be allocated
(`PGAlloc`), so neither holds a page table.

* `flat_write`: **writing a word of an allocated page keeps the region
  matching the abstract state.** The second-level page tables are in hidden
  pages (`PGHide`), and a hidden page is not an allocated one.
* `flatmemCopy_step`, `flatmemCopy_triple`: **the loop refines
  `flatmem_copy_spec`.**

What differs: mCertiKOS takes `flatmem_copy` as a primitive of its bottom
layer, with no code. Here it is a loop over the cells of flat memory. Flat
memory is indexed by word here and by byte in mCertiKOS, so byte address `x`
is word `x / 4`, and the copy steps by one word where mCertiKOS steps by four
bytes. The arguments are named `src` and `dst` (`from` is a keyword).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace FlatMem

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Specification (`ObjFlatMem.v`) -/

/-- `flatmem_copy_aux`: copy `n` words from word `src` on to word `dst` on. A
word that was never written cannot be copied. -/
def flatmem_copy_aux : Nat → Nat → Nat → (Nat → Option Val) → Option (Nat → Option Val)
  | 0, _, _, h => some h
  | n + 1, src, dst, h =>
    match h src with
    | some v => flatmem_copy_aux n (src + 1) (dst + 1) (setAt h dst (some v))
    | none => none

/-- **`flatmem_copy_spec`**: copy `count` words from the page at byte address
`src` to the page at byte address `dst`. Both are allocated pages below
`adr_low`. -/
def flatmem_copy_spec (count src dst : Nat) (d : PTData) : Option PTData :=
  if d.ipt = true ∧ dst < 2 ^ 30 ∧ src < 2 ^ 30 ∧ count ≤ 1024 ∧ dst % 4096 = 0 ∧ src % 4096 = 0 ∧
      d.pperm (src / 4096) = .PGAlloc ∧ d.pperm (dst / 4096) = .PGAlloc then
    match flatmem_copy_aux count (src / 4) (dst / 4) d.HP with
    | some h => some { d with HP := h }
    | none => none
  else none

theorem copy_step {n s t : Nat} {h hf : Nat → Option Val} (hn : 0 < n)
    (hc : flatmem_copy_aux n s t h = some hf) :
    ∃ v, h s = some v ∧ flatmem_copy_aux (n - 1) (s + 1) (t + 1) (setAt h t (some v)) = some hf := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  cases hv : h s with
  | none => simp [flatmem_copy_aux, hv] at hc
  | some v =>
    simp only [flatmem_copy_aux, hv] at hc
    exact ⟨v, rfl, hc⟩

/-- `flatmem_copy` changes only flat memory. -/
theorem flatmem_copy_HP {count src dst : Nat} {d d' : PTData} (hs : flatmem_copy_spec count src dst d = some d') :
    ∃ h, d' = { d with HP := h } := by
  unfold flatmem_copy_spec at hs
  split at hs
  · cases hcp : flatmem_copy_aux count (src / 4) (dst / 4) d.HP with
    | none => rw [hcp] at hs; cases hs
    | some h =>
      rw [hcp] at hs
      simp only [Option.some.injEq] at hs
      exact ⟨h, hs.symm⟩
  · cases hs

/-! ## The code -/

/-- `&FlatMem[x / 4 + i]` -/
def fmE (fb : Nat) (x : Ident) : Expr :=
  .bin .add (.const (BitVec.ofNat 32 fb)) (.bin .add (.bin .div (.var x) (.const 4)) (.var "i"))

/-- `flatmem_copy(len, from, to)`:
`for (i = 0; i < len; i++) FlatMem[to / 4 + i] = FlatMem[from / 4 + i];` -/
def flatmemCopyS (fb : Nat) : Stmt APrim :=
  .seq (.assign "i" (.const 0))
    (.while (.bin .ltu (.var "i") (.var "len"))
      (.seq (.call "v" .pull [lkE, fmE fb "from"])
        (.seq (.call "_" .push [lkE, fmE fb "to", .var "v"])
          (.assign "i" (.bin .add (.var "i") (.const 1))))))

theorem fm_eval {fb : Nat} (hfb : fb + 2 ^ 30 ≤ 2 ^ 32) {σ : Locals} {x : Ident} {a m : Nat}
    (hx : σ x = BitVec.ofNat 32 a) (hi : σ "i" = BitVec.ofNat 32 m) (ha : a < 2 ^ 30) (hm : m ≤ 1024) :
    ((fmE fb x).eval σ).toNat = fb + (a / 4 + m) := by
  have e : (fmE fb x).eval σ = BitVec.ofNat 32 fb + (σ x / 4 + σ "i") := rfl
  rw [e, hx, hi, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_udiv, tn (show fb < 2 ^ 32 by omega),
    tn (show a < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]
  show (fb + (a / 4 + m) % 2 ^ 32) % 2 ^ 32 = _
  omega

section Region
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **Writing a word of an allocated page.** The page tables are in hidden
pages, so no table sees the write. -/
theorem flat_write (hL : Layout maxpage num_id cb num_proc pb ib fb) {d : PTData} {b : Region}
    (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida d b) {a : Nat} (v : Val)
    (hal : d.pperm (a / 1024) = .PGAlloc) :
    MatchAll maxpage num_id cb num_proc pb ib fb ida { d with HP := setAt d.HP a (some v) }
      (setCell b (fb + a) v) := by
  have := hL.hpb; have := hL.hib; have := hL.hfb
  have hpage : ∀ n i pi pdx, n < num_proc → i < 1024 → d.ptpool n i = .PDEValid pi pdx → pi ≠ a / 1024 := by
    intro n i pi pdx hn hi hp e
    have old := hM.pt.pool n i hn hi
    rw [hp] at old
    have h2 : d.pperm pi = .PGHide n i := old.2
    rw [e, hal] at h2
    cases h2
  refine ⟨mm_frame hL hM.mm rfl rfl rfl (fun k hk => sc_ne _ _ (by omega)), ?_⟩
  refine ⟨fun n i hn hi => ?_, fun i j hi hj => ?_, fun n i pi pdx hn hi hp vadr hv => ?_,
    fun a' v' hav => ?_, fun n i pi pdx hn hi hp a' ha' => ?_⟩
  · show MatchPDE d.pperm ida (d.ptpool n i) (setCell b (fb + a) v (pb + n * 1024 + i)) n i
    rw [sc_ne _ _ (by omega)]; exact hM.pt.pool n i hn hi
  · show MatchIDPTE (d.idpde i j) (setCell b (fb + a) v (ib + i * 1024 + j)) i j
    rw [sc_ne _ _ (by omega)]; exact hM.pt.idp i j hi hj
  · have hp' : d.ptpool n i = .PDEValid pi pdx := hp
    have hne := hpage n i pi pdx hn hi hp'
    rw [sc_ne _ _ (by omega)]
    exact hM.pt.pte n i pi pdx hn hi hp' vadr hv
  · have hav' : setAt d.HP a (some v) a' = some v' := hav
    by_cases e : a' = a
    · subst e
      rw [setAt_eq] at hav'
      injection hav' with hav'
      rw [sc_eq]; exact hav'
    · rw [setAt_ne _ _ e] at hav'
      rw [sc_ne _ _ (by omega)]
      exact hM.pt.hp a' v' hav'
  · have hp' : d.ptpool n i = .PDEValid pi pdx := hp
    have hne := hpage n i pi pdx hn hi hp'
    show setAt d.HP a (some v) a' = none
    rw [setAt_ne _ _ (fun e => hne (by rw [← ha', e]))]
    exact hM.pt.hid n i pi pdx hn hi hp' a' ha'

variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MA" => MatchAll maxpage num_id cb num_proc pb ib fb ida

/-- **`flatmem_copy` runs as its specification says.** The length is in
`len`, the addresses in `from` and `to`. It writes flat memory only, and of
the locals only `i`, `v` and `_`. -/
theorem flatmemCopy_step (hL : Layout maxpage num_id cb num_proc pb ib fb) (hF : ∀ k, fb ≤ k → F k)
    {σ : Locals} {d d' : PTData} {count src dst : Nat} (hlen : σ "len" = BitVec.ofNat 32 count)
    (hsrc : σ "from" = BitVec.ofNat 32 src) (hdst : σ "to" = BitVec.ofNat 32 dst)
    (hs : flatmem_copy_spec count src dst d = some d') :
    ∃ σ', Step εR c i0 MA F (flatmemCopyS fb) σ d σ' d' ∧
      ∀ z, z ≠ "i" → z ≠ "v" → z ≠ "_" → σ' z = σ z := by
  have hfb := hL.hend
  unfold flatmem_copy_spec at hs
  by_cases hc : d.ipt = true ∧ dst < 2 ^ 30 ∧ src < 2 ^ 30 ∧ count ≤ 1024 ∧ dst % 4096 = 0 ∧ src % 4096 = 0 ∧
      d.pperm (src / 4096) = .PGAlloc ∧ d.pperm (dst / 4096) = .PGAlloc
  · rw [if_pos hc] at hs
    obtain ⟨hipt, hd30, hs30, hcnt, hdm, hsm, hps, hpd⟩ := hc
    cases hcp : flatmem_copy_aux count (src / 4) (dst / 4) d.HP with
    | none => rw [hcp] at hs; cases hs
    | some hf =>
      rw [hcp] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      let I : Locals → PTData → Prop := fun τ e => ∃ (m : Nat) (hm : Nat → Option Val), m ≤ count ∧
        τ "i" = BitVec.ofNat 32 m ∧ (∀ z, z ≠ "i" → z ≠ "v" → z ≠ "_" → τ z = σ z) ∧
        flatmem_copy_aux (count - m) (src / 4 + m) (dst / 4 + m) hm = some hf ∧ e = { d with HP := hm }
      have hbody : ∀ τ e, I τ e → ¬ (Expr.bin .ltu (.var "i") (.var "len")).eval τ = 0 →
          ∃ τ' e', Step εR c i0 MA F (.seq (.call "v" .pull [lkE, fmE fb "from"])
              (.seq (.call "_" .push [lkE, fmE fb "to", .var "v"])
                (.assign "i" (.bin .add (.var "i") (.const 1))))) τ e τ' e' ∧ I τ' e' ∧
            count - (τ' "i").toNat < count - (τ "i").toNat := by
        rintro τ e ⟨m, hm, hmc, hiτ, hfr, haux, rfl⟩ hg
        have hlenτ : τ "len" = BitVec.ofNat 32 count :=
          (hfr "len" (by decide) (by decide) (by decide)).trans hlen
        have hsrcτ : τ "from" = BitVec.ofNat 32 src :=
          (hfr "from" (by decide) (by decide) (by decide)).trans hsrc
        have hdstτ : τ "to" = BitVec.ofNat 32 dst := (hfr "to" (by decide) (by decide) (by decide)).trans hdst
        rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .var "len") hiτ hlenτ (by omega) (by omega)] at hg
        have hmlt : m < count := by
          by_cases h : m < count
          · exact h
          · rw [if_neg h] at hg; exact absurd rfl hg
        obtain ⟨v, hv, haux'⟩ := copy_step (show 0 < count - m by omega) haux
        let τ1 := τ.set "v" v
        let τ2 := τ1.set "_" 0
        let τ3 := τ2.set "i" (BitVec.ofNat 32 (m + 1))
        have hal : d.pperm ((dst / 4 + m) / 1024) = .PGAlloc := by
          have e : (dst / 4 + m) / 1024 = dst / 4096 := by omega
          rw [e]; exact hpd
        refine ⟨τ3, { d with HP := setAt hm (dst / 4 + m) (some v) }, ⟨by simp [τ3, τ2, τ1, Locals.set], ?_⟩,
          ⟨m + 1, _, hmlt, by simp [τ3], fun z h1 h2 h3 => ?_, ?_, rfl⟩, ?_⟩
        · intro l b hlk hcs hM
          have r1 := rd_run (εR := εR) hcs hlk "v" (fmE fb "from") (fm_eval hfb hsrcτ hiτ hs30 (by omega))
          rw [hM.pt.hp (src / 4 + m) v hv] at r1
          have hlk1 : (τ1 "lk").toNat = i0 := by simpa [τ1, Locals.set] using hlk
          obtain ⟨l2, r2, c2⟩ := wr_run (εR := εR) hcs hlk1 (fmE fb "to") (.var "v") (v := v)
            (fm_eval (σ := τ1) (a := dst) (m := m) hfb (by simp [τ1, Locals.set, hdstτ])
              (by simp [τ1, Locals.set, hiτ]) hd30 (by omega)) (by simp [τ1, Expr.eval])
          have r3 : Runs (rprimsA εR c) (.assign "i" (.bin .add (.var "i") (.const 1))) τ2 l2 τ3 l2 :=
            asg_run "i" _ (inc_eval (m := m) (by simp [τ2, τ1, Locals.set, hiτ]))
          have hw : MA { d with HP := setAt hm (dst / 4 + m) (some v) } (setCell b (fb + (dst / 4 + m)) v) :=
            flat_write hL hM (a := dst / 4 + m) v hal
          exact ⟨l2, _, Runs.seq r1 (Runs.seq r2 r3), c2, hw,
            fun k hk => sc_ne _ _ (fun e => hk (hF k (by omega)))⟩
        · simp [τ3, τ2, τ1, Locals.set, h1, h2, h3]; exact hfr z h1 h2 h3
        · have e1 : count - (m + 1) = count - m - 1 := by omega
          rw [e1]; exact haux'
        · show count - (τ3 "i").toNat < count - (τ "i").toNat
          have e3 : τ3 "i" = BitVec.ofNat 32 (m + 1) := by simp [τ3]
          rw [e3, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
      obtain ⟨σ', e', hr, ⟨m, hm, hmc, hi', hfr, haux, rfl⟩, h0⟩ :=
        Step.while_inv (εR := εR) (c := c) (i := i0) (M := MA) (F := F) I
          (fun τ => count - (τ "i").toNat) hbody count (σ.set "i" 0) d (by omega)
          ⟨0, d.HP, by omega, by simp, fun z h1 _ _ => by simp [Locals.set, h1], hcp, rfl⟩
      have hlen' : σ' "len" = BitVec.ofNat 32 count :=
        (hfr "len" (by decide) (by decide) (by decide)).trans hlen
      rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .var "len") hi' hlen' (by omega) (by omega)] at h0
      have hme : m = count := by
        by_cases h : m < count
        · rw [if_pos h] at h0; cases h0
        · omega
      subst hme
      rw [Nat.sub_self] at haux
      simp only [flatmem_copy_aux, Option.some.injEq] at haux
      subst haux
      exact ⟨σ', (Step.assign "i" (by decide) (.const 0)).seq hr, hfr⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`flatmem_copy` refines `flatmem_copy_spec`.** -/
theorem flatmemCopy_triple (hL : Layout maxpage num_id cb num_proc pb ib fb) (count src dst : Nat) :
    Triple εR c i0 MA (fun k => fb ≤ k)
      (fun σ d => σ "len" = BitVec.ofNat 32 count ∧ σ "from" = BitVec.ofNat 32 src ∧
        σ "to" = BitVec.ofNat 32 dst ∧ ∃ d1, flatmem_copy_spec count src dst d = some d1)
      (flatmemCopyS fb)
      (fun σ d σ' d' => flatmem_copy_spec count src dst d = some d' ∧
        ∀ z, z ≠ "i" → z ≠ "v" → z ≠ "_" → σ' z = σ z) :=
  Step.triple (fun σ d ⟨h1, h2, h3, d1, hs⟩ => by
    obtain ⟨σ', h, hfr⟩ := flatmemCopy_step εR c i0 hL (fun _ h => h) h1 h2 h3 hs
    exact ⟨σ', d1, h, hs, hfr⟩)

end Region

end FlatMem
