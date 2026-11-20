import CertiKOS.TSysCall

/-!
# mCertiKOS security: the observation function, ported

Ported from `security/ObsEq.v` (Costanzo, Shao, Gu, PLDI'16, section 4).

The security property is stated with an observation function: what part of
the kernel's state a process can see. Two states are indistinguishable to
process `i` when `i` observes the same thing in both.

* `vread`: what `i` sees at a user virtual address: the word it is mapped to,
  through `i`'s page table. The physical page is hidden, which is the point.
* `vread_perm`: the permission of the mapping and the kind of page mapped.
* `MyObs`, `observe`: the observation. Besides the address space: what is
  left of `i`'s quota, how many children it has, whether its container is in
  use, whether it is the running process, its kernel context, its user
  context, and, if it is running, the mode flags.
* `ObsEq`: observable equivalence, field by field (`my_obs_eq`).
* `obsEq_convert`: `ObsEq i d1 d2 ↔ observe i d1 = observe i d2`.
* `ObsEq.refl`, `ObsEq.symm`, `ObsEq.trans`.

What differs: flat memory is indexed by word, so `vread` gives the word that
holds the address. mCertiKOS also observes the output buffer (`devout`) and
the trap information (`ti`), which the state here does not have.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Security

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt

/-- `vread`: the word of flat memory that user address `vadr` of process `i`
is mapped to, if it is mapped. -/
def vread (i vadr : Nat) (ptp : PMapPool) (hp : Nat → Option Val) : Option (Option Val) :=
  if 1073741824 ≤ vadr ∧ vadr < 4026531840 then
    match ptp i (PDX vadr) with
    | .PDEValid _ pte =>
      match pte (PTX vadr) with
      | .PTEValid pi _ => some (hp (pi * 1024 + vadr % 4096 / 4))
      | _ => none
    | _ => none
  else none

/-- What can be seen of a mapping. -/
inductive ObsPerm
  | ObsValid (p : PTPerm) (pp : PPgInfo)
  | ObsPDEID
  | ObsPDEUnPresent
  | ObsPDEUndef
  | ObsPTEUnPresent
  | ObsPTEUndef

/-- `vread_perm`: the permission bits of the mapping of `vadr`. -/
def vread_perm (i vadr : Nat) (ptp : PMapPool) (pp : Nat → PPgInfo) : Option ObsPerm :=
  if 1073741824 ≤ vadr ∧ vadr < 4026531840 then
    match ptp i (PDX vadr) with
    | .PDEValid _ pte =>
      match pte (PTX vadr) with
      | .PTEValid v p => some (.ObsValid p (pp v))
      | .PTEUnPresent => some .ObsPTEUnPresent
      | .PTEUndef => some .ObsPTEUndef
    | .PDEUnPresent => some .ObsPDEUnPresent
    | .PDEID => some .ObsPDEID
    | .PDEUndef => some .ObsPDEUndef
  else none

/-- The type of observations. -/
structure MyObs where
  observe_HP : Nat → Option (Option Val)
  observe_perm : Nat → Option ObsPerm
  observe_AC_quota : Int
  observe_AC_nchildren : Nat
  observe_AC_used : Bool
  observe_cid : Bool
  observe_kctxt : KCtx
  observe_uctxt : UContext
  observe_ikern : Option Bool
  observe_ihost : Option Bool
  observe_pg : Option Bool
  observe_ipt : Option Bool
  observe_init : Option Bool

/-- **The observation function**: what process `i` can see of the state. -/
def observe (i : Nat) (d : UData) : MyObs where
  observe_HP := fun vadr => vread i vadr d.ptpool d.HP
  observe_perm := fun vadr => vread_perm i vadr d.ptpool d.pperm
  observe_AC_quota := ((d.AC i).cquota : Int) - (d.AC i).cusage
  observe_AC_nchildren := (d.AC i).cchildren.length
  observe_AC_used := (d.AC i).cused
  observe_cid := decide (i = d.cid)
  observe_kctxt := d.kctxt i
  observe_uctxt := d.uctxt i
  observe_ikern := if i = d.cid then some d.ikern else none
  observe_ihost := if i = d.cid then some d.ihost else none
  observe_pg := if i = d.cid then some d.pg else none
  observe_ipt := if i = d.cid then some d.ipt else none
  observe_init := if i = d.cid then some d.init else none

/-- **Observable equivalence** (`my_obs_eq`). -/
structure ObsEq (i : Nat) (d1 d2 : UData) : Prop where
  hHP : ∀ vadr, vread i vadr d1.ptpool d1.HP = vread i vadr d2.ptpool d2.HP
  hperm : ∀ vadr, vread_perm i vadr d1.ptpool d1.pperm = vread_perm i vadr d2.ptpool d2.pperm
  hquota : ((d1.AC i).cquota : Int) - (d1.AC i).cusage = ((d2.AC i).cquota : Int) - (d2.AC i).cusage
  hnchildren : (d1.AC i).cchildren.length = (d2.AC i).cchildren.length
  hused : (d1.AC i).cused = (d2.AC i).cused
  hcid : i = d1.cid ↔ i = d2.cid
  hkctxt : d1.kctxt i = d2.kctxt i
  huctxt : d1.uctxt i = d2.uctxt i
  hikern : i = d1.cid → d1.ikern = d2.ikern
  hihost : i = d1.cid → d1.ihost = d2.ihost
  hpg : i = d1.cid → d1.pg = d2.pg
  hipt : i = d1.cid → d1.ipt = d2.ipt
  hinit : i = d1.cid → d1.init = d2.init

theorem flag_eq {i c1 c2 : Nat} {x1 x2 : Bool} (hc : i = c1 ↔ i = c2) (hx : i = c1 → x1 = x2) :
    (if i = c1 then some x1 else none) = (if i = c2 then some x2 else none) := by
  by_cases h : i = c1
  · rw [if_pos h, if_pos (hc.1 h), hx h]
  · rw [if_neg h, if_neg (fun e => h (hc.2 e))]

theorem flag_of_eq {i c1 c2 : Nat} {x1 x2 : Bool}
    (h : (if i = c1 then some x1 else none) = (if i = c2 then some x2 else none)) (e : i = c1) : x1 = x2 := by
  rw [if_pos e] at h
  by_cases h2 : i = c2
  · rw [if_pos h2] at h; exact Option.some.inj h
  · rw [if_neg h2] at h; cases h

/-- **The relation is equality of observations.** -/
theorem obsEq_convert (i : Nat) (d1 d2 : UData) : ObsEq i d1 d2 ↔ observe i d1 = observe i d2 := by
  constructor
  · intro h
    unfold observe
    rw [funext h.hHP, funext h.hperm, h.hquota, h.hnchildren, h.hused, h.hkctxt, h.huctxt,
      flag_eq h.hcid h.hikern, flag_eq h.hcid h.hihost, flag_eq h.hcid h.hpg, flag_eq h.hcid h.hipt,
      flag_eq h.hcid h.hinit, show decide (i = d1.cid) = decide (i = d2.cid) from decide_eq_decide.2 h.hcid]
  · intro h
    have hc : i = d1.cid ↔ i = d2.cid := decide_eq_decide.1 (congrArg MyObs.observe_cid h)
    exact ⟨fun v => congrFun (congrArg MyObs.observe_HP h) v, fun v => congrFun (congrArg MyObs.observe_perm h) v,
      congrArg MyObs.observe_AC_quota h, congrArg MyObs.observe_AC_nchildren h, congrArg MyObs.observe_AC_used h,
      hc, congrArg MyObs.observe_kctxt h, congrArg MyObs.observe_uctxt h,
      flag_of_eq (congrArg MyObs.observe_ikern h), flag_of_eq (congrArg MyObs.observe_ihost h),
      flag_of_eq (congrArg MyObs.observe_pg h), flag_of_eq (congrArg MyObs.observe_ipt h),
      flag_of_eq (congrArg MyObs.observe_init h)⟩

theorem ObsEq.refl (i : Nat) (d : UData) : ObsEq i d d := (obsEq_convert i d d).2 rfl

theorem ObsEq.symm {i : Nat} {d1 d2 : UData} (h : ObsEq i d1 d2) : ObsEq i d2 d1 :=
  (obsEq_convert i d2 d1).2 ((obsEq_convert i d1 d2).1 h).symm

theorem ObsEq.trans {i : Nat} {d1 d2 d3 : UData} (h1 : ObsEq i d1 d2) (h2 : ObsEq i d2 d3) : ObsEq i d1 d3 :=
  (obsEq_convert i d1 d3).2 (((obsEq_convert i d1 d2).1 h1).trans ((obsEq_convert i d2 d3).1 h2))

end Security
