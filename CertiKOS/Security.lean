import CertiKOS.ConfidentialityPF

/-!
# mCertiKOS security: the three unwinding conditions, ported

Ported from `security/Security.v` (lemmas `conf`, `integ`, `conf_restore`),
which apply the integrity and confidentiality theorems to a step of the top
layer. Here a step is one passage through the kernel.

* `Trap`: what the user program chose: a system call, a page fault at an
  address, or a yield, with the registers at the trap.
* `KPass t d d' rs'`: **one passage through the kernel**, at the level of the
  specifications: from user mode in state `d`, the trap `t` is handled and
  the machine is in user mode again in state `d'` with registers `rs'`. For a
  yield, the process then running is another one.
* `SecInv`: the invariants the security proof assumes of a state
  (`secure_inv`).
* `integ`: **integrity.** A passage during which process `i` is not running,
  before or after, does not change what `i` observes.
* `conf`: **confidentiality.** From two states the running process cannot
  tell apart, the same trap leads to two states it cannot tell apart, and to
  the same registers if it is still running.
* `conf_restore`: **confidentiality when a process is resumed.** From two
  states a parked process could not tell apart, any two passages that resume
  it lead to states it cannot tell apart and to the same registers.

These are the hypotheses of the unwinding theorem that gives noninterference
for whole executions; it is in `SecurityBigstep.lean`.

What differs: mCertiKOS's step is one instruction of the machine; a yield and
the `proc_start_user` of the process resumed are two steps there and one
passage here. The invariants are assumed of the states where they are used
(mCertiKOS proves them preserved, `secure_inv_preserved`).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Security

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt PProc TTrap TSysCall

/-- What the user program chose at a trap. -/
inductive Trap
  | syscall (rs : UContext)
  | pgf (rs : UContext) (vadr : Nat)
  | yield (rs : UContext) (rsK : KCtx)

section
variable (num_id mc num_chan num_proc maxpage : Nat) (code : Nat → Stmt KPrim) (pstart : Nat) (elf : Nat → Nat)

/-- **One passage through the kernel.** -/
inductive KPass : Trap → UData → UData → UContext → Prop
  | syscall {d d1 d2 d3 : UData} {rs rs' : UContext} (h1 : proc_exit_user_spec rs d = some d1)
      (h2 : sys_dispatch_c_spec num_id mc num_chan code pstart elf d1 = some d2)
      (h3 : proc_start_user_spec d2 = some (d3, rs')) : KPass (.syscall rs) d d3 rs'
  | pgf {d d1 d2 d3 : UData} {rs rs' : UContext} {vadr : Nat} (h1 : proc_exit_user_spec rs d = some d1)
      (h2 : ptfault_resv_spec maxpage num_proc vadr d1 = some d2)
      (h3 : proc_start_user_spec d2 = some (d3, rs')) : KPass (.pgf rs vadr) d d3 rs'
  | yield {d d1 d3 : UData} {rs rs' : UContext} {rsK : KCtx} {la : Nat} {ql : List Nat}
      (h1 : proc_exit_user_spec rs d = some d1) (hq : d.abq num_chan = .AbQValid ql)
      (hla : ql.getLastD num_proc = la) (hne : la ≠ d.cid)
      (h3 : proc_start_user_spec (putK d1 (yieldOut num_chan la ql rsK (toK d1))) = some (d3, rs')) :
      KPass (.yield rs rsK) d d3 rs'

end

/-- The invariants the security proof assumes of a state, for observer `i`
(`secure_inv`). -/
structure SecInv (num_id mc i : Nat) (d : UData) : Prop where
  cv : Container_valid num_id mc d.AC
  cur : (d.AC d.cid).cused = true
  obs : (d.AC i).cused = true
  mu : MappedUsed i d.toPTData
  fn : FreeNone d.toPTData
  init : d.init = true
  ihost : d.ihost = true

variable {num_id mc num_chan num_proc maxpage : Nat} {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
variable {i : Nat}

/-- The dispatcher does not change the running process. -/
theorem dispatch_cid {d d' : UData} (h : sys_dispatch_c_spec num_id mc num_chan code pstart elf d = some d') :
    d'.cid = d.cid := by
  have o := obs_dispatch (i := d.cid) h rfl
  have hr : (observe d.cid d).observe_cid = true := obs_running rfl
  have : (observe d.cid d').observe_cid = true := by
    rw [o]
    revert hr
    generalize observe d.cid d = o'
    intro hr
    unfold obsDispatch obsTrapCreate obsGetQuota obsSetReg obsCreate
    repeat' split
    all_goals exact hr
  exact (running_of_obs this).symm

/-- Who runs after a system call or a page fault: the same process. -/
theorem pass_cid {t : Trap} {d d' : UData} {rs' : UContext}
    (hp : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d' rs') :
    (∀ rs rsK, t ≠ .yield rs rsK) → d'.cid = d.cid := by
  intro hny
  cases hp with
  | @syscall _ d1 d2 _ rs _ h1 h2 h3 =>
    have c3 : d'.cid = d2.cid := by rw [(start_shape h3).1]
    have c2 : d2.cid = d1.cid := dispatch_cid h2
    have c1 : d1.cid = d.cid := by rw [(exit_shape h1).1]
    exact c3.trans (c2.trans c1)
  | @pgf _ d1 d2 _ rs _ vadr h1 h2 h3 =>
    have c3 : d'.cid = d2.cid := by rw [(start_shape h3).1]
    have c2 : d2.cid = d1.cid := ptfault_cid h2
    have c1 : d1.cid = d.cid := by rw [(exit_shape h1).1]
    exact c3.trans (c2.trans c1)
  | yield h1 hq hla hne h3 => exact absurd rfl (hny _ _)

/-- **Integrity** (`integ`). -/
theorem integ {t : Trap} {d d' : UData} {rs' : UContext} (hI : SecInv num_id mc i d)
    (hp : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d' rs') (h1 : i ≠ d.cid)
    (h2 : i ≠ d'.cid) : ObsEq i d d' := by
  cases hp with
  | syscall g1 g2 g3 => exact integrity_syscall hI.cv hI.cur hI.obs g1 g2 g3 h1
  | pgf g1 g2 g3 => exact integrity_pgf hI.mu g1 g2 g3 h1
  | @yield _ d1 _ rs _ rsK la ql g1 hq hla hne g3 =>
    have hc : d'.cid = la := by rw [(start_shape g3).1]; rfl
    have hil : i ≠ la := fun e => h2 (by rw [hc]; exact e)
    exact (integrity_yield g1 h1 hil).trans (integ_proc_start_user g3 hil)

/-- **Confidentiality** (`conf`). -/
theorem conf {t : Trap} {d d' e e' : UData} {r1 r2 : UContext} (hI1 : SecInv num_id mc i d)
    (hI2 : SecInv num_id mc i e) (p1 : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d' r1)
    (p2 : KPass num_id mc num_chan num_proc maxpage code pstart elf t e e' r2) (hi : i = d.cid)
    (h : ObsEq i d e) : ObsEq i d' e' ∧ (i = d'.cid → r1 = r2) := by
  have hi2 : i = e.cid := h.hcid.1 hi
  cases p1 with
  | syscall h1 h2 h3 =>
    cases p2 with
    | syscall g1 g2 g3 =>
      obtain ⟨a, b⟩ := confidentiality_syscall h1 h2 h3 g1 g2 g3 hi h
      exact ⟨a, fun _ => b⟩
  | pgf h1 h2 h3 =>
    cases p2 with
    | pgf g1 g2 g3 =>
      obtain ⟨a, b⟩ := confidentiality_pgf hI1.mu hI2.mu hI1.fn hI2.fn h1 h2 h3 g1 g2 g3 hi h
      exact ⟨a, fun _ => b⟩
  | @yield _ d1 _ rs _ rsK la1 ql1 h1 hq1 hla1 hne1 h3 =>
    cases p2 with
    | @yield _ e1 _ _ _ _ la2 ql2 g1 hq2 hla2 hne2 g3 =>
      have hy := confidentiality_yield (i := i) (nc := num_chan) (la1 := la1) (la2 := la2) (ql1 := ql1)
        (ql2 := ql2) (rsK := rsK) h1 g1 hi hne1 hne2 h
      have n1 : i ≠ la1 := fun e' => hne1 (e'.symm.trans hi)
      have n2 : i ≠ la2 := fun e' => hne2 (e'.symm.trans hi2)
      refine ⟨((integ_proc_start_user h3 n1).symm.trans hy).trans (integ_proc_start_user g3 n2), fun e' => ?_⟩
      have hc : d'.cid = la1 := by rw [(start_shape h3).1]; rfl
      exact absurd (e'.trans hc) n1

/-- **Confidentiality when a process is resumed** (`conf_restore`). -/
theorem conf_restore {t1 t2 : Trap} {d d' e e' : UData} {r1 r2 : UContext} (hI1 : SecInv num_id mc i d)
    (hI2 : SecInv num_id mc i e) (p1 : KPass num_id mc num_chan num_proc maxpage code pstart elf t1 d d' r1)
    (p2 : KPass num_id mc num_chan num_proc maxpage code pstart elf t2 e e' r2) (hi : i ≠ d.cid)
    (h1 : i = d'.cid) (h2 : i = e'.cid) (h : ObsEq i d e) : ObsEq i d' e' ∧ r1 = r2 := by
  have hie : i ≠ e.cid := fun e0 => hi (h.hcid.2 e0)
  have hc1 := pass_cid p1
  have hc2 := pass_cid p2
  cases p1 with
  | syscall a1 a2 a3 => exact absurd (h1.trans (hc1 (fun _ _ => nofun))) hi
  | pgf a1 a2 a3 => exact absurd (h1.trans (hc1 (fun _ _ => nofun))) hi
  | @yield _ d1 _ rs1 _ rsK1 la1 ql1 a1 aq ala ane a3 =>
    cases p2 with
    | syscall b1 b2 b3 => exact absurd (h2.trans (hc2 (fun _ _ => nofun))) hie
    | pgf b1 b2 b3 => exact absurd (h2.trans (hc2 (fun _ _ => nofun))) hie
    | @yield _ e1 _ rs2 _ rsK2 la2 ql2 b1 bq bla bne b3 =>
      -- both passages resumed `i`
      have c1 : d'.cid = la1 := by rw [(start_shape a3).1]; rfl
      have c2 : e'.cid = la2 := by rw [(start_shape b3).1]; rfl
      have l1 : i = la1 := h1.trans c1
      have l2 : i = la2 := h2.trans c2
      subst l1
      subst l2
      obtain ⟨o, -⟩ := confidentiality_restore (i := i) (nc := num_chan) (ql1 := ql1) (ql2 := ql2)
        (rsK1 := rsK1) (rsK2 := rsK2) a1 b1 hi hI1.init hI2.init hI1.ihost hI2.ihost h
      exact conf_proc_start_user a3 b3 rfl o

end Security
