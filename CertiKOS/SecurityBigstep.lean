import CertiKOS.Security

/-!
# mCertiKOS security: noninterference from the unwinding conditions

Ported in outline from `security/SecurityBigstep.v` and the end of
`security/Security.v`.

The three unwinding conditions are about one passage through the kernel.
Noninterference is about executions: whatever the other processes do, process
`i` sees the same thing each time it returns from the kernel.

* `Idle`: passages of other processes while `i` is parked.
* `BStep t d d' r`: **a big step of process `i`.** From a state where it
  runs, its trap `t` is handled, and the machine goes on until `i` is in user
  mode again, in state `d'` with registers `r`. Either it never stopped
  running (a system call, a page fault), or it yielded, others ran, and one
  of them yielded back to it.
* `idle_obs`: while `i` is parked, what it observes does not change
  (integrity, step by step).
* `bigstep_conf`: **confidentiality of a big step.** From two states `i`
  cannot tell apart, the same trap, however the other processes behave in
  between: `i` returns to user mode in two states it cannot tell apart, with
  the same registers.
* `Prog`, `Exec`: a user program as the kernel sees it, and its execution.
  `noninterference`: **two executions of the same program from states it
  cannot tell apart stay in step for ever**: after any number of its returns
  from the kernel the states are indistinguishable and the registers equal,
  so its next trap is the same (`next_trap_eq`).

What differs:
* In mCertiKOS a user program is machine code, and its steps in user mode are
  steps of the machine. User code is not modelled here. A program is the
  function `Prog` from what the process can see, its registers and its
  observation, to the trap it makes next. That a real program is such a
  function is mCertiKOS's confidentiality of user-mode instructions, which is
  not ported.
* Here `SecInv` is a premise of every step. `TSecInv.lean` shows it
  preserved, with the kernel invariant `KInv`, and gives
  `noninterference_inv`, which assumes the invariants only of the first
  states.
* mCertiKOS's theorem is also about what the process outputs; there is no
  output device here.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Security

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt PProc TTrap TSysCall

section
variable (num_id mc num_chan num_proc maxpage : Nat) (code : Nat → Stmt KPrim) (pstart : Nat) (elf : Nat → Nat)
variable (i : Nat)

/-- Passages of other processes while `i` is parked. -/
inductive Idle : UData → UData → Prop
  | refl (d : UData) : Idle d d
  | step {t : Trap} {d d1 d2 : UData} {rs : UContext} (hI : SecInv num_id mc i d)
      (hp : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d1 rs) (h1 : i ≠ d.cid)
      (h2 : i ≠ d1.cid) (hrest : Idle d1 d2) : Idle d d2

/-- **A big step of process `i`**: its trap is handled, and the machine runs
until `i` is in user mode again. -/
inductive BStep : Trap → UData → UData → UContext → Prop
  | stay {t : Trap} {d d' : UData} {r : UContext} (hI : SecInv num_id mc i d)
      (hp : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d' r) (hi : i = d.cid)
      (hi' : i = d'.cid) : BStep t d d' r
  | away {t t2 : Trap} {d d1 d2 d' : UData} {r1 r : UContext} (hI : SecInv num_id mc i d)
      (hp : KPass num_id mc num_chan num_proc maxpage code pstart elf t d d1 r1) (hi : i = d.cid)
      (h1 : i ≠ d1.cid) (hidle : Idle num_id mc num_chan num_proc maxpage code pstart elf i d1 d2)
      (hI2 : SecInv num_id mc i d2)
      (hp2 : KPass num_id mc num_chan num_proc maxpage code pstart elf t2 d2 d' r) (h2 : i ≠ d2.cid)
      (hi' : i = d'.cid) : BStep t d d' r

/-- A user program, as far as the kernel is concerned: the trap it makes
next, from its registers and what it observes. -/
abbrev Prog := UContext → MyObs → Trap

/-- An execution of process `i` running program `P`: `n` of its returns to
user mode. -/
inductive Exec (P : Prog) : Nat → UData → UContext → UData → UContext → Prop
  | zero (d : UData) (r : UContext) : Exec P 0 d r d r
  | succ {n : Nat} {d d1 d' : UData} {r r1 r' : UContext}
      (hb : BStep num_id mc num_chan num_proc maxpage code pstart elf i (P r (observe i d)) d d1 r1)
      (hrest : Exec P n d1 r1 d' r') : Exec P (n + 1) d r d' r'

end

variable {num_id mc num_chan num_proc maxpage : Nat} {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
variable {i : Nat}

/-- **While a process is parked, what it observes does not change.** -/
theorem idle_obs {d d' : UData} (h : Idle num_id mc num_chan num_proc maxpage code pstart elf i d d') :
    ObsEq i d d' := by
  induction h with
  | refl d => exact ObsEq.refl i d
  | step hI hp h1 h2 _ ih => exact (integ hI hp h1 h2).trans ih

/-- **Confidentiality of a big step.** -/
theorem bigstep_conf {t : Trap} {d d' e e' : UData} {r1 r2 : UContext}
    (b1 : BStep num_id mc num_chan num_proc maxpage code pstart elf i t d d' r1)
    (b2 : BStep num_id mc num_chan num_proc maxpage code pstart elf i t e e' r2) (h : ObsEq i d e) :
    ObsEq i d' e' ∧ r1 = r2 := by
  cases b1 with
  | stay hI hp hi hi' =>
    cases b2 with
    | stay gI gp gi gi' =>
      obtain ⟨o, f⟩ := conf hI gI hp gp hi h
      exact ⟨o, f hi'⟩
    | away gI gp gi g1 gidle gI2 gp2 g2 gi' =>
      obtain ⟨o, -⟩ := conf hI gI hp gp hi h
      exact absurd (o.hcid.1 hi') g1
  | away hI hp hi h1 hidle hI2 hp2 h2 hi' =>
    cases b2 with
    | stay gI gp gi gi' =>
      obtain ⟨o, -⟩ := conf hI gI hp gp hi h
      exact absurd (o.hcid.2 gi') h1
    | away gI gp gi g1 gidle gI2 gp2 g2 gi' =>
      obtain ⟨o1, -⟩ := conf hI gI hp gp hi h
      have o2 := ((idle_obs hidle).symm.trans o1).trans (idle_obs gidle)
      exact conf_restore hI2 gI2 hp2 gp2 h2 hi' gi' o2

/-- **Noninterference.** Two executions of one program by process `i`, from
states it cannot tell apart and with the same registers: after any number of
its returns from the kernel, it still cannot tell the states apart, and its
registers are the same. What the other processes did in between, and how
long they took, makes no difference. -/
theorem noninterference (P : Prog) :
    ∀ (n : Nat) {d e d' e' : UData} {r rd re : UContext},
      Exec num_id mc num_chan num_proc maxpage code pstart elf i P n d r d' rd →
      Exec num_id mc num_chan num_proc maxpage code pstart elf i P n e r e' re → ObsEq i d e →
      ObsEq i d' e' ∧ rd = re
  | 0, _, _, _, _, _, _, _, x1, x2, h => by
    cases x1
    cases x2
    exact ⟨h, rfl⟩
  | n + 1, _, _, _, _, _, _, _, x1, x2, h => by
    cases x1 with
    | succ hb hrest =>
      cases x2 with
      | succ gb grest =>
        rw [← (obsEq_convert _ _ _).1 h] at gb
        obtain ⟨o, hr⟩ := bigstep_conf hb gb h
        subst hr
        exact noninterference P n hrest grest o

/-- The program makes the same trap next in both executions. -/
theorem next_trap_eq (P : Prog) {n : Nat} {d e d' e' : UData} {r rd re : UContext}
    (x1 : Exec num_id mc num_chan num_proc maxpage code pstart elf i P n d r d' rd)
    (x2 : Exec num_id mc num_chan num_proc maxpage code pstart elf i P n e r e' re) (h : ObsEq i d e) :
    P rd (observe i d') = P re (observe i e') := by
  obtain ⟨o, hr⟩ := noninterference P n x1 x2 h
  rw [hr, (obsEq_convert _ _ _).1 o]

end Security
