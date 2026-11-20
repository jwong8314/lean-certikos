import CertiKOS.PyL

/-!
# A verified printer from PyL to Python tokens

The Python counterpart of `PrintC.lean`. Python has no braces: a block is
indented, and `a; b; c` reads the same however the sequence was nested. So the
printed text determines a program only up to the nesting of its sequences,
and that is what is proved.

* `Tok`: Python tokens, with `indent`/`dedent` for blocks (as in Python's
  own tokenizer).
* `printC`: the printer. `norm`: a command with every sequence nested to the
  right, the form a parser reads back.
* `parse_print`: **parsing the printed tokens gives back the program, with its
  sequences nested to the right** (`norm c`), for every source command (one
  with no run-time `inAtomic` marker, `Src c`).
* `print_norm`: `c` and `norm c` print the same. So two source programs print
  the same tokens exactly when they are equal up to the nesting of sequences
  (`print_eq_iff`).

Rendering tokens to text (`render`) is lexical and unverified. It writes
comparisons as Python's `(a == b)`, whose `True`/`False` are the integers 1
and 0.
-/

namespace PrintPy

open PyL

inductive Tok
  | id (s : String)
  | num (n : Int)
  | lp | rp | eq | dot | nl
  | op (o : BinOp)
  | kwNot | kwPass | kwObj | kwIf | kwElse | kwWhile | kwWith
  | indent | dedent

def printE : Expr → List Tok
  | .const v => [.num v]
  | .var x => [.id x]
  | .bin o a b => [.lp] ++ printE a ++ [.op o] ++ printE b ++ [.rp]
  | .not a => [.lp, .kwNot] ++ printE a ++ [.rp]

def printC : Cmd → List Tok
  | .skip => [.kwPass, .nl]
  | .assign x e => [.id x, .eq] ++ printE e ++ [.nl]
  | .load x o f => [.id x, .eq, .kwObj] ++ printE o ++ [.dot, .id f, .nl]
  | .store o f e => [.kwObj] ++ printE o ++ [.dot, .id f, .eq] ++ printE e ++ [.nl]
  | .seq a b => printC a ++ printC b
  | .ite e a b =>
      [.kwIf] ++ printE e ++ [.indent] ++ printC a ++ [.dedent, .kwElse, .indent] ++ printC b ++ [.dedent]
  | .while e b => [.kwWhile] ++ printE e ++ [.indent] ++ printC b ++ [.dedent]
  | .atomic b => [.kwWith, .indent] ++ printC b ++ [.dedent]
  | .inAtomic b => printC b

/-- Source commands: no run-time marker. -/
def Src : Cmd → Prop
  | .seq a b => Src a ∧ Src b
  | .ite _ a b => Src a ∧ Src b
  | .while _ b => Src b
  | .atomic b => Src b
  | .inAtomic _ => False
  | _ => True

/-- Put `d` after `c`, nesting to the right. -/
def app : Cmd → Cmd → Cmd
  | .seq x y, d => .seq x (app y d)
  | c, d => .seq c d

/-- Every sequence nested to the right. -/
def norm : Cmd → Cmd
  | .seq a b => app (norm a) (norm b)
  | .ite e a b => .ite e (norm a) (norm b)
  | .while e b => .while e (norm b)
  | .atomic b => .atomic (norm b)
  | .inAtomic b => .inAtomic (norm b)
  | c => c

def appO (c : Cmd) : Option Cmd → Cmd
  | none => c
  | some d => app c d

theorem app_assoc : ∀ a b c : Cmd, app (app a b) c = app a (app b c)
  | .seq x y, b, c => by simp [app, app_assoc y b c]
  | .skip, _, _ => rfl
  | .assign _ _, _, _ => rfl
  | .load _ _ _, _, _ => rfl
  | .store _ _ _, _, _ => rfl
  | .ite _ _ _, _, _ => rfl
  | .while _ _, _, _ => rfl
  | .atomic _, _, _ => rfl
  | .inAtomic _, _, _ => rfl

/-! ## The parser -/

def parseE : Nat → List Tok → Option (Expr × List Tok)
  | 0, _ => none
  | _ + 1, .num k :: r => some (.const k, r)
  | _ + 1, .id x :: r => some (.var x, r)
  | n + 1, .lp :: r =>
    match r with
    | .kwNot :: r0 =>
      match parseE n r0 with
      | some (a, .rp :: r1) => some (.not a, r1)
      | _ => none
    | _ =>
      match parseE n r with
      | some (a, .op o :: r1) =>
        match parseE n r1 with
        | some (b, .rp :: r2) => some (.bin o a b, r2)
        | _ => none
      | _ => none
  | _ + 1, _ => none

/-- The end of a block: no more tokens, or a `dedent`. -/
def closed : List Tok → Bool
  | [] => true
  | .dedent :: _ => true
  | _ => false

/-- Add what follows a statement: nothing (the block ends), or the rest of the block. -/
def withTail (s : Cmd) : Option (Option Cmd × List Tok) → Option (Cmd × List Tok)
  | some (none, r) => some (s, r)
  | some (some d, r) => some (.seq s d, r)
  | none => none

/-- Parse the statements of a block, nesting to the right. -/
def parseSeq : Nat → List Tok → Option (Cmd × List Tok)
  | 0, _ => none
  | n + 1, toks =>
    let tail (r : List Tok) : Option (Option Cmd × List Tok) :=
      if closed r then some (none, r) else (parseSeq n r).map fun p => (some p.1, p.2)
    match toks with
    | .kwPass :: .nl :: r => withTail .skip (tail r)
    | .id x :: .eq :: r =>
      match r with
      | .kwObj :: r0 =>
        match parseE n r0 with
        | some (o, .dot :: .id f :: .nl :: r1) => withTail (.load x o f) (tail r1)
        | _ => none
      | _ =>
        match parseE n r with
        | some (e, .nl :: r1) => withTail (.assign x e) (tail r1)
        | _ => none
    | .kwObj :: r =>
      match parseE n r with
      | some (o, .dot :: .id f :: .eq :: r1) =>
        match parseE n r1 with
        | some (e, .nl :: r2) => withTail (.store o f e) (tail r2)
        | _ => none
      | _ => none
    | .kwIf :: r =>
      match parseE n r with
      | some (e, .indent :: r1) =>
        match parseSeq n r1 with
        | some (a, .dedent :: .kwElse :: .indent :: r2) =>
          match parseSeq n r2 with
          | some (b, .dedent :: r3) => withTail (.ite e a b) (tail r3)
          | _ => none
        | _ => none
      | _ => none
    | .kwWhile :: r =>
      match parseE n r with
      | some (e, .indent :: r1) =>
        match parseSeq n r1 with
        | some (b, .dedent :: r2) => withTail (.while e b) (tail r2)
        | _ => none
      | _ => none
    | .kwWith :: .indent :: r =>
      match parseSeq n r with
      | some (b, .dedent :: r1) => withTail (.atomic b) (tail r1)
      | _ => none
    | _ => none

/-- What follows a statement, as `parseSeq` computes it. -/
def parseTail (n : Nat) (r : List Tok) : Option (Option Cmd × List Tok) :=
  if closed r then some (none, r) else (parseSeq n r).map fun p => (some p.1, p.2)

/-! ## Round trip -/

def sizeE : Expr → Nat
  | .bin _ a b => sizeE a + sizeE b + 1
  | .not a => sizeE a + 1
  | _ => 1

def sizeC : Cmd → Nat
  | .seq a b => sizeC a + sizeC b + 1
  | .ite e a b => sizeE e + sizeC a + sizeC b + 1
  | .while e b => sizeE e + sizeC b + 1
  | .atomic b => sizeC b + 1
  | .inAtomic b => sizeC b + 1
  | .assign _ e => sizeE e + 1
  | .load _ o _ => sizeE o + 1
  | .store o _ e => sizeE o + sizeE e + 1
  | .skip => 1

theorem parseE_print : ∀ (e : Expr) (rest : List Tok) (n : Nat), sizeE e ≤ n →
    parseE n (printE e ++ rest) = some (e, rest)
  | .const v, rest, n + 1, _ => by simp [printE, parseE]
  | .var x, rest, n + 1, _ => by simp [printE, parseE]
  | .not a, rest, n + 1, h => by
    have ha := parseE_print a (.rp :: rest) n (by simp [sizeE] at h; omega)
    simp only [printE, List.append_assoc, List.cons_append, List.nil_append, parseE]
    rw [ha]
  | .bin o a b, rest, n + 1, h => by
    have ha := parseE_print a (.op o :: (printE b ++ .rp :: rest)) n (by simp [sizeE] at h; omega)
    have hb := parseE_print b (.rp :: rest) n (by simp [sizeE] at h; omega)
    have hne : ∀ r r', printE a ++ r ≠ .kwNot :: r' := by
      intro r r'; cases a <;> simp [printE]
    simp only [printE, List.append_assoc, List.cons_append, List.nil_append, parseE]
    split
    · rename_i r0 heq; exact absurd heq (hne _ _)
    · rw [ha]; simp only; rw [hb]
  | .const _, _, 0, h => by simp [sizeE] at h
  | .var _, _, 0, h => by simp [sizeE] at h
  | .not _, _, 0, h => by simp [sizeE] at h
  | .bin _ _ _, _, 0, h => by simp [sizeE] at h

theorem printE_ne_obj (e : Expr) (r r' : List Tok) : printE e ++ r ≠ .kwObj :: r' := by
  cases e <;> simp [printE]

/-! Unfolding `parseSeq` on each statement form. -/

theorem ps_pass (n : Nat) (r : List Tok) :
    parseSeq (n + 1) (.kwPass :: .nl :: r) = withTail .skip (parseTail n r) := rfl

theorem ps_load (n : Nat) (x : String) (r : List Tok) :
    parseSeq (n + 1) (.id x :: .eq :: .kwObj :: r) =
      match parseE n r with
      | some (o, .dot :: .id f :: .nl :: r1) => withTail (.load x o f) (parseTail n r1)
      | _ => none := rfl

theorem ps_assign (n : Nat) (x : String) (r : List Tok) (h : ∀ r0, r ≠ .kwObj :: r0) :
    parseSeq (n + 1) (.id x :: .eq :: r) =
      match parseE n r with
      | some (e, .nl :: r1) => withTail (.assign x e) (parseTail n r1)
      | _ => none := by
  cases r with
  | nil => rfl
  | cons t r0 => cases t <;> first | rfl | exact absurd rfl (h r0)

theorem ps_store (n : Nat) (r : List Tok) :
    parseSeq (n + 1) (.kwObj :: r) =
      match parseE n r with
      | some (o, .dot :: .id f :: .eq :: r1) =>
        match parseE n r1 with
        | some (e, .nl :: r2) => withTail (.store o f e) (parseTail n r2)
        | _ => none
      | _ => none := rfl

theorem ps_if (n : Nat) (r : List Tok) :
    parseSeq (n + 1) (.kwIf :: r) =
      match parseE n r with
      | some (e, .indent :: r1) =>
        match parseSeq n r1 with
        | some (a, .dedent :: .kwElse :: .indent :: r2) =>
          match parseSeq n r2 with
          | some (b, .dedent :: r3) => withTail (.ite e a b) (parseTail n r3)
          | _ => none
        | _ => none
      | _ => none := rfl

theorem ps_while (n : Nat) (r : List Tok) :
    parseSeq (n + 1) (.kwWhile :: r) =
      match parseE n r with
      | some (e, .indent :: r1) =>
        match parseSeq n r1 with
        | some (b, .dedent :: r2) => withTail (.while e b) (parseTail n r2)
        | _ => none
      | _ => none := rfl

theorem ps_with (n : Nat) (r : List Tok) :
    parseSeq (n + 1) (.kwWith :: .indent :: r) =
      match parseSeq n r with
      | some (b, .dedent :: r1) => withTail (.atomic b) (parseTail n r1)
      | _ => none := rfl

theorem withTail_app (s : Cmd) (hs : ∀ d, app s d = .seq s d) (od : Option Cmd) (r : List Tok) :
    withTail s (some (od, r)) = some (appO s od, r) := by
  cases od with
  | none => rfl
  | some d => simp [withTail, appO, hs]

theorem tail_dedent (m : Nat) (r : List Tok) : parseTail m (.dedent :: r) = some (none, .dedent :: r) := by
  simp [parseTail, closed]

/-- A printed command is never the end of a block. -/
theorem print_open : ∀ (c : Cmd) (r : List Tok), closed (printC c ++ r) = false
  | .skip, _ => rfl
  | .assign _ _, _ => rfl
  | .load _ _ _, _ => rfl
  | .store _ _ _, _ => rfl
  | .seq a b, r => by simp only [printC, List.append_assoc]; exact print_open a _
  | .ite _ _ _, _ => rfl
  | .while _ _, _ => rfl
  | .atomic _, _ => rfl
  | .inAtomic b, r => by simp only [printC]; exact print_open b r

/-- **The printer is faithful.** Parsing a printed source command, followed by
anything the parser can read as the rest of the block, gives the command with
its sequences nested to the right, followed by that rest. -/
theorem parseSeq_print : ∀ (c : Cmd), Src c → ∀ (rest rest' : List Tok) (od : Option Cmd) (m0 : Nat),
    (∀ m, m0 ≤ m → parseTail m rest = some (od, rest')) →
    ∀ n, m0 + sizeC c ≤ n → parseSeq n (printC c ++ rest) = some (appO (norm c) od, rest')
  | .skip, _, rest, rest', od, m0, ht, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [sizeC] at hn; omega⟩
    simp only [printC, List.cons_append, List.nil_append, ps_pass]
    rw [ht k (by simp [sizeC] at hn; omega)]
    exact withTail_app _ (fun _ => rfl) od rest'
  | .assign x e, _, rest, rest', od, m0, ht, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [sizeC] at hn; omega⟩
    simp only [printC, List.append_assoc, List.cons_append, List.nil_append]
    rw [ps_assign k x _ (fun r0 => printE_ne_obj e _ r0),
      parseE_print e _ k (by simp [sizeC] at hn; omega)]
    simp only
    rw [ht k (by simp [sizeC] at hn; omega)]
    exact withTail_app _ (fun _ => rfl) od rest'
  | .load x o f, _, rest, rest', od, m0, ht, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [sizeC] at hn; omega⟩
    simp only [printC, List.append_assoc, List.cons_append, List.nil_append, ps_load]
    rw [parseE_print o _ k (by simp [sizeC] at hn; omega)]
    simp only
    rw [ht k (by simp [sizeC] at hn; omega)]
    exact withTail_app _ (fun _ => rfl) od rest'
  | .store o f e, _, rest, rest', od, m0, ht, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [sizeC] at hn; omega⟩
    simp only [printC, List.append_assoc, List.cons_append, List.nil_append, ps_store]
    rw [parseE_print o _ k (by simp [sizeC] at hn; omega)]
    simp only
    rw [parseE_print e _ k (by simp [sizeC] at hn; omega)]
    simp only
    rw [ht k (by simp [sizeC] at hn; omega)]
    exact withTail_app _ (fun _ => rfl) od rest'
  | .seq a b, hs, rest, rest', od, m0, ht, n, hn => by
    have hb := parseSeq_print b hs.2 rest rest' od m0 ht
    have htb : ∀ m, m0 + sizeC b ≤ m →
        parseTail m (printC b ++ rest) = some (some (appO (norm b) od), rest') := by
      intro m hm
      simp only [parseTail, print_open b rest, Bool.false_eq_true, ite_false, hb m hm, Option.map_some]
    have ha := parseSeq_print a hs.1 (printC b ++ rest) rest' (some (appO (norm b) od)) (m0 + sizeC b) htb n
      (by simp [sizeC] at hn; omega)
    simp only [printC, List.append_assoc]
    rw [ha]
    cases od with
    | none => rfl
    | some d => simp [appO, norm, app_assoc]
  | .ite e a b, hs, rest, rest', od, m0, ht, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [sizeC] at hn; omega⟩
    have ha := parseSeq_print a hs.1 (.dedent :: .kwElse :: .indent :: (printC b ++ .dedent :: rest)) _ none 0
      (fun m _ => tail_dedent m _) k (by simp [sizeC] at hn; omega)
    have hb := parseSeq_print b hs.2 (.dedent :: rest) _ none 0 (fun m _ => tail_dedent m _) k
      (by simp [sizeC] at hn; omega)
    simp only [printC, List.append_assoc, List.cons_append, List.nil_append, ps_if]
    rw [parseE_print e _ k (by simp [sizeC] at hn; omega)]
    simp only
    rw [ha]; simp only [appO]
    rw [hb]; simp only [appO]
    rw [ht k (by simp [sizeC] at hn; omega)]
    exact withTail_app _ (fun _ => rfl) od rest'
  | .while e b, hs, rest, rest', od, m0, ht, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [sizeC] at hn; omega⟩
    have hb := parseSeq_print b hs (.dedent :: rest) _ none 0 (fun m _ => tail_dedent m _) k
      (by simp [sizeC] at hn; omega)
    simp only [printC, List.append_assoc, List.cons_append, List.nil_append, ps_while]
    rw [parseE_print e _ k (by simp [sizeC] at hn; omega)]
    simp only
    rw [hb]; simp only [appO]
    rw [ht k (by simp [sizeC] at hn; omega)]
    exact withTail_app _ (fun _ => rfl) od rest'
  | .atomic b, hs, rest, rest', od, m0, ht, n, hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp [sizeC] at hn; omega⟩
    have hb := parseSeq_print b hs (.dedent :: rest) _ none 0 (fun m _ => tail_dedent m _) k
      (by simp [sizeC] at hn; omega)
    simp only [printC, List.append_assoc, List.cons_append, List.nil_append, ps_with]
    rw [hb]; simp only [appO]
    rw [ht k (by simp [sizeC] at hn; omega)]
    exact withTail_app _ (fun _ => rfl) od rest'
  | .inAtomic _, hs, _, _, _, _, _, _, _ => hs.elim

theorem tail_nil (m : Nat) : parseTail m [] = some (none, []) := by simp [parseTail, closed]

/-- **Round trip**: parsing a printed source program gives it back, with its
sequences nested to the right. -/
theorem parse_print (c : Cmd) (hs : Src c) (n : Nat) (hn : sizeC c ≤ n) :
    parseSeq n (printC c) = some (norm c, []) := by
  simpa [appO] using parseSeq_print c hs [] [] none 0 (fun m _ => tail_nil m) n (by omega)

theorem print_app : ∀ a b : Cmd, printC (app a b) = printC a ++ printC b
  | .seq x y, b => by simp [app, printC, print_app y b]
  | .skip, _ => rfl
  | .assign _ _, _ => rfl
  | .load _ _ _, _ => rfl
  | .store _ _ _, _ => rfl
  | .ite _ _ _, _ => rfl
  | .while _ _, _ => rfl
  | .atomic _, _ => rfl
  | .inAtomic _, _ => rfl

/-- Renesting sequences does not change what is printed. -/
theorem print_norm : ∀ c : Cmd, printC (norm c) = printC c
  | .seq a b => by simp [norm, print_app, printC, print_norm a, print_norm b]
  | .ite e a b => by simp [norm, printC, print_norm a, print_norm b]
  | .while e b => by simp [norm, printC, print_norm b]
  | .atomic b => by simp [norm, printC, print_norm b]
  | .inAtomic b => by simp [norm, printC, print_norm b]
  | .skip => rfl
  | .assign _ _ => rfl
  | .load _ _ _ => rfl
  | .store _ _ _ => rfl

/-- **The text determines the program up to the nesting of sequences.** -/
theorem print_eq_iff {c d : Cmd} (hc : Src c) (hd : Src d) : printC c = printC d ↔ norm c = norm d := by
  constructor
  · intro h
    have h1 := parse_print c hc (sizeC c + sizeC d) (by omega)
    have h2 := parse_print d hd (sizeC c + sizeC d) (by omega)
    rw [h, h2] at h1
    simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h1
    exact h1.symm
  · intro h
    rw [← print_norm c, ← print_norm d, h]

/-! ## Rendering (lexical, unverified) -/

def opPy : BinOp → String
  | .add => " + " | .sub => " - " | .mul => " * " | .fdiv => " // " | .fmod => " % "
  | .eq => " == " | .ne => " != " | .lt => " < " | .le => " <= "
  | .band => " & " | .bor => " | " | .shl => " << "

def pad (lvl : Nat) : String := String.join (List.replicate lvl "    ")

/-- Tokens to Python text. `lvl` is the indentation level, and `start` says
whether we are at the start of a line. -/
def renderGo : Nat → Bool → List Tok → String
  | _, _, [] => ""
  | lvl, _, .nl :: ts => "\n" ++ renderGo lvl true ts
  | lvl, _, .indent :: ts => ":\n" ++ renderGo (lvl + 1) true ts
  | lvl, _, .dedent :: ts => renderGo (lvl - 1) true ts
  | lvl, start, t :: ts =>
    let txt := match t with
      | .id s => if s = "$r" then "_r" else s
      | .num n => toString n
      | .lp => "(" | .rp => ")" | .eq => " = " | .dot => "]."
      | .op o => opPy o
      | .kwNot => "not " | .kwPass => "pass" | .kwObj => "OBJ[" | .kwIf => "if " | .kwElse => "else"
      | .kwWhile => "while " | .kwWith => "with L"
      | _ => ""
    (if start then pad lvl else "") ++ txt ++ renderGo lvl false ts

def render (lvl : Nat) (ts : List Tok) : String := renderGo lvl true ts

end PrintPy
