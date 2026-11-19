import CertiKOS.ClightL

/-!
# A verified printer from ClightL to C tokens

`Bench/EmitC.lean` turns the verified ASTs into C source. Here the printer is
proved to lose nothing: a parser reads the printed tokens back to the same AST.

* `Tok`: C tokens (identifiers, numbers, punctuation, `if`/`else`/`while`, the
  binary operators).
* `printE`, `printS`: the printer. Binary expressions are fully parenthesized,
  and every sequence is printed as a block `{ a b }`, so the nesting of the AST
  is visible in the text. A primitive call `x = p(e₁, …)` uses the
  primitive's C name.
* `parseE`, `parseS`: a parser for exactly this output, with fuel.
* `parse_print`: **parsing the printed tokens gives back the AST**, for every
  statement and any primitive naming whose names can be read back
  (`ofName (name p) = some p`). So the printer is injective, and the C text is
  a faithful rendering of the proved code.

The only unverified step left is `render`, which joins tokens with spaces. It
is a lexical layer with no structure (constants are printed in decimal with a
`u` suffix).
-/

namespace PrintC

open ClightL

inductive Tok
  | id (s : String)
  | num (n : Nat)
  | lp | rp | lb | rb | semi | comma | eq
  | op (o : BinOp)
  | kwIf | kwElse | kwWhile

variable {Pn : Type} (name : Pn → String) (ofName : String → Option Pn)

def printE : Expr → List Tok
  | .const v => [.num v.toNat]
  | .var x => [.id x]
  | .bin o a b => [.lp] ++ printE a ++ [.op o] ++ printE b ++ [.rp]

def printArgs : List Expr → List Tok
  | [] => []
  | [e] => printE e
  | e :: es => printE e ++ [.comma] ++ printArgs es

def printS : Stmt Pn → List Tok
  | .skip => [.semi]
  | .assign x e => [.id x, .eq] ++ printE e ++ [.semi]
  | .seq a b => [.lb] ++ printS a ++ printS b ++ [.rb]
  | .ite e a b => [.kwIf, .lp] ++ printE e ++ [.rp] ++ printS a ++ [.kwElse] ++ printS b
  | .while e b => [.kwWhile, .lp] ++ printE e ++ [.rp] ++ printS b
  | .call x p args => [.id x, .eq, .id (name p), .lp] ++ printArgs args ++ [.rp, .semi]

def parseE : Nat → List Tok → Option (Expr × List Tok)
  | 0, _ => none
  | _ + 1, .num k :: r => some (.const (BitVec.ofNat 32 k), r)
  | _ + 1, .id x :: r => some (.var x, r)
  | n + 1, .lp :: r =>
    match parseE n r with
    | some (a, .op o :: r1) =>
      match parseE n r1 with
      | some (b, .rp :: r2) => some (.bin o a b, r2)
      | _ => none
    | _ => none
  | _ + 1, _ => none

def parseArgs : Nat → List Tok → Option (List Expr × List Tok)
  | 0, _ => none
  | n + 1, r =>
    match r with
    | .rp :: _ => some ([], r)
    | _ =>
      match parseE n r with
      | some (e, .comma :: r1) =>
        match parseArgs n r1 with
        | some (es, r2) => some (e :: es, r2)
        | none => none
      | some (e, r1) => some ([e], r1)
      | none => none

def parseS : Nat → List Tok → Option (Stmt Pn × List Tok)
  | 0, _ => none
  | _ + 1, .semi :: r => some (.skip, r)
  | n + 1, .lb :: r =>
    match parseS n r with
    | some (a, r1) =>
      match parseS n r1 with
      | some (b, .rb :: r2) => some (.seq a b, r2)
      | _ => none
    | none => none
  | n + 1, .kwIf :: .lp :: r =>
    match parseE n r with
    | some (e, .rp :: r1) =>
      match parseS n r1 with
      | some (a, .kwElse :: r2) =>
        match parseS n r2 with
        | some (b, r3) => some (.ite e a b, r3)
        | none => none
      | _ => none
    | _ => none
  | n + 1, .kwWhile :: .lp :: r =>
    match parseE n r with
    | some (e, .rp :: r1) =>
      match parseS n r1 with
      | some (b, r2) => some (.while e b, r2)
      | none => none
    | _ => none
  | n + 1, .id x :: .eq :: .id s :: .lp :: r =>
    match ofName s with
    | some p =>
      match parseArgs n r with
      | some (args, .rp :: .semi :: r1) => some (.call x p args, r1)
      | _ => none
    | none => none
  | n + 1, .id x :: .eq :: r =>
    match parseE n r with
    | some (e, .semi :: r1) => some (.assign x e, r1)
    | _ => none
  | _ + 1, _ => none

/-! ## Round trip -/

def sizeE : Expr → Nat
  | .bin _ a b => sizeE a + sizeE b + 1
  | _ => 1

def sizeArgs : List Expr → Nat
  | [] => 1
  | e :: es => sizeE e + sizeArgs es + 1

def sizeS : Stmt Pn → Nat
  | .seq a b => sizeS a + sizeS b + 1
  | .ite e a b => sizeE e + sizeS a + sizeS b + 1
  | .while e b => sizeE e + sizeS b + 1
  | .assign _ e => sizeE e + 1
  | .call _ _ args => sizeArgs args + 1
  | .skip => 1

/-- What may follow a printed expression: never something that extends it. -/
theorem parseE_print : ∀ (e : Expr) (rest : List Tok) (n : Nat), sizeE e ≤ n →
    parseE n (printE e ++ rest) = some (e, rest)
  | .const v, rest, n + 1, _ => by simp [printE, parseE]
  | .var x, rest, n + 1, _ => by simp [printE, parseE]
  | .bin o a b, rest, n + 1, h => by
    have ha := parseE_print a (.op o :: (printE b ++ .rp :: rest)) n (by simp [sizeE] at h; omega)
    have hb := parseE_print b (.rp :: rest) n (by simp [sizeE] at h; omega)
    simp only [printE, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, parseE]
    try simp only [List.cons_append] at ha
    rw [ha]; (try simp only); rw [hb]
  | .const _, _, 0, h => by simp [sizeE] at h
  | .var _, _, 0, h => by simp [sizeE] at h
  | .bin _ _ _, _, 0, h => by simp [sizeE] at h

theorem printE_ne_rp : ∀ (e : Expr) (r : List Tok), printE e ++ r ≠ .rp :: r'
  | .const _, _ => by simp [printE]
  | .var _, _ => by simp [printE]
  | .bin _ _ _, _ => by simp [printE]

theorem parseArgs_print : ∀ (args : List Expr) (rest : List Tok) (n : Nat), sizeArgs args ≤ n →
    parseArgs n (printArgs args ++ .rp :: rest) = some (args, .rp :: rest)
  | [], rest, n + 1, _ => by simp [printArgs, parseArgs]
  | [e], rest, n + 1, h => by
    have he := parseE_print e (.rp :: rest) n (by simp [sizeArgs] at h; omega)
    simp only [printArgs, parseArgs]
    split
    · rename_i r' heq; exact absurd heq (printE_ne_rp e _)
    · rw [he]
  | e :: e2 :: es, rest, n + 1, h => by
    have he := parseE_print e (.comma :: (printArgs (e2 :: es) ++ .rp :: rest)) n
      (by simp [sizeArgs] at h; omega)
    have hs := parseArgs_print (e2 :: es) rest n (by simp [sizeArgs] at h ⊢; omega)
    simp only [printArgs, List.append_assoc, List.cons_append, parseArgs]
    split
    · rename_i r' heq; exact absurd heq (printE_ne_rp e _)
    · simp only [List.nil_append]; rw [he]; (try simp only); rw [hs]
  | [], _, 0, h => by simp [sizeArgs] at h
  | [_], _, 0, h => by simp [sizeArgs] at h
  | _ :: _ :: _, _, 0, h => by simp [sizeArgs] at h

variable {name ofName}

/-- **The printer is faithful**: parsing a printed statement gives it back. -/
theorem parseS_print (hname : ∀ p, ofName (name p) = some p) :
    ∀ (s : Stmt Pn) (rest : List Tok) (n : Nat), sizeS s ≤ n →
      parseS ofName n (printS name s ++ rest) = some (s, rest)
  | .skip, rest, n + 1, _ => by simp [printS, parseS]
  | .assign x e, rest, n + 1, h => by
    have he := parseE_print e (.semi :: rest) n (by simp [sizeS] at h; omega)
    cases e with
    | const v => simp_all [printS, parseS, printE]
    | var y => simp_all [printS, parseS, printE]
    | bin o a b => simp_all [printS, parseS, printE]
  | .seq a b, rest, n + 1, h => by
    have ha := parseS_print hname a (printS name b ++ .rb :: rest) n (by simp [sizeS] at h; omega)
    have hb := parseS_print hname b (.rb :: rest) n (by simp [sizeS] at h; omega)
    simp only [printS, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, parseS]
    rw [ha]; (try simp only); rw [hb]
  | .ite e a b, rest, n + 1, h => by
    have he := parseE_print e (.rp :: (printS name a ++ .kwElse :: (printS name b ++ rest))) n
      (by simp [sizeS] at h; omega)
    have ha := parseS_print hname a (.kwElse :: (printS name b ++ rest)) n (by simp [sizeS] at h; omega)
    have hb := parseS_print hname b rest n (by simp [sizeS] at h; omega)
    simp only [printS, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, parseS]
    try simp only [List.cons_append] at he
    rw [he]; simp only; rw [ha]; (try simp only); rw [hb]
  | .while e b, rest, n + 1, h => by
    have he := parseE_print e (.rp :: (printS name b ++ rest)) n (by simp [sizeS] at h; omega)
    have hb := parseS_print hname b rest n (by simp [sizeS] at h; omega)
    simp only [printS, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, parseS]
    try simp only [List.cons_append] at he
    rw [he]; (try simp only); rw [hb]
  | .call x p args, rest, n + 1, h => by
    have hargs := parseArgs_print args (.semi :: rest) n (by simp [sizeS] at h; omega)
    simp only [printS, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, parseS,
      hname]
    rw [hargs]
  | .skip, _, 0, h => by simp [sizeS] at h
  | .assign _ _, _, 0, h => by simp [sizeS] at h
  | .seq _ _, _, 0, h => by simp [sizeS] at h
  | .ite _ _ _, _, 0, h => by simp [sizeS] at h
  | .while _ _, _, 0, h => by simp [sizeS] at h
  | .call _ _ _, _, 0, h => by simp [sizeS] at h

/-- **Round trip** for a whole program. -/
theorem parse_print (hname : ∀ p, ofName (name p) = some p) (s : Stmt Pn) :
    parseS ofName (sizeS s) (printS name s) = some (s, []) := by
  simpa using parseS_print hname s [] (sizeS s) (Nat.le_refl _)

/-- So the printer is injective: different programs print differently. -/
theorem print_injective (hname : ∀ p, ofName (name p) = some p) {s t : Stmt Pn}
    (h : printS name s = printS name t) : s = t := by
  have h1 := parseS_print hname s [] (sizeS s + sizeS t) (by omega)
  have h2 := parseS_print hname t [] (sizeS s + sizeS t) (by omega)
  simp only [List.append_nil] at h1 h2
  rw [h, h2] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact h1.1.symm

/-! ## Rendering (lexical, unverified) -/

def binC : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .eq => "==" | .ne => "!=" | .ltu => "<"

def Tok.render : Tok → String
  | .id s => s
  | .num n => toString n ++ "u"
  | .lp => "(" | .rp => ")" | .lb => "{" | .rb => "}" | .semi => ";" | .comma => ","
  | .eq => "=" | .op o => binC o
  | .kwIf => "if" | .kwElse => "else" | .kwWhile => "while"

def render (ts : List Tok) : String := " ".intercalate (ts.map Tok.render)

end PrintC
