(** * A small C-like language

    The Coq side of the virtualization port. Code is written in this language
    and proved to refine the specifications; the Lean port then transcribes
    the same code into ClightL.

    Values are unsigned 32-bit words, represented as [Z] in [0, 2^32).
    Arithmetic and bitwise operations wrap modulo [2^32], as in C.
    Memory is one region of word-indexed cells (the kernel region of the Lean
    development); locks are not modelled here, the Lean port adds them. *)

From Stdlib Require Import ZArith String Lia.
Local Open Scope string_scope.
Open Scope Z_scope.

Definition W : Z := 4294967296.

(** Wrap to 32 bits. *)
Definition norm (z : Z) : Z := z mod W.

Lemma norm_small : forall z, 0 <= z < W -> norm z = z.
Proof. intros; unfold norm; apply Z.mod_small; lia. Qed.

Lemma norm_range : forall z, 0 <= norm z < W.
Proof. intros; unfold norm, W; apply Z.mod_pos_bound; lia. Qed.

(** The C operations on 32-bit unsigned words. *)
Definition wand (a b : Z) : Z := norm (Z.land a b).
Definition wor (a b : Z) : Z := norm (Z.lor a b).
Definition wshl (a b : Z) : Z := norm (Z.shiftl a b).

Definition locals := string -> Z.
Definition mem := Z -> Z.

Definition lset (s : locals) (x : string) (v : Z) : locals :=
  fun y => if string_dec y x then v else s y.

Definition upd (m : mem) (k v : Z) : mem := fun a => if Z.eq_dec a k then v else m a.

Lemma lset_same : forall s x v, lset s x v x = v.
Proof. intros; unfold lset; destruct (string_dec x x); congruence. Qed.

Lemma lset_other : forall s x y v, y <> x -> lset s x v y = s y.
Proof. intros; unfold lset; destruct (string_dec y x); congruence. Qed.

Lemma upd_same : forall m k v, upd m k v k = v.
Proof. intros; unfold upd; destruct (Z.eq_dec k k); congruence. Qed.

Lemma upd_other : forall m k a v, a <> k -> upd m k v a = m a.
Proof. intros; unfold upd; destruct (Z.eq_dec a k); congruence. Qed.

Inductive binop := Add | Sub | Mul | Div | Mod | And | Or | Shl | Eq | Ltu.

Inductive expr :=
| Const (v : Z)
| Var (x : string)
| Bin (o : binop) (a b : expr).

Definition binop_eval (o : binop) (a b : Z) : Z :=
  match o with
  | Add => norm (a + b)
  | Sub => norm (a - b)
  | Mul => norm (a * b)
  | Div => a / b
  | Mod => a mod b
  | And => wand a b
  | Or => wor a b
  | Shl => wshl a b
  | Eq => if Z.eqb a b then 1 else 0
  | Ltu => if Z.ltb a b then 1 else 0
  end.

Fixpoint eval (s : locals) (e : expr) : Z :=
  match e with
  | Const v => v
  | Var x => s x
  | Bin o a b => binop_eval o (eval s a) (eval s b)
  end.

Inductive stmt :=
| Skip
| Assign (x : string) (e : expr)
| Load (x : string) (a : expr)        (* x = MEM[a] *)
| Store (a v : expr)                  (* MEM[a] = v *)
| Seq (s1 s2 : stmt)
| Ite (c : expr) (s1 s2 : stmt)
| While (c : expr) (s : stmt).

(** Big-step semantics: [exec s σ m σ' m'] when [s] runs to completion. *)
Inductive exec : stmt -> locals -> mem -> locals -> mem -> Prop :=
| ESkip : forall s m, exec Skip s m s m
| EAssign : forall x e s m, exec (Assign x e) s m (lset s x (eval s e)) m
| ELoad : forall x a s m, exec (Load x a) s m (lset s x (m (eval s a))) m
| EStore : forall a v s m, exec (Store a v) s m s (upd m (eval s a) (eval s v))
| ESeq : forall c1 c2 s m s1 m1 s2 m2,
    exec c1 s m s1 m1 -> exec c2 s1 m1 s2 m2 -> exec (Seq c1 c2) s m s2 m2
| EIteT : forall c c1 c2 s m s' m',
    eval s c <> 0 -> exec c1 s m s' m' -> exec (Ite c c1 c2) s m s' m'
| EIteF : forall c c1 c2 s m s' m',
    eval s c = 0 -> exec c2 s m s' m' -> exec (Ite c c1 c2) s m s' m'
| EWhileF : forall c b s m, eval s c = 0 -> exec (While c b) s m s m
| EWhileT : forall c b s m s1 m1 s2 m2,
    eval s c <> 0 -> exec b s m s1 m1 -> exec (While c b) s1 m1 s2 m2 ->
    exec (While c b) s m s2 m2.

(** Convenience: an assignment whose value is known. *)
Lemma exec_assign : forall x e s m v, eval s e = v -> exec (Assign x e) s m (lset s x v) m.
Proof. intros; subst; constructor. Qed.

Lemma exec_load : forall x a s m k, eval s a = k -> exec (Load x a) s m (lset s x (m k)) m.
Proof. intros; subst; constructor. Qed.

Lemma exec_store : forall a v s m k w, eval s a = k -> eval s v = w -> exec (Store a v) s m s (upd m k w).
Proof. intros; subst; constructor. Qed.
