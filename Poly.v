(* isabelle tutorial prog-prove Excercise 2.11 *)
Require Import ZArith.
Require Import Lists.List.
Import ListNotations.
Require Import CpdtTactics.
Open Scope Z.
Arguments Z.mul x y : simpl nomatch.
Arguments Z.add x y : simpl nomatch.

Inductive exp :=
| Var : exp
| Const : Z -> exp
| Add : exp -> exp -> exp
| Mult : exp -> exp -> exp.

Fixpoint eval (e : exp) (x : Z) : Z :=
  match e with
  | Var => x
  | Const c => c
  | Add e1 e2 => eval e1 x + eval e2 x
  | Mult e1 e2 => eval e1 x * eval e2 x
  end.

Fixpoint evalp (ps : list Z) (x : Z) : Z :=
  match ps with
  | nil => 0
  | p :: ps' => p + x * evalp ps' x
  end.

Fixpoint poly_add (ps : list Z) (qs : list Z) :=
  match ps, qs with
  | nil, _ => qs
  | _, nil => ps
  | p :: ps', q :: qs' => (p + q) :: poly_add ps' qs'
  end.
Functional Scheme poly_add_ind := Induction for poly_add Sort Prop.

Fixpoint poly_mult (ps : list Z) (qs : list Z) :=
  match ps, qs with
  | nil, _ => nil
  | _, nil => nil
  | p :: ps', _ => poly_add (map (Z.mul p) qs) (0 :: poly_mult ps' qs)
  end.
Functional Scheme poly_mult_ind := Induction for poly_mult Sort Prop.

Fixpoint coeffs (e : exp) : list Z :=
  match e with
  | Var => [0; 1]
  | Const c => [c]
  | Add e1 e2 => poly_add (coeffs e1) (coeffs e2)
  | Mult e1 e2 => poly_mult (coeffs e1) (coeffs e2)
  end.

Lemma poly_add_spec : forall ps qs x, evalp (poly_add ps qs) x = evalp ps x + evalp qs x.
Proof.
  intros.
  functional induction (poly_add ps qs); crush; ring.
Qed.
Hint Rewrite poly_add_spec : core.

Lemma mapmult_evalp : forall a ps x, evalp (map (Z.mul a) ps) x = a * evalp ps x.
Proof.
  induction ps; intros; crush; ring.
Qed.
Hint Rewrite mapmult_evalp : core.

Lemma poly_mult_spec : forall ps qs x, evalp (poly_mult ps qs) x = evalp ps x * evalp qs x.
Proof.
  intros.
  functional induction (poly_mult ps qs); crush; ring.
Qed.
Hint Rewrite poly_mult_spec : core.

Theorem coeffs_spec : forall e x, evalp (coeffs e) x = eval e x.
Proof.
  intros.
  induction e; crush; ring.
Qed.
