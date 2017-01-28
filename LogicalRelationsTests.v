Require Import LogicalRelations.
Require Import Coq.Lists.List.

(** * Tests *)

(** ** Setoid rewriting *)

Goal
  forall A (a b: A) `(HR: Equivalence A) (H: R a b),
    sum_rel R R (inl a) (inl b).
Proof.
  intros.
  rewrite H.
  rewrite <- H.
  reflexivity.
Qed.

(** ** Monotonicity tactics *)

Goal
  forall A (a b: A) (R: rel A A) (H: R a b),
    let f (x y: A * A) := (@pair (A+A) (A+A) (inr (fst x)) (inl (snd y))) in
    Proper (R * ⊤ ++> ⊤ * R ++> (⊥ + R) * (R + ⊥))%rel f.
Proof.
  intros; unfold f.
  solve_monotonic.
Qed.

Goal
  forall {A1 A2 B1 B2} (R1 R1': rel A1 A2) (R2 R2': rel B1 B2),
    subrel R1' R1 ->
    subrel R2 R2' ->
    subrel (R1 ++> R2) (R1' ++> R2').
Proof.
  do 10 intro.
  solve_monotonic.
Qed.

(** Check that we can use relational hypotheses from the context as
  well as [Proper] and [Related] instances. *)

Goal
  forall
    {A B} (R: rel A A)
    (op: A -> B) (Hop: (R ++> eq) op op)
    (x y: A) (Hxy: R x y),
    op x = op y.
Proof.
  intros.
  solve_monotonic.
Qed.

(** Bug with relational parametricity: you can't [RElim] a relation
  you don't know yet. *)

Goal
  forall {A B} (RA: rel A A) (RB: rel B B) (m n: (A -> B) * B) (x y: A),
    ((- ==> RB) * RB)%rel m n ->
    RB (fst m x) (fst n x).
Proof.
  intros A B RA RB m n x y Hmn.
  try monotonicity.
  try solve_monotonic.
Abort.

(** Pattern matching *)

Goal
  forall {A B} (RA: rel A A) (RB: rel B B) (x y: A) (f: A -> A + B),
    RA x y ->
    (RA ++> RA + RB) f f ->
    RA (match f x with inl a => a | inr b => x end)
       (match f y with inl a => a | inr b => y end).
Proof.
  intros.
  solve_monotonic.
Qed.

Goal
  forall {A B} (RA: rel A A) (RB: rel B B) (x y: A * B) (z: A),
    RA z z ->
    prod_rel RA RB x y ->
    RA (let (a, b) := x in z)
       (let (a, b) := y in z).
Proof.
  intros.
  solve_monotonic.
Qed.

(** [rel_curry] *)

Goal
  forall {A B C} R R' S (f: A -> B -> B -> C) (x1 y1: A) (x2 y2: B),
    Proper (rel_curry (R ++> R' ++> S)) f ->
    S (f x1 x2 x2) (f y1 y2 y2).
Proof.
  intros A B C R R' S f x1 y1 x2 y2 Hf.
  monotonicity.
Abort.

(** Hypotheses from the context. This used to fail because [Hyy] would
  shadow [Hxy] (the hypothesis we want). *)

Goal
  forall {A} (R: rel A A) (x y: A),
    R x y -> eq y y -> R x y.
Proof.
  intros A R x y Hxy Hyy.
  monotonicity.
Qed.

(** ** Using [foo_subrel] instances *)

(** Still broken because of the interaction between [subrel] and
  [- ==> - ==> impl] (or lack thereof) *)

(*
Goal
  forall A1 A2 B1 B2 C1 C2 (R1 R2: rel A1 A2) (R1': rel B1 B2) (R: rel C1 C2),
    subrel R1 R2 ->
    forall x y,
      (R2 ++> R) x y ->
      (R1 ++> R) x y.
Proof.
  intros A1 A2 B1 B2 C1 C2 R1 R2 R1' R HR12 x y H.
  rewrite HR12.
  assumption.
Qed.
*)

Goal
  forall A B (xa1 xa2 ya1 ya2 : A) (xb1 xb2 yb1 yb2 : B)
         (opA: A -> A -> A) (opB: B -> B -> B)
         (RA: rel A A) (RB: rel B B)
         (HopA: Proper (RA ++> RA ++> RA) opA)
         (HopB: Proper (RB ++> RB ++> RB) opB)
         (Hxa: RA xa1 xa2)
         (Hxb: RB xb1 xb2)
         (Hya: RA ya1 ya2)
         (Hyb: RB yb1 yb2),
    (RA * RB)%rel
      (opA xa1 ya1, opB xb1 yb1)
      (opA xa2 ya2, opB xb2 yb2).
Proof.
  intros.
  solve_monotonic.
Qed.

(** FIXME: this should work as well. *)

(* This now triggers a "not an arity" anomaly with Coq 8.4 *)
(*
Goal
  forall A1 A2 B1 B2 C1 C2 (R1 R2: rel A1 A2) (R1': rel B1 B2) (R: rel C1 C2),
    subrel R1 R2 ->
    forall x y,
      (R2 * R1' ++> R) x y ->
      (R1 * R1' ++> R) x y.
Proof.
  intros A1 A2 B1 B2 C1 C2 R1 R2 R1' R HR12 x y H.
  try rewrite HR12.
Abort.
*)

(** ** The [preorder] tactic *)

Goal
  forall {A} (R S T: rel A A),
    subrel R S ->
    subrel S R ->
    subrel S T ->
    subrel R T.
Proof.
  intros.
  rstep.
Qed.

(** ** The [transport] tactic *)

Goal
  forall W acc A B C (R1: W -> rel A A) (R2: W -> rel B B) (R3: W -> rel C C) f g a b x w,
    Proper (rforall w, R1 w ++> R2 w) f ->
    Proper (rforall w, R2 w ++> option_rel (rel_incr acc R3 w)) g ->
    R1 w a b ->
    g (f a) = Some x ->
    exists y, rel_incr acc R3 w x y.
Proof.
  intros.
  transport H2.
  eexists.
  solve_monotonic.
Qed.

(** ** Tests for specific relators *)

(** [list_subrel] use to not work because of a missing [Params] declaration. *)

Goal
  forall A B (R R': rel A B) l1 l2 x y,
    subrel R R' ->
    list_rel R l1 l2 ->
    R' x y ->
    list_rel R' (x :: l1) (y :: l2).
Proof.
  intros.
  rauto.
Qed.
