Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import RelDefinitions.
Require Import RelOperators.
Require Import Relators.
Require Import Monotonicity.

(** * Interoperation with [Coq.Classes.Morphisms] *)

(** Although ultimately we will reimplement a [rewrite] tactic, and
  our system is largely designed to replace the setoid rewriting
  support in [Coq.Classes.Morphisms], we still want to be compatible
  with it so that:

    - we can take advantage of the relational properties declared in
      the old system;
    - the generalized [setoid_rewrite] can take advantage of our
      library for answering its [Morphisms.Proper] queries.

  This compatibility layer is pretty straightforward: we simply
  declare the instances we need in order to use the properties
  declared in the old system, and use [rauto] to handle
  [Morphisms.Proper] queries. *)

(** ** Using [Morphisms]-style relational properties *)

(** *** Relators *)

(** While [Coq.Classes.Morphisms] uses a distinct set of relators from
  ours, we don't try to map them into our language. Instead, we hook
  them into our system the same way we do our generalized versions,
  so that [respectful] and the like can be used as just another set of
  "native" Coqrel relators. *)

Global Instance respectful_subrel A B:
  Monotonic (@respectful A B) (subrel --> subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance respectful_params:
  Params (@respectful) 4.

Global Instance respectful_rintro {A B} (RA: relation A) (RB: relation B) f g:
  RIntro (forall x y, RA x y -> RB (f x) (g y)) (respectful RA RB) f g.
Proof.
  firstorder.
Qed.

Lemma respectful_relim {A B} (RA: relation A) (RB: relation B) f g m n P Q:
  RElim RB (f m) (g n) P Q ->
  RElim (respectful RA RB) f g (RA m n /\ P) Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (respectful _ _) _ _ _ _) =>
  eapply respectful_relim : typeclass_instances.

Global Instance forall_relation_subrel A P:
  Monotonic (@forall_relation A P) ((forallr -, subrel) ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance forall_relation_params:
  Params (@forall_relation) 3.

Global Instance forall_relation_rintro {A B} (R: forall a:A, relation (B a)) f g:
  RIntro (forall a, R a (f a) (g a)) (forall_relation R) f g.
Proof.
  firstorder.
Qed.

Lemma forall_relation_relim {A B} (R: forall a:A, relation (B a)) f g a P Q:
  RElim (R a) (f a) (g a) P Q ->
  RElim (forall_relation R) f g P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (forall_relation _) _ _ _ _) =>
  eapply forall_relation_relim : typeclass_instances.

Global Instance pointwise_relation_subrel A B:
  Monotonic (@pointwise_relation A B) (subrel ++> subrel).
Proof.
  firstorder.
Qed.

Global Instance pointwise_relation_params:
  Params (@pointwise_relation) 3.

Global Instance pointwise_relation_rintro {A B} (R: relation B) f g:
  RIntro (forall a, R (f a) (g a)) (pointwise_relation A R) f g.
Proof.
  firstorder.
Qed.

Lemma pointwise_relation_relim {A B} (R: relation B) f g a P Q:
  RElim R (f a) (g a) P Q ->
  RElim (pointwise_relation A R) f g P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (pointwise_relation _ _) _ _ _ _) =>
  eapply pointwise_relation_relim : typeclass_instances.

(** The rewriting system sometimes generates arguments constraints of
  the following form (when rewriting an argument of [arrow_rel] for
  instance), which need to be matched against our relational
  properties stated in terms of [subrel]. *)

Global Instance pointwise_relation_subrel_subrel A B:
  Related (pointwise_relation A (pointwise_relation B impl)) subrel subrel.
Proof.
  firstorder.
Qed.

(** *** [Morphisms.Proper] instances *)

(** Now that we can interpret the relators used in [Morphisms]-style
  relational properties, we can simply hook instances of
  [Morphisms.Proper] into our own database. We don't want to use the
  corresponding deductive infrastructure in [Coq.Classes.Morphisms],
  so we declare the following as an immediate hint so that we only use
  "leaf" instances of [Proper]. *)

Lemma morphisms_proper_related {A} (R: relation A) (a: A):
  Morphisms.Proper R a ->
  Monotonic a R.
Proof.
  firstorder.
Qed.

Hint Immediate morphisms_proper_related : typeclass_instances.

(** *** [subrelation] instances *)

(** Likewise, we want to be able to use [subrelation] declaration as
  [subrel] instances. Again, we use an immediate hint. *)

Lemma subrelation_subrel {A} (R1 R2: relation A):
  subrelation R1 R2 ->
  Related R1 R2 subrel.
Proof.
  firstorder.
Qed.

Hint Immediate subrelation_subrel : typeclass_instances.


(** ** Satisfying [Morphisms.Proper] queries *)

(** This is quite straightforward. The only slightly subtle part is,
  we need to avoid a loop with [morphisms_proper_related] above. We
  use a hypothesis of the following type as a flag to avoid reentry. *)

CoInductive in_solve_morphisms_proper := in_solve_morphisms_proper_intro.

Ltac solve_morphisms_proper :=
  match goal with
    | _ : normalization_done |- _ =>
      fail 1
    | H : apply_subrelation |- _ =>
      clear H;
      red;
      rauto
  end.

Hint Extern 10 (Morphisms.Proper _ _) =>
  solve_morphisms_proper : typeclass_instances.
