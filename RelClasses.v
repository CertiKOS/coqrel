Require Export Coq.Classes.RelationClasses.
Require Export RelDefinitions.


(** * More classes for relation properties *)

(** In the following we introduce more typeclasses for characterizing
  properties of relations, in the spirit of the [RelationClasses]
  standard library. *)

(** ** Coreflexive relations *)

Class Coreflexive {A} (R: relation A) :=
  coreflexivity: forall x y, R x y -> x = y.

Global Instance eq_corefl {A}:
  Coreflexive (@eq A).
Proof.
  firstorder.
Qed.

Global Instance subrel_eq {A} (R: relation A):
  Coreflexive R ->
  Related R eq subrel.
Proof.
  firstorder.
Qed.

(** ** Composition *)

Class RCompose {A B C} (RAB : rel A B) (RBC : rel B C) (RAC : rel A C) :=
  rcompose : forall x y z, RAB x y -> RBC y z -> RAC x z.

Ltac rcompose b :=
  lazymatch goal with
    | |- ?R ?a ?c =>
      apply (rcompose a b c)
  end.

Ltac ercompose :=
  eapply rcompose.

(** [Transitive] is a special case of [RCompose]. The following makes
  it possible for the [transitivity] tactic to use [RCompose]
  instances. *)

Global Instance rcompose_transitive {A} (R : relation A) :
  RCompose R R R -> Transitive R.
Proof.
  firstorder.
Qed.

(** Conversely, we will want to use declared [Transitive] instances to
  satisfy [RCompose] queries. To avoid loops in the resolution process
  this is only declared as an immediate hint --- we expect all derived
  instances to be formulated in terms of [RCompose] rather than
  [Transitive]. *)

Lemma transitive_rcompose `(Transitive) :
  RCompose R R R.
Proof.
  assumption.
Qed.

Hint Immediate transitive_rcompose : typeclass_instances.

(** ** Decomposition *)

(** The converse of [RCompose] is the following "decomposition" property. *)

Class RDecompose {A B C} (RAB : rel A B) (RBC : rel B C) (RAC : rel A C) :=
  rdecompose : forall x z, RAC x z -> exists y, RAB x y /\ RBC y z.

Tactic Notation "rdecompose" constr(H) "as" simple_intropattern(p) :=
  lazymatch type of H with
    | ?R ?a ?b =>
      destruct (rdecompose a b H) as p
    | _ =>
      fail "Not an applied relation"
  end.

Tactic Notation "rdecompose" hyp(H) "as" simple_intropattern(p) :=
  lazymatch type of H with
    | ?R ?a ?b =>
      apply rdecompose in H; destruct H as p
    | _ =>
      fail "Not an applied relation"
  end.

Tactic Notation "rdecompose" constr(H) :=
  rdecompose H as (? & ? & ?).

Tactic Notation "rdecompose" hyp(H) :=
  rdecompose H as (? & ? & ?).
