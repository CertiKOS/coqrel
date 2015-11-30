Require Export RelDefinitions.

(** ** Union of relations *)

Definition rel_union {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y \/ R2 x y.

Arguments rel_union {_ _} R1%signature R2%signature _ _.

Infix "∪" := rel_union (at level 50) : signature_scope.

Lemma rel_union_introl {A B} (R1 R2: rel A B):
  subrel R1 (R1 ∪ R2).
Proof.
  firstorder.
Qed.

Hint Extern 0 (subrel _ (_ ∪ _)) =>
  eapply rel_union_introl : typeclass_instances.

Lemma rel_union_intror {A B} (R1 R2: rel A B):
  subrel R2 (R1 ∪ R2).
Proof.
  firstorder.
Qed.

Hint Extern 0 (subrel _ (_ ∪ _)) =>
  eapply rel_union_introl : typeclass_instances.

Lemma rel_union_lub {A B} (R1 R2 R: rel A B):
  subrel R1 R ->
  subrel R2 R ->
  subrel (R1 ∪ R2)%signature R.
Proof.
  firstorder.
Qed.

Hint Extern 2 (subrel (_ ∪ _) _) =>
  eapply rel_union_lub : typeclass_instances.

(** ** Intersection of relations *)

Definition rel_inter {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y /\ R2 x y.

Arguments rel_inter {_ _} R1%signature R2%signature _ _.

Infix "∩" := rel_inter (at level 40) : signature_scope.

Lemma rel_inter_eliml {A B} (R1 R2: rel A B):
  subrel (R1 ∩ R2) R1.
Proof.
  firstorder.
Qed.

Hint Extern 0 (subrel (_ ∩ _) _) =>
  eapply rel_inter_eliml : typeclass_instances.

Lemma rel_inter_elimr {A B} (R1 R2: rel A B):
  subrel (R1 ∩ R2) R2.
Proof.
  firstorder.
Qed.

Hint Extern 0 (subrel (_ ∩ _) _) =>
  eapply rel_inter_elimr : typeclass_instances.

Lemma rel_inter_glb {A B} (R R1 R2: rel A B):
  subrel R R1 ->
  subrel R R2 ->
  subrel R (R1 ∩ R2).
Proof.
  firstorder.
Qed.

Hint Extern 2 (subrel _ (_ ∩ _)) =>
  eapply rel_inter_glb : typeclass_instances.

Lemma rel_inter_refl {A} (R1 R2: rel A A):
  Reflexive R1 ->
  Reflexive R2 ->
  Reflexive (R1 ∩ R2).
Proof.
  intros H1 H2.
  split; reflexivity.
Qed.

Hint Extern 2 (Reflexive (_ ∩ _)) =>
  eapply rel_inter_refl : typeclass_instances.

Lemma rel_inter_trans {A} (R1 R2: rel A A):
  Transitive R1 ->
  Transitive R2 ->
  Transitive (R1 ∩ R2).
Proof.
  intros H1 H2 x y z [Hxy1 Hxy2] [Hyz1 Hyz2].
  split; etransitivity; eassumption.
Qed.

Hint Extern 2 (Transitive (_ ∩ _)) =>
  eapply rel_inter_trans : typeclass_instances.

Lemma rel_inter_sym {A} (R1 R2: rel A A):
  Symmetric R1 ->
  Symmetric R2 ->
  Symmetric (R1 ∩ R2).
Proof.
  intros H1 H2 x y [Hxy1 Hxy2].
  split; symmetry; assumption.
Qed.

Hint Extern 2 (Symmetric (_ ∩ _)) =>
  eapply rel_inter_sym : typeclass_instances.

Global Instance rel_inter_flip_sym {A} (R: rel A A):
  Symmetric (R ∩ flip R).
Proof.
  intros x y [Hxy Hyx].
  split; assumption.
Qed.

(** ** The bottom and top relations *)

Definition rel_bot {A B}: rel A B :=
  fun x y => False.

Notation "⊥" := rel_bot : signature_scope.

Definition rel_top {A B}: rel A B :=
  fun x y => True.

Notation "⊤" := rel_top : signature_scope.

Hint Resolve (fun A B (x:A) (y:B) => I : rel_top x y).

(** ** Relation equivalence *)

Definition eqrel {A B}: rel (rel A B) (rel A B) :=
  (subrel ∩ flip subrel).

Arguments eqrel {_ _} RA%signature RB%signature.

Global Instance eqrel_equivalence A B:
  Equivalence (@eqrel A B).
Proof.
  unfold eqrel.
  split; typeclasses eauto.
Qed.

(** ** Relation composition *)

Definition rel_compose {A B C} (RAB: rel A B) (RBC: rel B C): rel A C :=
  fun x z => exists y, RAB x y /\ RBC y z.

Global Instance rel_compose_subrel A B C:
  Proper (subrel ++> subrel ++> subrel) (@rel_compose A B C).
Proof.
  firstorder.
Qed.

Global Instance rel_compose_eqrel A B C:
  Proper (eqrel ==> eqrel ==> eqrel) (@rel_compose A B C).
Proof.
  firstorder.
Qed.

Lemma rel_compose_id_left {A B} (R: rel A B):
  eqrel (rel_compose R eq) R.
Proof.
  unfold rel_compose.
  split; intros x y; firstorder; congruence.
Qed.

Lemma rel_compose_id_right {A B} (R: rel A B):
  eqrel (rel_compose eq R) R.
Proof.
  unfold rel_compose.
  split; intros x y; firstorder; congruence.
Qed.

Lemma rel_compose_assoc {A B C D} (RAB: rel A B) (RBC: rel B C) (RCD: rel C D):
  eqrel
    (rel_compose (rel_compose RAB RBC) RCD)
    (rel_compose RAB (rel_compose RBC RCD)).
Proof.
  unfold rel_compose.
  split; intros x y; firstorder; congruence.
Qed.

(** ** Relation currying *)

(* [rel_uncurry] is particularly useful when two (curried) arguments
  to a given function have to be related in a dependent way. For
  example in Compcert, memory injections relate memory blocks and
  offsets jointly, but many operations have those as two separate
  arguments. To state the relational property of such operations, we
  can uncurry a joint relation on (block, offset) pairs. *)

Definition rel_uncurry {A1 A2 B1 B2 C1 C2}:
    rel (A1  * B1 -> C1) (A2  * B2 -> C2) ->
    rel (A1 -> B1 -> C1) (A2 -> B2 -> C2) :=
  fun R f g =>
    R (fun x => f (fst x) (snd x))
      (fun y => g (fst y) (snd y)).

Global Instance rel_uncurry_subrel A1 A2 B1 B2 C1 C2:
  Proper (subrel ++> subrel) (@rel_uncurry A1 A2 B1 B2 C1 C2).
Proof.
  firstorder.
Qed.

(** ** Checking predicates on the left and right elements *)

Definition lsat {A B} (P: A -> Prop): rel A B :=
  fun x y => P x.

Definition rsat {A B} (P: B -> Prop): rel A B :=
  fun x y => P y.

(** ** Relation versions of [ex] and [all] *)

(** Ideally we would overload the [forall] and [exists] notation to
  use the relation version under the [signature] scope. But as long as
  we keep [signature_scope] open globally, we can't really do that
  without breaking everything. So we use our own keyword [rexists] and
  [rforall] instead. *)

Definition rel_all {A B C} (R: C -> rel A B): rel A B :=
  fun x y => forall c, R c x y.

Notation "'rforall' x .. y , p" :=
  (rel_all (fun x => .. (rel_all (fun y => p)) .. ))
  (at level 200, x binder, right associativity)
  : signature_scope.

Definition rel_ex {A B C} (R: C -> rel A B): rel A B :=
  fun x y => exists c, R c x y.

Notation "'rexists' x .. y , p" :=
  (rel_ex (fun x => .. (rel_ex (fun y => p)) ..))
  (at level 200, x binder, right associativity)
  : signature_scope.

