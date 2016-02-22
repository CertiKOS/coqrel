Require Export RelDefinitions.

(** ** Union of relations *)

Definition rel_union {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y \/ R2 x y.

Arguments rel_union {_ _} R1%rel R2%rel _ _.

Infix "∪" := rel_union (at level 50) : rel_scope.

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
  subrel (R1 ∪ R2)%rel R.
Proof.
  firstorder.
Qed.

Hint Extern 2 (subrel (_ ∪ _) _) =>
  eapply rel_union_lub : typeclass_instances.

(** ** Intersection of relations *)

Definition rel_inter {A B} (R1 R2: rel A B): rel A B :=
  fun x y => R1 x y /\ R2 x y.

Arguments rel_inter {_ _} R1%rel R2%rel _ _.

Infix "∩" := rel_inter (at level 40) : rel_scope.

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

Notation "⊥" := rel_bot : rel_scope.

Definition rel_top {A B}: rel A B :=
  fun x y => True.

Notation "⊤" := rel_top : rel_scope.

Hint Resolve (fun A B (x:A) (y:B) => I : rel_top x y).

(** ** Relation equivalence *)

Definition eqrel {A B}: rel (rel A B) (rel A B) :=
  (subrel ∩ flip subrel).

Arguments eqrel {_ _} RA%rel RB%rel.

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

(** ** Pulling a relation along functions *)

Definition rel_pull {A B A' B'} f g (R: rel A' B'): rel A B :=
  fun x y => R (f x) (g y).

Notation "R @@ f" := (rel_pull f f R)
  (at level 30, right associativity) : rel_scope.

Notation "R @@ ( f , g )" := (rel_pull f g R)
  (at level 30, right associativity) : rel_scope.

Global Instance rel_pull_subrel {A B A' B'} (f: A -> A') (g: B -> B'):
  Proper (subrel ++> subrel) (rel_pull f g).
Proof.
  firstorder.
Qed.

(** In the restricted case where [f = g], [rel_pull] preserves many
  properties of the underlying relation. *)

Lemma rel_pull_refl {A B} (f: A -> B) (R: rel B B):
  Reflexive R ->
  Reflexive (R @@ f).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Reflexive (rel_pull _ _ _)) =>
  eapply rel_pull_refl : typeclass_instances.

Lemma rel_pull_sym {A B} (f: A -> B) R:
  Symmetric R ->
  Symmetric (R @@ f).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Symmetric (rel_pull _ _ _)) =>
  eapply rel_pull_sym : typeclass_instances.

Lemma rel_pull_trans {A B} (f: A -> B) R:
  Transitive R ->
  Transitive (R @@ f).
Proof.
  firstorder.
Qed.

Hint Extern 1 (Transitive (rel_pull _ _ _)) =>
  eapply rel_pull_trans : typeclass_instances.

(** We can also reuse instances of [RIntro] and [RElim] for the
  underlying relation to provide corresponding instances for the
  pulled relation. *)

Lemma rel_pull_rintro {A B A' B'} (f: A -> A') (g: B -> B') P R x y:
  RIntro P R (f x) (g y) ->
  RIntro P (R @@ (f, g)) x y.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RIntro _ (_ @@ (_, _)) _ _) =>
  eapply rel_pull_rintro : typeclass_instances.

Lemma rel_pull_relim {A B A' B'} (f: A -> A') (g: B -> B') R x y P Q:
  RElim R (f x) (g y) P Q ->
  RElim (R @@ (f, g)) x y P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (_ @@ (_, _)) _ _ _ _) =>
  eapply rel_pull_relim : typeclass_instances.

(** ** Relation currying *)

(* An interesting special case of [rel_pull] is [rel_curry], which
  takes a relation over [A * B -> C] and turns it into a relation
  over [A -> B -> C].

  [rel_curry] is particularly useful when two (curried) arguments
  to a given function have to be related in a dependent way. For
  example in Compcert, memory injections relate memory blocks and
  offsets jointly, but many operations have those as two separate
  arguments. To state the relational property of such operations, we
  can uncurry a joint relation on (block, offset) pairs.

  [rel_curry] can be obtained by pulling back the original relation
  along [uncurry]: *)

Definition curry {A B C} (f: A * B -> C): A -> B -> C :=
  fun a b => f (a, b).

Definition uncurry {A B C} (f: A -> B -> C): A * B -> C :=
  fun ab => f (fst ab) (snd ab).

Notation rel_curry :=
  (fun R => R @@ (uncurry, uncurry)).

Notation rel_uncurry :=
  (fun R => R @@ (curry, curry)).

(** ** Checking predicates on the left and right elements *)

Definition lsat {A B} (P: A -> Prop): rel A B :=
  fun x y => P x.

Definition rsat {A B} (P: B -> Prop): rel A B :=
  fun x y => P y.

(** ** Relation versions of [ex] and [all] *)

(** Ideally we would overload the [forall] and [exists] notation to
  use the relation version under the [rel] scope. But as long as
  we keep [rel_scope] open globally, we can't really do that
  without breaking everything. So we use our own keyword [rexists] and
  [rforall] instead. *)

Definition rel_all {A B C} (R: C -> rel A B): rel A B :=
  fun x y => forall c, R c x y.

Notation "'rforall' x .. y , p" :=
  (rel_all (fun x => .. (rel_all (fun y => p)) .. ))
  (at level 200, x binder, right associativity)
  : rel_scope.

Lemma rel_all_rintro {A B C} (R: C -> rel A B) m n:
  RIntro (forall c : C, R c m n) (rel_all R) m n.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (rel_all _) _ _) =>
  eapply rel_all_rintro : typeclass_instances.

Lemma rel_all_relim {A B C} (R: C -> rel A B) x y P Q:
  (exists c, RElim (R c) x y P Q) ->
  RElim (rel_all R) x y P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (rel_all _) _ _ _ _) =>
  eapply rel_all_relim; eexists : typeclass_instances.

Definition rel_ex {A B C} (R: C -> rel A B): rel A B :=
  fun x y => exists c, R c x y.

Notation "'rexists' x .. y , p" :=
  (rel_ex (fun x => .. (rel_ex (fun y => p)) ..))
  (at level 200, x binder, right associativity)
  : rel_scope.

Lemma rel_ex_rintro {A B C} (R: C -> rel A B) m n:
  RIntro (exists c : C, R c m n) (rel_ex R) m n.
Proof.
  firstorder.
Qed.

Hint Extern 0 (RIntro _ (rel_ex _) _ _) =>
  eapply rel_ex_rintro : typeclass_instances.

Lemma rel_ex_relim {A B C} (R: C -> rel A B) x y P Q:
  (forall c, RElim (R c) x y P Q) ->
  RElim (rel_ex R) x y P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (rel_ex _) _ _ _ _) =>
  eapply rel_ex_relim : typeclass_instances.
