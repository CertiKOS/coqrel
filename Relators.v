Require Export RelDefinitions.
Require Import Coq.Lists.List.


(** * Relators *)

(** With this infrastructure in place, we can define actual relators
  that cover the commonly used type constructors. There are two broad
  categories: those related to function types, and those derived from
  inductive types. *)

(** As a convention, we name relators and the associated monotonicity
  theorems by appending the suffix [_rel] to the name of original type
  and those of its constructors. Likewise, we use the suffix [_subrel]
  for monotonicity theorems that characterize the variance of
  corresponding relators with respect to [subrel], and the suffix
  [_relim] for an associated instance of [RElim]. *)

(** ** Relators for function types *)

(** *** Pointwise extension of a relation *)

(** One useful special case is the pointwise extension of a relation
  on the domain to the function type. This is equivalent to [eq ==> R],
  however with the formulation below we don't have consider two equal
  elements of the domain. *)

Definition arrow_pointwise_rel A {B1 B2}:
  rel B1 B2 -> rel (A -> B1) (A -> B2) :=
    fun RB f g => forall a, RB (f a) (g a).

Arguments arrow_pointwise_rel _ {_ _} RB%rel _ _.

Notation "- ==> R" := (arrow_pointwise_rel _ R)
  (at level 55, right associativity) : rel_scope.

Global Instance arrow_pointwise_subrel {A B1 B2}:
  Proper (subrel ++> subrel) (@arrow_pointwise_rel A B1 B2).
Proof.
  firstorder.
Qed.

Lemma arrow_pointwise_relim {A B1 B2} (R: rel B1 B2) f g (a: A) P Q:
  RElim R (f a) (g a) P Q ->
  RElim (- ==> R) f g P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (- ==> _) _ _ _ _) =>
  eapply arrow_pointwise_relim : typeclass_instances.

Global Instance arrow_pointwise_eq_subrel {A B1 B2} (RB1 RB2: rel B1 B2):
  subrel RB1 RB2 ->
  subrel (- ==> RB1) (@eq A ==> RB2).
Proof.
  intros HRB f g Hfg x y Hxy.
  subst.
  apply HRB.
  apply Hfg.
Qed.

(** *** Dependent pointwise extension *)

(** Like we did for non-dependent functions, we can provide a simpler
  definition for the special case where [E] is [eq]. *)

Definition forall_pointwise_rel {V: Type} {FV1 FV2: V -> Type}:
    (forall v, rel (FV1 v) (FV2 v)) ->
    rel (forall v, FV1 v) (forall v, FV2 v) :=
  fun FE f g =>
    forall v, FE v (f v) (g v).

Arguments forall_pointwise_rel {_ _ _} FE%rel _ _.

Notation "∀ - , FE" := (forall_pointwise_rel (fun _ => FE))
  (at level 200).

Notation "∀ - : 'rel' , FE" := (forall_pointwise_rel (fun _ => FE))
  (at level 200).

Notation "∀ - : 'rel' v , FE" := (forall_pointwise_rel (fun v => FE))
  (at level 200, a at level 0).

Lemma forall_pointwise_relim {V FV1 FV2} R f g v P Q:
  RElim (R v) (f v) (g v) P Q ->
  RElim (@forall_pointwise_rel V FV1 FV2 R) f g P Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (forall_pointwise_rel _) _ _ _ _) =>
  eapply forall_pointwise_relim : typeclass_instances.

(** *** Dependent products (restricted version) *)

(** This is a restricted version of [forall_rel] with [E] in [Prop],
  when the codomain relation only depends on the arguments. *)

Definition forallp_rel {V1 V2} (E: rel V1 V2) {FV1: V1->Type} {FV2: V2->Type}:
    (forall v1 v2, rel (FV1 v1) (FV2 v2)) ->
    rel (forall v1, FV1 v1) (forall v2, FV2 v2) :=
  fun FE f g =>
    forall v1 v2, E v1 v2 -> FE v1 v2 (f v1) (g v2).

Arguments forallp_rel {_ _} _ {_ _} FE%rel _ _.

Notation "∀ ( v1 , v2 ) : E , R" := (forallp_rel E (fun v1 v2 => R))
  (at level 200, E at level 7, v1 ident, v2 ident, right associativity)
  : rel_scope.

(** Since [e : E v1 v2] cannot be unified in [Q], the elimination rule
  adds an [E v1 v2] premise to [P] instead. *)

Lemma forallp_relim {V1 V2 E FV1 FV2} R f g v1 v2 P Q:
  RElim (R v1 v2) (f v1) (g v2) P Q ->
  RElim (@forallp_rel V1 V2 E FV1 FV2 R) f g (E v1 v2 /\ P) Q.
Proof.
  firstorder.
Qed.

Hint Extern 1 (RElim (forallp_rel _ _) _ _ _ _) =>
  eapply forallp_relim : typeclass_instances.

(** *** Sets ([A -> Prop]) *)

(** Sets of type [A -> Prop] can be related using the regular arrow
  relator, as in [R ++> impl]. This states that for any two elements
  related by [R], if the first is in the first set, then the second
  must be in the second set.

  However, very often we need the following relator instead, which
  states that for any element of the first set, there exists an
  element of the second set which is related to it. This is useful for
  example when defining simulation diagrams. *)

Definition set_rel {A B} (R: rel A B): rel (A -> Prop) (B -> Prop) :=
  fun sA sB => forall a, sA a -> exists b, sB b /\ R a b.

Global Instance set_subrel A B:
  Proper (subrel ++> subrel) (@set_rel A B).
Proof.
  intros R1 R2 HR sA sB Hs.
  intros x Hx.
  destruct (Hs x) as (y & Hy & Hxy); eauto.
Qed.

(** ** Inductive types *)

(** For inductive types, there is a systematic way of converting their
  definition into that of the corresponding relator. Where the
  original inductive definition quantifies over types, the
  corresponding relator will quantify over pairs of types and
  relations between them. Then, the constructors of the relator will
  essentially be [Proper] instances for the original constructors.
  In other words, the resulting relation will be the smallest one such
  that the constructors are order-preserving. *)

(** *** Nullary type constructors *)

(** As a proof-of-concept, we start with the most elementary types
  [Empty_set] and [unit], which can be considered as nullary type
  constructors related to [sum] and [prod] below. *)

Inductive Empty_set_rel: rel Empty_set Empty_set := .

Inductive unit_rel: rel unit unit :=
  tt_rel: Proper unit_rel tt.

Global Existing Instance tt_rel.

(** *** Sum types *)

(** The definition of [sum_rel] could look something like this:
<<
  Inductive sum_rel:
    forall {A1 A2 B1 B2}, rel A1 A2 -> rel B1 B2 -> rel (A1+B1) (A2+B2):=
    | inl_rel: Proper (∀ RA : rel, ∀ RB : rel, RA ++> sum_rel RA RB) (@inl)
    | inr_rel: Proper (∀ RA : rel, ∀ RB : rel, RB ++> sum_rel RA RB) (@inr).
>>
  However, to minimize the need for [inversion]s we want to keep as
  many arguments as possible as parameters of the inductive type. *)

Inductive sum_rel {A1 A2} RA {B1 B2} RB: rel (A1 + B1)%type (A2 + B2)%type :=
  | inl_rel_def: (RA ++> sum_rel RA RB) (@inl A1 B1) (@inl A2 B2)
  | inr_rel_def: (RB ++> sum_rel RA RB) (@inr A1 B1) (@inr A2 B2).

Infix "+" := sum_rel : rel_scope.

(** Since it is not possible to retype the constructors after the
  fact, we use the [_def] suffix when defining them, then redeclare
  a corresponding, full-blown [Proper] instance. *)

Local Instance inl_rel:
  Proper (∀ RA, ∀ RB, RA ++> RA + RB) (@inl).
Proof.
  exact @inl_rel_def.
Qed.

Local Instance inr_rel:
  Proper (∀ RA, ∀ RB, RB ++> RA + RB) (@inr).
Proof.
  exact @inr_rel_def.
Qed.

Global Instance sum_subrel:
  Proper (∀ -, ∀ -, subrel ++> ∀ -, ∀ -, subrel ++> subrel) (@sum_rel).
Proof.
  intros A1 A2 RA1 RA2 HRA B1 B2 RB1 RB2 HRB.
  intros x1 x2 Hx.
  destruct Hx; constructor; eauto.
Qed.

Global Instance sum_rel_refl {A B} (R1: rel A A) (R2: rel B B):
  Reflexive R1 -> Reflexive R2 -> Reflexive (R1 + R2).
Proof.
  intros H1 H2 x.
  destruct x; constructor; reflexivity.
Qed.

Global Instance sum_rel_trans {A B} (R1: rel A A) (R2: rel B B):
  Transitive R1 -> Transitive R2 -> Transitive (R1 + R2).
Proof.
  intros H1 H2 x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; constructor; etransitivity; eassumption.
Qed.

Global Instance sum_rel_sym {A B} (R1: rel A A) (R2: rel B B):
  Symmetric R1 -> Symmetric R2 -> Symmetric (R1 + R2).
Proof.
  intros H1 H2 x y Hxy.
  destruct Hxy; constructor; symmetry; eassumption.
Qed.

Arguments PreOrder A%type R%rel.

Global Instance sum_rel_preorder {A B} (R1: rel A A) (R2: rel B B):
  PreOrder R1 -> PreOrder R2 -> PreOrder (R1 + R2).
Proof.
  split; typeclasses eauto.
Qed.

Hint Extern 0 (Proper _ (@inl)) => exact inl_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@inr)) => exact inr_rel : typeclass_instances.

(** *** Pairs *)

Definition prod_rel {A1 A2} RA {B1 B2} RB: rel (A1 * B1)%type (A2 * B2)%type :=
  fun x1 x2 => RA (fst x1) (fst x2) /\ RB (snd x1) (snd x2).

Infix "*" := prod_rel : rel_scope.

Local Instance pair_rel:
  Proper (∀ RA, ∀ RB, RA ++> RB ++> RA * RB) (@pair).
Proof.
  intros A1 A2 RA B1 B2 RB a1 a2 Ha b1 b2 Hb.
  red.
  eauto.
Qed.

Local Instance fst_rel:
  Proper (∀ RA, ∀ RB, RA * RB ==> RA) (@fst).
Proof.
  intros A1 A2 RA B1 B2 RB.
  intros x1 x2 [Ha Hb].
  assumption.
Qed.

Local Instance snd_rel:
  Proper (∀ RA, ∀ RB, RA * RB ==> RB) (@snd).
Proof.
  intros A1 A2 RA B1 B2 RB.
  intros x1 x2 [Ha Hb].
  assumption.
Qed.

Global Instance prod_subrel:
  Proper (∀ -, ∀ -, subrel ++> ∀ -, ∀ -, subrel ++> subrel) (@prod_rel).
Proof.
  firstorder.
Qed.

Global Instance prod_rel_refl {A B} (R1: rel A A) (R2: rel B B):
  Reflexive R1 -> Reflexive R2 -> Reflexive (R1 * R2).
Proof.
  intros H1 H2 x.
  destruct x; constructor; reflexivity.
Qed.

Global Instance prod_rel_trans {A B} (R1: rel A A) (R2: rel B B):
  Transitive R1 -> Transitive R2 -> Transitive (R1 * R2).
Proof.
  intros H1 H2 x y z Hxy Hyz.
  destruct Hxy; inversion Hyz; constructor; etransitivity; eassumption.
Qed.

Global Instance prod_rel_sym {A B} (R1: rel A A) (R2: rel B B):
  Symmetric R1 -> Symmetric R2 -> Symmetric (R1 * R2).
Proof.
  intros H1 H2 x y Hxy.
  destruct Hxy; constructor; symmetry; eassumption.
Qed.

Global Instance prod_rel_preorder {A B} (R1: rel A A) (R2: rel B B):
  PreOrder R1 -> PreOrder R2 -> PreOrder (R1 * R2).
Proof.
  split; typeclasses eauto.
Qed.

Hint Extern 0 (Proper _ (@pair)) => exact pair_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@fst)) => exact fst_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@snd)) => exact snd_rel : typeclass_instances.

(** *** Option types *)

Inductive option_rel {A1 A2} (RA: rel A1 A2): rel (option A1) (option A2) :=
  | Some_rel_def: (RA ++> option_rel RA) (@Some A1) (@Some A2)
  | None_rel_def: option_rel RA (@None A1) (@None A2).

Local Instance Some_rel:
  Proper (∀ R : rel A1 A2, R ++> option_rel R) (@Some).
Proof.
  exact @Some_rel_def.
Qed.

Local Instance None_rel:
  Proper (∀ R, option_rel R) (@None).
Proof.
  exact @None_rel_def.
Qed.

Global Instance option_subrel:
  Proper (∀ -, ∀ -, subrel ++> subrel) (@option_rel).
Proof.
  intros A1 A2 RA1 RA2 HRA.
  intros x1 x2 Hx.
  destruct Hx; constructor; eauto.
Qed.

Hint Extern 0 (Proper _ (@Some)) => exact Some_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@None)) => exact None_rel : typeclass_instances.

Lemma option_rel_some_inv A B (R: rel A B) (x: option A) (y: option B) (a: A):
  option_rel R x y ->
  x = Some a ->
  exists b,
    y = Some b /\
    R a b.
Proof.
  destruct 1; inversion 1; subst; eauto.
Qed.

(** *** Lists *)

Inductive list_rel {A1 A2} (R: rel A1 A2): rel (list A1) (list A2) :=
  | nil_rel_def: (list_rel R) (@nil A1) (@nil A2)
  | cons_rel_def: (R ++> list_rel R ++> list_rel R) (@cons A1) (@cons A2).

Local Instance nil_rel:
  Proper (∀ R, list_rel R) (@nil).
Proof.
  exact @nil_rel_def.
Qed.

Local Instance cons_rel:
  Proper (∀ R, R ++> list_rel R ++> list_rel R) (@cons).
Proof.
  exact @cons_rel_def.
Qed.

Hint Extern 0 (Proper _ (@nil)) => exact nil_rel : typeclass_instances.
Hint Extern 0 (Proper _ (@cons)) => exact cons_rel : typeclass_instances.

Global Instance list_subrel {A1 A2}:
  Proper (subrel ++> subrel) (@list_rel A1 A2).
Proof.
  intros R S HRS x y.
  red in HRS.
  induction 1; constructor; eauto.
Qed.

Global Instance app_rel:
  Proper (∀ R : rel, list_rel R ++> list_rel R ++> list_rel R) (@app).
Proof.
  intros A1 A2 R l1 l2 Hl.
  induction Hl as [ | x1 x2 Hx l1 l2 Hl IHl]; simpl.
  - firstorder.
  - constructor; eauto.
Qed.

Global Instance map_rel:
  Proper (∀ RA, ∀ RB, (RA ++> RB) ++> list_rel RA ++> list_rel RB) map.
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg l1 l2 Hl.
  induction Hl; constructor; eauto.
Qed.

Global Instance fold_right_rel:
  Proper
    (∀ RA, ∀ RB, (RB ++> RA ++> RA) ++> RA ++> list_rel RB ++> RA)
    fold_right.
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg a1 a2 Ha l1 l2 Hl.
  induction Hl; simpl; eauto.
  eapply Hfg; eauto.
Qed.

Global Instance fold_left_rel:
  Proper
    (∀ RA, ∀ RB, (RA ++> RB ++> RA) ++> list_rel RB ++> RA ++> RA)
    fold_left.
Proof.
  intros A1 A2 RA B1 B2 RB f g Hfg l1 l2 Hl.
  induction Hl; simpl.
  - firstorder.
  - intros a1 a2 Ha.
    eapply IHHl.
    eapply Hfg; assumption.
Qed.

(** ** Monotonicity of logical connectives *)

Global Instance all_monotonic A:
  Proper ((- ==> impl) ++> impl) (@all A).
Proof.
  intros P Q HPQ H x.
  apply HPQ.
  apply H.
Qed.

Global Instance ex_monotonic A:
  Proper ((- ==> impl) ++> impl) (@ex A).
Proof.
  intros P Q HPQ [x Hx].
  exists x.
  apply HPQ.
  assumption.
Qed.

Global Instance and_monotonic:
  Proper (impl ++> impl ++> impl) and.
Proof.
  intros P1 P2 HP Q1 Q2 HQ [HP1 HQ1].
  eauto.
Qed.

Global Instance or_monotonic:
  Proper (impl ++> impl ++> impl) or.
Proof.
  intros P1 P2 HP Q1 Q2 HQ [HP1|HQ1];
  eauto.
Qed.
