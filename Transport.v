Require Export Monotonicity.

(** ** The [transport] tactic *)

(** Often, we know that a number of terms are related, and need to
  transport hypotheses built out the the left-hand sides into ones
  with similar shapes, but built out of the right-hand sides. For
  instance, in cirumstances where [solve_monotonic] can establish
  [option_le R x y], we will want to turn a hypothesis of the form
  [x = Some a] into one of the form [y = Some b], and remember that
  [R a b]. This is the role of the [transport] tactic. *)

(** *** Transportable hypotheses *)

(* To make the tactic extensible, we use the following typeclass to
  declare patterns of relations and hypothesis shapes that can be
  handled in this way. *)

Class Transport {A B} (R: rel A B) (a: A) (b: B) (PA: Prop) (PB: Prop) :=
  transport: R a b -> PA -> PB.

(** The stereotypical example is [option_rel], which we can use to
  transport hypotheses as per the following instances. *)

Global Instance option_rel_transport_eq_some {A B} (R: rel A B) x y a:
  Transport (option_rel R) x y (x = Some a) (exists b, y = Some b /\ R a b).
Proof.
  intros Hxy Hx.
  subst; inversion Hxy; eauto.
Qed.

Global Instance option_rel_transport_eq_none {A B} (R: rel A B) x y:
  Transport (option_rel R) x y (x = None) (y = None).
Proof.
  intros Hxy Hx.
  subst; inversion Hxy; eauto.
Qed.

(** A similar approach can be used to transport hypotheses which assert
  a element of a product type is equal to a specific pair. *)

Global Instance prod_rel_transport_eq_pair {A1 B1 A2 B2} (R1: rel A1 B1) (R2: rel A2 B2) x y a1 a2:
  Transport (prod_rel R1 R2) x y (x = (a1, a2)) (exists b1 b2, y = (b1, b2) /\ R1 a1 b1 /\ R2 a2 b2).
Proof.
  intros [Hxy1 Hxy2] Hx.
  destruct y.
  subst.
  simpl in *.
  eauto.
Qed.

(** For [set_rel] the situation is slightly more involved, for two
  reasons. First, a regular [eapply set_rel_transport] fails to unify
  the parameter [B] of [Transport] against the [_ -> Prop] provied by
  the instance below. This can be worked around by pre-unifying that
  specific parameter. Second, because [set_rel_transport] is
  potentially applicable to virtually any hypothesis (since there is
  no strongly distinguishing syntactic format in our target
  hypotheses), it makes [transport_hyps] very slow.

  To address this, we explicitely register hints based on the
  [set_rel_transport] tactic, which looks for "keywords" before doing
  anything, then applies the lemma with the required unification
  preparation. For example, [set_rel_transport] is used in the
  following way in the [SimClight] library:
  <<<
  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_rel_transport @assign_loc : typeclass_instances.
  >>>
  Note that it's necessary to use [@] because [assign_loc] is
  parametrized by typeclasses, and we want to avoid undue
  specialization at hint registration time. *)

Lemma set_rel_transport {A B} (R: rel A B) sA sB a:
  Transport (set_rel R) sA sB (sA a) (exists b, sB b /\ R a b).
Proof.
  intros HsAB Ha.
  edestruct HsAB; eauto.
Qed.

Ltac set_rel_transport keyword :=
  lazymatch goal with
    | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB =>
      lazymatch PA with
        | appcontext [keyword] =>
          let Xv := fresh "X" in evar (Xv: Type);
          let X := eval red in Xv in clear Xv;
          unify B (X -> Prop);
          eapply set_rel_transport
      end
  end.
      
(** We defined a few more relation patterns based on [set_rel] and
  [rel_curry], with a similar strategy. *)

Lemma rel_curry_set_rel_transport {A1 A2 B1 B2} R sA sB (a1: A1) (a2: A2):
  Transport (rel_curry (set_rel R)) sA sB
    (sA a1 a2)
    (exists (b1: B1) (b2: B2), sB b1 b2 /\ R (a1, a2) (b1, b2)).
Proof.
  intros HsAB Ha.
  destruct (HsAB (a1, a2)) as ([b1 b2] & Hb & Hab); eauto.
Qed.

Ltac rel_curry_set_rel_transport keyword :=
  lazymatch goal with
    | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB =>
      lazymatch PA with
        | appcontext [keyword] =>
          let Xv := fresh "X" in evar (Xv: Type);
          let X := eval red in Xv in clear Xv;
          let Yv := fresh "Y" in evar (Yv: Type);
          let Y := eval red in Yv in clear Yv;
          unify B (X -> Y -> Prop);
          eapply rel_curry_set_rel_transport
      end
  end.

Lemma rel_curry2_set_rel_transport {A1 A2 A3 B1 B2 B3} R sA sB (a1: A1) (a2: A2) (a3: A3):
  Transport (rel_curry (rel_curry (set_rel R))) sA sB
    (sA a1 a2 a3)
    (exists (b1: B1) (b2: B2) (b3: B3), sB b1 b2 b3 /\ R (a1, a2, a3) (b1, b2, b3)).
Proof.
  intros HsAB Ha.
  destruct (HsAB (a1, a2, a3)) as ([[b1 b2] b3] & Hb & Hab); eauto.
Qed.

Ltac rel_curry2_set_rel_transport keyword :=
  lazymatch goal with
    | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB =>
      lazymatch PA with
        | appcontext [keyword] =>
          let Xv := fresh "X" in evar (Xv: Type);
          let X := eval red in Xv in clear Xv;
          let Yv := fresh "Y" in evar (Yv: Type);
          let Y := eval red in Yv in clear Yv;
          let Zv := fresh "Y" in evar (Yv: Type);
          let Z := eval red in Yv in clear Yv;
          unify B (X -> Y -> Z -> Prop);
          eapply rel_curry2_set_rel_transport
      end
  end.

(** The situation for [impl] is similar: since this transport instance
  can apply to pretty much anything, we need to register it on a
  case-by-case basis. Here is an example used in the CertiKOS proof
  for hypotheses of the form [writable_block ge b]:
  <<<
  Hint Extern 10 (Transport _ _ _ (writable_block _ _) _) =>
    eapply impl_transport : typeclass_instances.
  >>> *)

Lemma impl_transport P Q:
  Transport impl P Q P Q.
Proof.
  firstorder.
Qed.

(*** *** The actual tactic *)

(** Often, the target hypotheses declared using the [Transport] class
  have existential quantifiers, and need to be broken up to get to the
  actual relational hypotheses we're interested in. The [split_hyp]
  tactic does that. As a generally useful complement, the [split_hyps]
  tactic applies the same process to all hypotheses. *)

Ltac split_hyp H :=
  lazymatch type of H with
    | ex _ =>
      destruct H as [? H];
      split_hyp H
    | _ /\ _ =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      split_hyp H1;
      split_hyp H2
    | prod_rel ?Rx ?Ry (?x1, ?y1) (?x2, ?y2) =>
      change (Rx x1 x2 /\ Ry y1 y2) in H;
      split_hyp H
    | rel_incr ?acc ?R ?w ?x ?y =>
      let w' := fresh w "'" in
      let Hw' := fresh "H" w' in
      destruct H as (w' & Hw' & H);
      split_hyp H
    | _ =>
      idtac
  end.

Ltac split_hyps :=
  repeat
    lazymatch goal with
      | H: ex _ |- _ =>
        destruct H
      | H: _ /\ _ |- _ =>
        destruct H
      | H: prod_rel ?Rx ?Ry (?x1, ?y1) (?x2, ?y2) |- _ =>
        change (Rx x1 x2 /\ Ry y1 y2) in H
    end.
      
(** We're now ready to defined the [transport] tactic, which
  essentially looks up a [Transport] instance, applies it the the
  hypothesis to be transported, and discharges the generated
  relational subgoal using [solve_monotonic]. In this last step, the
  relation and right-hand side will usually contain existential
  variables, but the proof search can hopefully proceed by following
  the structure of the left-hand side.

  We need to avoid a delayed instance search, hence this mess. Also,
  note that it is important that we first let [solve_monotonic] unify
  all it can, then use the [split_hyp] tactic, which can now split
  things that use [prod_rel], which are common in contexts where
  [rel_curry] is involved.

  Another pitfall we want to avoid is illustrated by the [option_rel]
  case. When we have a hypothesis of the form [H: m = Some a], but no
  interesting way to relate [m] to something else, then the search for
  [(option_rel ?R) m ?n] can end up using [H] itself (because
  [option_rel eq] is reflexive, hence [subrel_eq] applies). To prevent
  such cases we need to make sure that the hypothesis being
  transported is not used to discharge the relational premise, and so
  we [clear H] prior to invoking [solve_monotonic]. *)

Ltac transport H :=
  let Av := fresh "A" in evar (Av: Type);
  let A := eval red in Av in clear Av;
  let Bv := fresh "B" in evar (Bv: Type);
  let B := eval red in Bv in clear Bv;
  let Rv := fresh "R" in evar (Rv: rel A B);
  let R := eval red in Rv in clear Rv;
  let av := fresh "a" in evar (av: A);
  let a := eval red in av in clear av;
  let bv := fresh "b" in evar (bv: B);
  let b := eval red in bv in clear bv;
  let PA := type of H in
  let PBv := fresh "PB" in evar (PBv: Prop);
  let PB := eval red in PBv in clear PBv;
  let HT := fresh in
  assert (HT: Transport R a b PA PB) by typeclasses eauto;
  eapply (transport (Transport := HT)) in H; clear HT;
  [ | solve [clear H; solve_monotonic]];
  try (unify a b; fail 1 "no progress");
  split_hyp H.

(** Again we provide a tactic which attempts to transport all
  hypotheses. Notice that earlier transportations may provide new
  hypotheses making later transportations possible. Hence it would be
  hard to provide a much more effective tactic, even though this one
  may retry failing transportations many times. *)

Ltac transport_hyps :=
  repeat
    match goal with
      | H: _ |- _ => transport H
    end.
