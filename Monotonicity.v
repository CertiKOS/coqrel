Require Export RelDefinitions.
Require Export RelOperators.
Require Export Relators.
Require Import MorphismsCompat.
Require Import Delay.

(** ** The [monotonicity] tactic *)

(** The purpose of the [monotonicity] tactic is to automatically
  select and apply a theorem of the form [Proper ?R ?m] in order to
  make progress when the goal is an applied relation. Compared with
  setoid rewriting, [monotonicity] is less powerful, but more direct
  and simple. This means it is easier to debug, and it can seamlessly
  handle dependent types and heterogenous relations. *)

(** *** Using [Proper] instances *)

(** Although [Related] won't help with setoid rewriting, it is used as
  as the resolution mechanism for the monotonicity tactic. To make
  sure we can use [Proper] instances as well we introduce the
  following instance. At the moment, [monotonicity] does not use any
  of the preprocessing phases for its [ProperQuery]. *)

Global Instance query_related {A} (R: rel A A) (m: A):
  ProperQuery nil R m ->
  Related R m m.
Proof.
  firstorder.
Qed.

(** *** Truncating applications *)

(** The search is guided by the left-hand side term, so that if the
  goal has the form [?R (?f ?x1 ?x2 ?x3 ... ?xn) ?y], we will seek a
  [Proper] instance for some prefix [f x1 ... xk]. This allows both
  [R] and [y] to be existential variables, which is required in
  particular by the [transport] tactic.

  However, since peeling off the [xi]s one by one and conducting a
  full-blown search at every step is very time-consuming, we narrow
  down the search to only one option whenever a [Params] instance has
  been declared. The [get_params] tactic queries the declared number
  of parameters for a given head term [h] and passes it to the
  continuation [sk]. The [remove_params] tactic drops applied
  arguments from its argument [m] so that the result expects the
  declared number of parameters. We are careful to skip an appropriate
  number of parameters when the type of term indicates that it is
  already a partial application. *)

Ltac get_params h sk fk :=
  let nv := fresh "nparams" in evar (nv : nat);
  let n := eval red in nv in clear nv;
  let H := fresh in
  first
    [ assert (H: Params h n) by typeclasses eauto;
      clear H;
      let n := eval compute in n in first [ sk n | fail 2 ]
    | unify n O; (* make sure [n] is instantciated *)
      (* idtac "Warning: no Params instance for" h; *)
      fk ].

Ltac remove_params m sk fk :=
  let rec remove m n :=
    lazymatch n with
      | S ?n' =>
        lazymatch m with
          | ?m' _ => remove m' n'
        end
      | O => sk m
    end in
  let rec remove_from_partial m t n :=
    lazymatch t with
      | forall x, ?t' =>
        lazymatch n with
          | S ?n' => remove_from_partial m t' n'
        end
      | _ =>
        remove m n
    end in
  let rec head m :=
    lazymatch m with
      | ?m' _ => head m'
      | _ => constr:m
    end in
  let h := head m in
  let t := type of m in
  get_params h ltac:(remove_from_partial m t) fk.

(** *** Selecting a monotonicity property *)

(** We want [monotonicity] to first select a property, then apply it
  to the goal with the [eapply] tactic. This way, much of the work is
  outsourced to [eapply] and Coq's unification algorithms in terms of
  partial application, instantiating existential variables, generating
  multiple subgoals, etc.

  Unfortunately, by the time we've resolved a property to apply using
  [assert by typeclasses eauto], we've committed to one specific
  instance of [Related], which may or may not be the right one if
  several of them are available. To fix this, we need to somehow
  embed the [eapply] into typeclasses resolution so that we can
  leverage its backtracking process. This is particulaly important
  with parametric instances of [Related] which themselves may rely on
  further resolution, which themselves may have multiple instances. As
  an example, in [liblayers] a common occurence is that the context
  offers two different memory models which have to be chosen
  appropriately.

  This means we need to somehow include the goal to which we want to
  apply the property as part of our typeclass query, and somehow reify
  the effect of using [eapply] as part of resolution process. This is
  done using the [EApply] class from the [Delay] library.

  With effect of [eapply] encoded into the typeclass
  infrastructure, the resolution process is straightforward: find an
  instance of [Related], attempt to apply it to the goal [Q], and if
  that succeeds, use the result to build an instance of the following
  class. *)

Class Monotonicity {A B} (R: rel A B) (x: A) (y: B) (Qs Q: Prop) :=
  monotonicity: Qs -> Q.

Global Instance related_monotonicity {A B} (R: rel A B) x y Qs Q:
  Related R x y ->
  EApply (R x y) Qs Q ->
  Monotonicity R x y Qs Q.
Proof.
  firstorder.
Qed.


(** *** Main tactic *)

(* Also, sometimes we don't have a [Proper] instance, but we do have
  an applicable hypothesis of the form [(RA ++> RB) f g] or similar in
  the context, for instance an induction hypothesis, or one of the
  premises when proving the monotonicity properties of high-order
  functions. The [monotonicity] tactic attempts to apply such
  hypotheses as well. *)

Ltac monotonicity :=
  let rec iter_prefixes apply_tac m :=
    idtac; (* needed, for some obscure reason *)
    match m with
      | _ => apply_tac m
      | ?f _ => iter_prefixes apply_tac f
    end in
  let apply_hyp_left m1 :=
    match goal with
      | H: _ m1 _ |- _ => eapply H
    end in
  let apply_hyp_right m2 :=
    match goal with
      | H: _ _ m2 |- _ => eapply H
    end in
  let apply_rel R m1 m2 :=
    let Qsv := fresh "Qs" in evar (Qsv: Prop);
    let Qs := eval red in Qsv in clear Qsv;
    let H := fresh in
    lazymatch goal with
      | |- ?Q =>
        assert (H: Monotonicity R m1 m2 Qs Q) by typeclasses eauto
    end;
    (*idtac "Query successful.";*)
    eapply H;
    clear H;
    Delay.split_conjunction in
  let apply_rel_left m1 :=
    let A := type of m1 in
    let Bv := fresh "B" in evar (Bv: Type);
    let B := eval red in Bv in clear Bv;
    let Rv := fresh "R" in evar (Rv: rel A B);
    let Re := eval red in Rv in clear Rv;
    let m2v := fresh "m2" in evar (m2v: B);
    let m2 := eval red in m2v in clear m2v;
    apply_rel Re m1 m2 in
  let apply_rel_right m2 :=
    let Av := fresh "A" in evar (Av: Type);
    let A := eval red in Av in clear Av;
    let B := type of m2 in
    let Rv := fresh "R" in evar (Rv: rel A B);
    let Re := eval red in Rv in clear Rv;
    let m1v := fresh "m1" in evar (m1v: A);
    let m1 := eval red in m1v in clear m1v;
    apply_rel Re m1 m2 in
  let apply_both_left m1 :=
    first [ apply_hyp_left m1 | apply_rel_left m1 ] in
  let apply_both_right m2 :=
    first [ apply_hyp_right m2 | apply_rel_right m2 ] in
  lazymatch goal with
    | |- ?R ?m1 ?m2 =>
      first
        [ not_evar m1;
          remove_params m1
            ltac:(fun m => first [ iter_prefixes apply_hyp_left m1 | apply_rel_left m ])
            ltac:(iter_prefixes apply_both_left m1)
        | not_evar m2;
          remove_params m2
            ltac:(fun m => first [ iter_prefixes apply_hyp_right m2 | apply_rel_right m ])
            ltac:(iter_prefixes apply_both_right m2) ]
    | |- ?P -> ?Q =>
      change (impl P Q); monotonicity
  end.

(** Our version of [Morphisms.f_equiv]. *)

Ltac f_equiv :=
  repeat monotonicity.

(** Our version of [Morphisms.solve_proper]. Note that we are somewhat
  parcimonious with introductions because we don't want to cause undue
  unfoldings. For instance, if we define the relation [R1] from [R2]
  as [R1 x y := forall i, R2 (get i x) (get i y)], we may create a
  situation where applying the monotonicity theorem for [get] on a
  goal of the form [R2 (get i x) (get i y)] produces a subgoal of the
  form [R1 x y], but then an introduction would get us back to where
  we started. So we limit them to well-defined cases.

  Most cases are straightforward. In the [match]/[if] case, we need to
  first show that the terms being destructed are related. Then if the
  relation has been defined in a typical way (akin to [sum_rel] or
  [list_rel] below), destructing that hypothesis will cause the goal
  to reduce and we can go on with the process. Note that for [prod],
  and for record types, we usually prefer to define associated
  relations as conjunctions of statements that the projections are
  related, in which case the terms would need to be destructed on
  their own as well. At the moment we don't do that. *)

Ltac solve_monotonic_tac t :=
  let conclusion_progress t :=
    lazymatch goal with
      | |- ?G =>
        t;
        lazymatch goal with
          | |- G => fail "No progress in conclusion"
          | |- _ => idtac
        end
    end in
  let destruct_both m1 m2 :=
    let t1 := type of m1 in
    let t2 := type of m2 in
    let Rv := fresh "R" in evar (Rv: rel t1 t2);
    let Rm := eval red in Rv in clear Rv;
    let H := fresh in
    assert (H: Rm m1 m2) by solve_monotonic_tac t;
    conclusion_progress ltac:(destruct H) in
  repeat
    match goal with
      | |- Proper _ _ => red
      | |- Related _ _ _ => red
      | |- flip _ _ _ => red
      | |- _ => progress t
      | |- _ _ _ => monotonicity
      | |- _ -> _ => monotonicity
      | |- (_ --> _) _ _ => let H := fresh in intros ? ? H; red in H
      | |- (_ ++> _) _ _ => intros ? ? ?
      | |- (- ==> _) _ _ => intro
      | |- (∀ _, _) _ _ => intros ? ? ?
      | |- (∀ -, _) _ _ => intro
      | |- (rforall _, _) _ _ => intro
      | |- _ ?x ?x => reflexivity
      | |- forall _, _ => intro
      | |- _ (match ?m with _ => _ end) (match ?m with _ => _ end) =>
        destruct m
      | |- _ (if ?m then _ else _) (if ?m then _ else _) =>
        destruct m
      | |- _ (match ?m1 with _ => _ end) (match ?m2 with _ => _ end) =>
        destruct_both m1 m2
      | |- _ (if ?m1 then _ else _) (if ?m2 then _ else _) =>
        destruct_both m1 m2
    end.

Tactic Notation "solve_monotonic" :=
  solve_monotonic_tac ltac:(eassumption || congruence || (now econstructor)).

Tactic Notation "solve_monotonic" tactic(t) :=
  solve_monotonic_tac ltac:(eassumption || congruence || (now econstructor)|| t).

(** ** Exploiting [foo_subrel] instances *)

(** Although we declared [Proper] instances for the relation
  constructors we defined, so far the usefulness of these instances
  has been limited. But now we can use them in conjunction with our
  [monotonicity] tactic to break up [subrel] goals along the structure
  of the relations being considered. *)

Hint Extern 5 (subrel _ _) =>
  monotonicity; unfold flip : typeclass_instances.

(** Furthermore, the following instance of [subrel] enables the use of
  [foo_subrel] instances for rewriting along within applied relations.
  So that for instance, a hypothesis [H: subrel R1 R2] can be used for
  rewriting in a goal of the form [(R1 * R1' ++> R) x y]. *)

Instance subrel_pointwise_subrel {A B}:
  subrel (@subrel A B) (eq ==> eq ==> impl).
Proof.
  intros R1 R2 HR x1 x2 Hx y1 y2 Hy H; subst.
  eauto.
Qed.
